import TemplateDependencies

/-!
Finite source storage bounds retaining free resource names. These conservative
bounds commute with lexical opening and agree with runtime support analysis
on resource-closed code. Applications and control results remain unknown.
-/

namespace Ash.OneShot.TemplateSupport
open Instantiation ScopedExpressions ScopedExecution TemplateDependencies

abbrev Bound := Option (List ResourceName)
abbrev SupportEnv := Nat → Bound

def merge {α : Type} (left right : Option (List α)) : Option (List α) := do
  let first ← left
  let second ← right
  pure (first ++ second)

def mapBound (environment : Instantiation.Environment) (bound : Bound) : Bound :=
  bound.map (List.map (ResourceName.instantiate environment))

def lift (bound : Option (List Nat)) : Bound := bound.map (List.map ResourceName.activation)

def runtimeEnv (environment : ResultSummaries.Environment) : SupportEnv :=
  fun name => lift (environment name).support

def atom (environment : SupportEnv) : Dep → Bound
  | .resource name => some [name]
  | .variable name => environment name
  | .ticket _ => none

def captured (environment : SupportEnv) : List Dep → Bound
  | [] => some []
  | first :: rest => merge (atom environment first) (captured environment rest)

def infer (environment : SupportEnv) : Code → Bound
  | .unit | .boolean _ | .integer _ => some []
  | .variable name => environment name
  | .resourceRef name => some [name]
  | .pair left right => merge (infer environment left) (infer environment right)
  | .lambda parameter body => captured environment (dependencies (.lambda parameter body))
  | .bind parameter initializer body =>
      infer (fun name => if name = parameter then infer environment initializer else environment name) body
  | .branch _ yes no => merge (infer environment yes) (infer environment no)
  | .app _ _ | .perform _ _ _ | .handle _ _ _ | .resume _ _ | .discard _ | .resource _ _ _ | .cleanup _ _ => none

theorem map_merge (left right : Bound) :
    mapBound environment (merge left right) = merge (mapBound environment left) (mapBound environment right) := by
  cases left <;> cases right <;> simp [merge, mapBound]

theorem lift_merge (left right : Option (List Nat)) :
    lift (merge left right) = merge (lift left) (lift right) := by
  cases left <;> cases right <;> simp [merge, lift]

theorem map_lift (bound : Option (List Nat)) : mapBound environment (lift bound) = lift bound := by
  cases bound <;> simp [mapBound, lift, List.map_map, ResourceName.instantiate]

theorem atom_instantiate (dependency : Dep) :
    atom (fun name => mapBound resources (environment name)) (dependency.instantiate resources) =
      mapBound resources (atom environment dependency) := by
  cases dependency <;> rfl

theorem captured_instantiate (items : List Dep) :
    captured (fun name => mapBound resources (environment name)) (items.map (Dep.instantiate resources)) =
      mapBound resources (captured environment items) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, captured, atom_instantiate, ih, map_merge]

theorem infer_instantiate (code : Code) (environment : SupportEnv) (resources : Instantiation.Environment) :
    infer (fun name => mapBound resources (environment name)) (code.instantiate resources) =
      mapBound resources (infer environment code) := by
  cases code with
  | unit | boolean | integer | «variable» | resourceRef => rfl
  | app | perform | handle | resume | discard | resource | cleanup => rfl
  | pair left right =>
      simp only [Code.instantiate, infer, infer_instantiate left environment resources,
        infer_instantiate right environment resources, map_merge]
  | branch condition yes no =>
      simp only [Code.instantiate, infer, infer_instantiate yes environment resources,
        infer_instantiate no environment resources, map_merge]
  | lambda parameter body =>
      change captured _ (dependencies ((Code.lambda parameter body).instantiate resources)) = _
      rw [dependencies_instantiate, captured_instantiate]
      rfl
  | bind parameter initializer body =>
      simp only [Code.instantiate, infer]
      have same :
          (fun name => if name = parameter then infer (fun n => mapBound resources (environment n))
            (initializer.instantiate resources) else mapBound resources (environment name)) =
          (fun name => mapBound resources (if name = parameter then infer environment initializer else environment name)) := by
        funext name
        split
        · exact infer_instantiate initializer environment resources
        · rfl
      rw [same]
      exact infer_instantiate body _ resources
termination_by sizeOf code

theorem captured_runtime (items : List Dep)
    (closed : ∀ name, Dep.resource (.bound name) ∉ items) :
    captured (runtimeEnv environment) items =
      lift (ResultSummaries.captured environment (items.filterMap Dep.runtime)).support := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      have tail := ih (fun name member => closed name (List.mem_cons_of_mem _ member))
      cases first with
      | resource name => cases name with
          | bound name => exact False.elim (closed name List.mem_cons_self)
          | activation identity =>
              change merge (lift (some [identity])) (captured (runtimeEnv environment) rest) =
                lift (merge (some [identity]) (ResultSummaries.captured environment (rest.filterMap Dep.runtime)).support)
              rw [tail, lift_merge]
      | «variable» name =>
          change merge (lift (environment name).support) (captured (runtimeEnv environment) rest) =
            lift (merge (environment name).support (ResultSummaries.captured environment (rest.filterMap Dep.runtime)).support)
          rw [tail, lift_merge]
      | ticket name => rfl

/-- Agreement requires resource closure. Before opening, a free bound name is
    informative source metadata and cannot be erased into empty runtime storage. -/
theorem runtime_agreement (code : Code) (closed : code.ResourceClosed) :
    infer (runtimeEnv environment) code = lift (ResultSummaries.analyze environment code).support := by
  cases code with
  | unit | boolean | integer | «variable» => rfl
  | resourceRef name => cases name with
      | activation => rfl
      | bound => cases closed
  | app | perform | handle | resume | discard | resource | cleanup => rfl
  | pair left right =>
      obtain ⟨leftClosed, rightClosed⟩ := List.append_eq_nil_iff.mp closed
      change merge (infer (runtimeEnv environment) left) (infer (runtimeEnv environment) right) =
        lift (merge (ResultSummaries.analyze environment left).support (ResultSummaries.analyze environment right).support)
      rw [runtime_agreement left leftClosed, runtime_agreement right rightClosed, lift_merge]
  | branch condition yes no =>
      obtain ⟨prefixClosed, noClosed⟩ := List.append_eq_nil_iff.mp closed
      have yesClosed := (List.append_eq_nil_iff.mp prefixClosed).2
      change merge (infer (runtimeEnv environment) yes) (infer (runtimeEnv environment) no) =
        lift (merge (ResultSummaries.analyze environment yes).support (ResultSummaries.analyze environment no).support)
      rw [runtime_agreement yes yesClosed, runtime_agreement no noClosed, lift_merge]
  | lambda parameter body =>
      have exactCaptures := captured_runtime (environment := environment) (dependencies (.lambda parameter body))
        (closed_dependencies_have_no_bound closed)
      rw [runtime_dependencies] at exactCaptures
      exact exactCaptures
  | bind parameter initializer body =>
      obtain ⟨initializerClosed, bodyClosed⟩ := List.append_eq_nil_iff.mp closed
      change infer (fun name => if name = parameter then infer (runtimeEnv environment) initializer else runtimeEnv environment name) body =
        lift (ResultSummaries.analyze (ResultSummaries.extendAnalysis environment parameter
          (ResultSummaries.analyze environment initializer)) body).support
      have same :
          (fun name => if name = parameter then infer (runtimeEnv environment) initializer else runtimeEnv environment name) =
          runtimeEnv (ResultSummaries.extendAnalysis environment parameter (ResultSummaries.analyze environment initializer)) := by
        funext name
        by_cases atParameter : name = parameter
        · simp only [if_pos atParameter, runtimeEnv, ResultSummaries.extendAnalysis]
          exact runtime_agreement initializer initializerClosed
        · simp only [if_neg atParameter, runtimeEnv, ResultSummaries.extendAnalysis]
      rw [same]
      exact runtime_agreement body bodyClosed
termination_by sizeOf code

theorem lift_injective : Function.Injective lift := by
  intro first second same
  cases first with
  | none => cases second with
      | none => rfl
      | some => cases same
  | some first => cases second with
      | none => cases same
      | some second =>
          have listEq : first.map ResourceName.activation = second.map ResourceName.activation := Option.some.inj same
          have restored := congrArg (List.map (fun name => match name with
            | ResourceName.activation identity => identity | .bound name => name)) listEq
          simp only [List.map_map, Function.comp_def] at restored
          change first.map id = second.map id at restored
          exact congrArg some (by simpa only [List.map_id] using restored)

/-- A finite source result lies wholly in the supplied resource world.
    This is a support bound, not proof of live ownership. It contains no
    unresolved resource binder. -/
def SourceBound (environment : ResultSummaries.Environment) (world : List Nat) (body : Code) : Prop :=
  ∃ resources, infer (runtimeEnv environment) body = some (resources.map ResourceName.activation) ∧ resources ⊆ world

def available (world : List Nat) : List ResourceName → Bool
  | [] => true
  | .bound _ :: _ => false
  | .activation identity :: rest => decide (identity ∈ world) && available world rest

theorem available_iff (names : List ResourceName) :
    available world names = true ↔ ∃ resources, names = resources.map ResourceName.activation ∧ resources ⊆ world := by
  induction names with
  | nil =>
      constructor
      · intro _; exact ⟨[], rfl, List.nil_subset _⟩
      · intro _; rfl
  | cons name rest ih => cases name with
      | bound name =>
          constructor
          · intro impossible; cases impossible
          · rintro ⟨resources, same, _⟩
            cases resources with
            | nil => cases same
            | cons first tail => cases (List.cons.inj same).1
      | activation identity =>
          constructor
          · intro checked
            have parts : identity ∈ world ∧ available world rest = true := by simpa [available] using checked
            obtain ⟨resources, same, contained⟩ := ih.mp parts.2
            refine ⟨identity :: resources, congrArg (List.cons (.activation identity)) same, ?_⟩
            intro resource member
            rcases List.mem_cons.mp member with equal | retained
            · exact equal ▸ parts.1
            · exact contained retained
          · rintro ⟨resources, same, contained⟩
            cases resources with
            | nil => cases same
            | cons first tail =>
                have parts := List.cons.inj same
                have head := ResourceName.activation.inj parts.1
                subst first
                have remaining := ih.mpr ⟨tail, parts.2, fun _ member => contained (List.mem_cons_of_mem _ member)⟩
                simp only [available, Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨contained List.mem_cons_self, remaining⟩

/-- This finite check reads the template and its ordinary support environment.
    It does not execute the body or enumerate future activation identities. -/
def check (environment : ResultSummaries.Environment) (world : List Nat) (body : Code) : Bool :=
  match infer (runtimeEnv environment) body with
  | none => false
  | some names => available world names

theorem check_iff_source_bound : check environment world body = true ↔ SourceBound environment world body := by
  cases known : infer (runtimeEnv environment) body with
  | none => simp [check, SourceBound, known]
  | some names =>
      simp only [check, SourceBound, known, Option.some.injEq]
      exact available_iff names

theorem infer_runtime_instantiate (code : Code) (resources : Instantiation.Environment) :
    infer (runtimeEnv environment) (code.instantiate resources) =
      mapBound resources (infer (runtimeEnv environment) code) := by
  have same : (fun name => mapBound resources (runtimeEnv environment name)) = runtimeEnv environment := by
    funext name
    exact map_lift _
  simpa only [same] using infer_instantiate code (runtimeEnv environment) resources

/-- A fresh opening cannot turn a rejected resource name into a member of
    the supplied world. Allocated identities are unaffected by opening. -/
theorem available_fresh_opening (names : List ResourceName) (fresh : identity ∉ world) :
    available world (names.map (ResourceName.instantiate (Instantiation.Environment.empty.bind binder identity))) =
      available world names := by
  induction names with
  | nil => rfl
  | cons name rest ih => cases name with
      | activation existing => simp only [List.map_cons, ResourceName.instantiate, available, ih]
      | bound name =>
          by_cases same : name = binder
          · simp [List.map_cons, ResourceName.instantiate, Instantiation.Environment.bind,
              same, available, fresh]
          · simp [List.map_cons, ResourceName.instantiate, Instantiation.Environment.bind,
              Instantiation.Environment.empty, same, available]

/-- This equality is about the finite checker, even on a template that is
    not resource-closed. It does not assert runtime availability or ownership. -/
theorem check_fresh_opening (code : Code) (fresh : identity ∉ world) :
    check environment world (code.instantiate (Instantiation.Environment.empty.bind binder identity)) =
      check environment world code := by
  unfold check
  rw [infer_runtime_instantiate]
  cases known : infer (runtimeEnv environment) code with
  | none => rfl
  | some names => exact available_fresh_opening names fresh

theorem source_bound_runtime_iff (closed : code.ResourceClosed) :
    SourceBound environment world code ↔
      ∃ resources, (ResultSummaries.analyze environment code).support = some resources ∧ resources ⊆ world := by
  constructor
  · rintro ⟨resources, known, contained⟩
    rw [runtime_agreement _ closed] at known
    exact ⟨resources, lift_injective known, contained⟩
  · rintro ⟨resources, known, contained⟩
    refine ⟨resources, ?_, contained⟩
    rw [runtime_agreement _ closed, known]
    rfl

/-- Checking the template is equivalent to bounding the actual freshly
    opened body's conservative result inside the earlier world. This is
    completeness for this observer, not for all safe resource returns. -/
theorem fresh_opening_runtime_iff
    (closed : (Code.resource binder initializer body).ResourceClosed)
    (fresh : identity ∉ world) :
    check environment world body = true ↔
      ∃ resources, (ResultSummaries.analyze environment
        (body.instantiate (Instantiation.Environment.empty.bind binder identity))).support = some resources ∧ resources ⊆ world := by
  rw [← check_fresh_opening body fresh (binder := binder)]
  exact check_iff_source_bound.trans
    (source_bound_runtime_iff (binding_closes_body binder identity initializer body closed))

theorem opened_source_bound
    (bound : SourceBound environment world body)
    (closed : (Code.resource binder initializer body).ResourceClosed) :
    ∃ resources, (ResultSummaries.analyze environment
      (body.instantiate (Instantiation.Environment.empty.bind binder identity))).support = some resources ∧ resources ⊆ world := by
  obtain ⟨resources, inferred, contained⟩ := bound
  let opening := Instantiation.Environment.empty.bind binder identity
  have sameEnv : (fun name => mapBound opening (runtimeEnv environment name)) = runtimeEnv environment := by
    funext name
    exact map_lift _
  have transport := infer_instantiate body (runtimeEnv environment) opening
  rw [sameEnv, runtime_agreement _ (binding_closes_body binder identity initializer body closed), inferred] at transport
  have same : lift (ResultSummaries.analyze environment (body.instantiate opening)).support = lift (some resources) := by
    change lift (ResultSummaries.analyze environment (body.instantiate opening)).support = mapBound opening (lift (some resources)) at transport
    rw [map_lift] at transport
    exact transport
  exact ⟨resources, lift_injective same, contained⟩

theorem source_entry_certificate
    (bound : SourceBound environment world body)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (fresh : identity ∉ world) :
    ReturnBoundaries.AllocationReturn environment [.resource identity]
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ := by
  obtain ⟨resources, known, contained⟩ := opened_source_bound bound closed (identity := identity)
  exact .cell (Or.inl ⟨resources, known, fun member => fresh (contained member)⟩)

theorem source_entry_constructs
    (bound : SourceBound environment world body)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
    ReturnBoundaries.AllocationReturn environment [.resource identity]
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ :=
  ⟨.enterCell binder identity payload body scope answer tail closed, source_entry_certificate bound closed fresh⟩

theorem checked_source_entry
    (checked : check environment world body = true)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
    ReturnBoundaries.AllocationReturn environment [.resource identity]
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ :=
  source_entry_constructs (check_iff_source_bound.mp checked) closed fresh

namespace Examples

def unknownEnvironment : ResultSummaries.Environment := fun _ => .unknown

theorem own_template_capture_rejected :
    check unknownEnvironment [] ReturnBoundaries.Examples.retainingTemplate = false := rfl

theorem outer_capture_accepted :
    check unknownEnvironment [8] (ResultSummaries.Examples.retainingConstant 8) = true := rfl

def aliasCapture : Code := .bind 3 (.resourceRef (.bound 4)) (.lambda 0 (.variable 3))

theorem alias_capture_rejected : check unknownEnvironment [] aliasCapture = false := rfl

def unusedAlias : Code := .bind 3 (.resourceRef (.bound 4)) (.lambda 0 (.integer 42))

theorem unused_alias_accepted : check unknownEnvironment [] unusedAlias = true := rfl

def nestedShadow : Code := .lambda 0 (.resource 4 (.integer 0)
  (.bind 1 (.resourceRef (.bound 4)) (.integer 42)))

theorem nested_resource_shadows_its_own_name :
    dependencies nestedShadow = [] ∧ check unknownEnvironment [] nestedShadow = true := ⟨rfl, rfl⟩

def initializerCapture : Code := .lambda 0 (.resource 4
  (.bind 1 (.resourceRef (.bound 4)) (.integer 0)) (.integer 42))

theorem initializer_remains_outside_new_binding :
    dependencies initializerCapture = [.resource (.bound 4)] ∧
    check unknownEnvironment [] initializerCapture = false := ⟨rfl, rfl⟩

def existingActivation : Code := .lambda 0 (.resource 4 (.integer 0)
  (.bind 1 (.resourceRef (.activation 4)) (.integer 42)))

theorem equal_numeric_activation_is_not_shadowed :
    dependencies existingActivation = [.resource (.activation 4)] ∧
    check unknownEnvironment [] existingActivation = false ∧
    check unknownEnvironment [4] existingActivation = true := ⟨rfl, rfl, rfl⟩

def metadataCapture : Code := .lambda 0
  (.perform (.user 1 [.apply (.nominal 2) (.resource (.bound 4))]) 0 .unit)

theorem nested_operation_metadata_retains_bound_name :
    dependencies metadataCapture = [.resource (.bound 4)] ∧
    check unknownEnvironment [] metadataCapture = false := ⟨rfl, rfl⟩

theorem unknown_ordinary_capture_rejected :
    check unknownEnvironment [] (.lambda 0 (.variable 3)) = false := rfl

theorem nonfresh_opening_can_change_the_check :
    check unknownEnvironment [8] (.resourceRef (.bound 4)) = false ∧
    check unknownEnvironment [8] ((Code.resourceRef (.bound 4)).instantiate
      (Instantiation.Environment.empty.bind 4 8)) = true := ⟨rfl, rfl⟩

theorem unresolved_capture_has_misleading_runtime_projection :
    check unknownEnvironment [] (.lambda 0 (.resourceRef (.bound 5))) = false ∧
    (ResultSummaries.analyze unknownEnvironment (.lambda 0 (.resourceRef (.bound 5)))).support = some [] := ⟨rfl, rfl⟩

theorem application_result_stays_unknown :
    infer (runtimeEnv unknownEnvironment) (.app (.lambda 0 (.integer 42)) .unit) = none := rfl

def ignoredApplication : Code := .bind 3 (.app ReturnBoundaries.Examples.retainingTemplate .unit)
  (.lambda 0 (.integer 42))

theorem ignored_application_has_empty_result_bound :
    check unknownEnvironment [] ignoredApplication = true := rfl

def copiedReadClosure : Code := .bind 3
  (.perform (.cell (.bound 4)) 0 (.resourceRef (.bound 4))) (.lambda 0 (.variable 3))

/-- Current Core accepts closures retaining a copied Int. This conservative
    observer still needs type-informed operation-result bounds to infer that
    case; unknown is not silently replaced with a scalar result. -/
theorem copied_read_closure_is_still_unknown :
    infer (runtimeEnv unknownEnvironment) copiedReadClosure = none ∧
    check unknownEnvironment [] copiedReadClosure = false := ⟨rfl, rfl⟩

/-- A function-valued return gets an inferred entry certificate for every
    world-fresh identity. This constructs a raw event, not lifetime freshness
    or complete typing/access admission. -/
theorem function_return_entry (fresh : identity ∉ [8]) :
    RawStep ⟨.resource 4 (.integer 41) (ResultSummaries.Examples.retainingConstant 8), .none, .nil⟩
      ⟨(ResultSummaries.Examples.retainingConstant 8).instantiate (Instantiation.Environment.empty.bind 4 identity), .none,
        .push (.cell identity 41 .none ReturnBoundaries.Examples.callbackAnswer) .nil⟩ [.resource identity] [] ∧
    ReturnBoundaries.AllocationReturn unknownEnvironment [.resource identity]
      ⟨(ResultSummaries.Examples.retainingConstant 8).instantiate (Instantiation.Environment.empty.bind 4 identity), .none,
        .push (.cell identity 41 .none ReturnBoundaries.Examples.callbackAnswer) .nil⟩ := by
  apply checked_source_entry (world := [8]) outer_capture_accepted _ fresh
  simp [Code.ResourceClosed, Code.freeNames, ResultSummaries.Examples.retainingConstant, ResourceName.freeNames]

end Examples

end Ash.OneShot.TemplateSupport

#print axioms Ash.OneShot.TemplateSupport.map_merge
#print axioms Ash.OneShot.TemplateSupport.lift_merge
#print axioms Ash.OneShot.TemplateSupport.map_lift
#print axioms Ash.OneShot.TemplateSupport.atom_instantiate
#print axioms Ash.OneShot.TemplateSupport.captured_instantiate
#print axioms Ash.OneShot.TemplateSupport.infer_instantiate
#print axioms Ash.OneShot.TemplateSupport.captured_runtime
#print axioms Ash.OneShot.TemplateSupport.runtime_agreement
#print axioms Ash.OneShot.TemplateSupport.lift_injective
#print axioms Ash.OneShot.TemplateSupport.available_iff
#print axioms Ash.OneShot.TemplateSupport.check_iff_source_bound
#print axioms Ash.OneShot.TemplateSupport.infer_runtime_instantiate
#print axioms Ash.OneShot.TemplateSupport.available_fresh_opening
#print axioms Ash.OneShot.TemplateSupport.check_fresh_opening
#print axioms Ash.OneShot.TemplateSupport.source_bound_runtime_iff
#print axioms Ash.OneShot.TemplateSupport.fresh_opening_runtime_iff
#print axioms Ash.OneShot.TemplateSupport.opened_source_bound
#print axioms Ash.OneShot.TemplateSupport.source_entry_certificate
#print axioms Ash.OneShot.TemplateSupport.source_entry_constructs
#print axioms Ash.OneShot.TemplateSupport.checked_source_entry
#print axioms Ash.OneShot.TemplateSupport.Examples.own_template_capture_rejected
#print axioms Ash.OneShot.TemplateSupport.Examples.outer_capture_accepted
#print axioms Ash.OneShot.TemplateSupport.Examples.alias_capture_rejected
#print axioms Ash.OneShot.TemplateSupport.Examples.unused_alias_accepted
#print axioms Ash.OneShot.TemplateSupport.Examples.nested_resource_shadows_its_own_name
#print axioms Ash.OneShot.TemplateSupport.Examples.initializer_remains_outside_new_binding
#print axioms Ash.OneShot.TemplateSupport.Examples.equal_numeric_activation_is_not_shadowed
#print axioms Ash.OneShot.TemplateSupport.Examples.nested_operation_metadata_retains_bound_name
#print axioms Ash.OneShot.TemplateSupport.Examples.unknown_ordinary_capture_rejected
#print axioms Ash.OneShot.TemplateSupport.Examples.nonfresh_opening_can_change_the_check
#print axioms Ash.OneShot.TemplateSupport.Examples.unresolved_capture_has_misleading_runtime_projection
#print axioms Ash.OneShot.TemplateSupport.Examples.application_result_stays_unknown
#print axioms Ash.OneShot.TemplateSupport.Examples.ignored_application_has_empty_result_bound
#print axioms Ash.OneShot.TemplateSupport.Examples.copied_read_closure_is_still_unknown
#print axioms Ash.OneShot.TemplateSupport.Examples.function_return_entry
