import DeclarationResults

/-!
Finite template return checking from validated resource-parameter declarations.
Free resource names remain visible until opening. The check supplies the local
allocation certificate used by signature-aware execution preservation.
-/

namespace Ash.OneShot.DeclarationTemplates
open Instantiation ScopedExpressions ScopedExecution TemplateDependencies
open TemplateSupport (Bound SupportEnv merge mapBound lift runtimeEnv captured
  map_merge map_lift lift_merge lift_injective captured_instantiate captured_runtime
  available available_iff available_fresh_opening)
open DeclarationResults (operationBound signature)

def infer (registry : DeclarationRegistry) (environment : SupportEnv) : Code → Bound
  | .unit | .boolean _ | .integer _ => some []
  | .variable name => environment name
  | .resourceRef name => some [name]
  | .pair left right => merge (infer registry environment left) (infer registry environment right)
  | .lambda parameter body => captured environment (dependencies (.lambda parameter body))
  | .bind parameter initializer body =>
      infer registry (fun name => if name = parameter then infer registry environment initializer else environment name) body
  | .branch _ yes no => merge (infer registry environment yes) (infer registry environment no)
  | .perform effect operation _ => operationBound registry effect operation
  | .app _ _ | .handle _ _ _ | .resume _ _ | .discard _ | .resource _ _ _ | .cleanup _ _ => none

theorem infer_instantiate (code : Code) (environment : SupportEnv) (resources : Instantiation.Environment) :
    infer registry (fun name => mapBound resources (environment name)) (code.instantiate resources) =
      mapBound resources (infer registry environment code) := by
  cases code with
  | unit | boolean | integer | «variable» | resourceRef => rfl
  | app | handle | resume | discard | resource | cleanup => rfl
  | perform effect operation operand => exact DeclarationResults.operation_bound_open effect operation
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
          (fun name => if name = parameter then infer registry (fun n => mapBound resources (environment n))
            (initializer.instantiate resources) else mapBound resources (environment name)) =
          (fun name => mapBound resources (if name = parameter then infer registry environment initializer else environment name)) := by
        funext name
        split
        · exact infer_instantiate initializer environment resources
        · rfl
      rw [same]
      exact infer_instantiate body _ resources
termination_by sizeOf code

/-- Agreement requires resource closure. Before opening, a free bound name is
    informative source metadata and cannot be erased into empty runtime storage. -/
theorem runtime_agreement (code : Code) (closed : code.ResourceClosed) :
    infer registry (runtimeEnv environment) code = lift (OperationResults.analyze (signature registry) environment code).support := by
  cases code with
  | unit | boolean | integer | «variable» => rfl
  | resourceRef name => cases name with
      | activation => rfl
      | bound => cases closed
  | app | handle | resume | discard | resource | cleanup => rfl
  | perform effect operation operand =>
      exact DeclarationResults.closed_operation_bound_runtime (List.append_eq_nil_iff.mp closed).1
  | pair left right =>
      obtain ⟨leftClosed, rightClosed⟩ := List.append_eq_nil_iff.mp closed
      change merge (infer registry (runtimeEnv environment) left) (infer registry (runtimeEnv environment) right) =
        lift (merge (OperationResults.analyze (signature registry) environment left).support (OperationResults.analyze (signature registry) environment right).support)
      rw [runtime_agreement left leftClosed, runtime_agreement right rightClosed, lift_merge]
  | branch condition yes no =>
      obtain ⟨prefixClosed, noClosed⟩ := List.append_eq_nil_iff.mp closed
      have yesClosed := (List.append_eq_nil_iff.mp prefixClosed).2
      change merge (infer registry (runtimeEnv environment) yes) (infer registry (runtimeEnv environment) no) =
        lift (merge (OperationResults.analyze (signature registry) environment yes).support (OperationResults.analyze (signature registry) environment no).support)
      rw [runtime_agreement yes yesClosed, runtime_agreement no noClosed, lift_merge]
  | lambda parameter body =>
      have exactCaptures := captured_runtime (environment := environment) (dependencies (.lambda parameter body))
        (closed_dependencies_have_no_bound closed)
      rw [runtime_dependencies] at exactCaptures
      exact exactCaptures
  | bind parameter initializer body =>
      obtain ⟨initializerClosed, bodyClosed⟩ := List.append_eq_nil_iff.mp closed
      change infer registry (fun name => if name = parameter then infer registry (runtimeEnv environment) initializer else runtimeEnv environment name) body =
        lift (OperationResults.analyze (signature registry) (ResultSummaries.extendAnalysis environment parameter
          (OperationResults.analyze (signature registry) environment initializer)) body).support
      have same :
          (fun name => if name = parameter then infer registry (runtimeEnv environment) initializer else runtimeEnv environment name) =
          runtimeEnv (ResultSummaries.extendAnalysis environment parameter (OperationResults.analyze (signature registry) environment initializer)) := by
        funext name
        by_cases atParameter : name = parameter
        · simp only [if_pos atParameter, runtimeEnv, ResultSummaries.extendAnalysis]
          exact runtime_agreement initializer initializerClosed
        · simp only [if_neg atParameter, runtimeEnv, ResultSummaries.extendAnalysis]
      rw [same]
      exact runtime_agreement body bodyClosed
termination_by sizeOf code

/-- A finite source result lies wholly in the supplied resource world.
    This is a support bound, not proof of live ownership. It contains no
    unresolved resource binder. -/
def SourceBound (registry : DeclarationRegistry) (environment : ResultSummaries.Environment) (world : List Nat) (body : Code) : Prop :=
  ∃ resources, infer registry (runtimeEnv environment) body = some (resources.map ResourceName.activation) ∧ resources ⊆ world

/-- This finite check reads the template and its ordinary support environment.
    It does not execute the body or enumerate future activation identities. -/
def check (registry : DeclarationRegistry) (environment : ResultSummaries.Environment) (world : List Nat) (body : Code) : Bool :=
  match infer registry (runtimeEnv environment) body with
  | none => false
  | some names => available world names

theorem check_iff_source_bound : check registry environment world body = true ↔ SourceBound registry environment world body := by
  cases known : infer registry (runtimeEnv environment) body with
  | none => simp [check, SourceBound, known]
  | some names =>
      simp only [check, SourceBound, known, Option.some.injEq]
      exact available_iff names

theorem infer_runtime_instantiate (code : Code) (resources : Instantiation.Environment) :
    infer registry (runtimeEnv environment) (code.instantiate resources) =
      mapBound resources (infer registry (runtimeEnv environment) code) := by
  have same : (fun name => mapBound resources (runtimeEnv environment name)) = runtimeEnv environment := by
    funext name
    exact map_lift _
  simpa only [same] using infer_instantiate code (runtimeEnv environment) resources

/-- This equality is about the finite checker, even on a template that is
    not resource-closed. It does not assert runtime availability or ownership. -/
theorem check_fresh_opening (code : Code) (fresh : identity ∉ world) :
    check registry environment world (code.instantiate (Instantiation.Environment.empty.bind binder identity)) =
      check registry environment world code := by
  unfold check
  rw [infer_runtime_instantiate]
  cases known : infer registry (runtimeEnv environment) code with
  | none => rfl
  | some names => exact available_fresh_opening names fresh

theorem source_bound_runtime_iff (closed : code.ResourceClosed) :
    SourceBound registry environment world code ↔
      ∃ resources, (OperationResults.analyze (signature registry) environment code).support = some resources ∧ resources ⊆ world := by
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
    check registry environment world body = true ↔
      ∃ resources, (OperationResults.analyze (signature registry) environment
        (body.instantiate (Instantiation.Environment.empty.bind binder identity))).support = some resources ∧ resources ⊆ world := by
  rw [← check_fresh_opening body fresh (binder := binder)]
  exact check_iff_source_bound.trans
    (source_bound_runtime_iff (binding_closes_body binder identity initializer body closed))

theorem opened_source_bound
    (bound : SourceBound registry environment world body)
    (closed : (Code.resource binder initializer body).ResourceClosed) :
    ∃ resources, (OperationResults.analyze (signature registry) environment
      (body.instantiate (Instantiation.Environment.empty.bind binder identity))).support = some resources ∧ resources ⊆ world := by
  obtain ⟨resources, inferred, contained⟩ := bound
  let opening := Instantiation.Environment.empty.bind binder identity
  have sameEnv : (fun name => mapBound opening (runtimeEnv environment name)) = runtimeEnv environment := by
    funext name
    exact map_lift _
  have transport := infer_instantiate (registry := registry) body (runtimeEnv environment) opening
  rw [sameEnv, runtime_agreement _ (binding_closes_body binder identity initializer body closed), inferred] at transport
  have same : lift (OperationResults.analyze (signature registry) environment (body.instantiate opening)).support = lift (some resources) := by
    change lift (OperationResults.analyze (signature registry) environment (body.instantiate opening)).support = mapBound opening (lift (some resources)) at transport
    rw [map_lift] at transport
    exact transport
  exact ⟨resources, lift_injective same, contained⟩

theorem source_entry_certificate
    (bound : SourceBound registry environment world body)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (fresh : identity ∉ world) :
    OperationReturns.AllocationReturn (signature registry) environment [.resource identity]
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ := by
  obtain ⟨resources, known, contained⟩ := opened_source_bound bound closed (identity := identity)
  exact .cell (Or.inl ⟨resources, known, fun member => fresh (contained member)⟩)

theorem source_entry_constructs
    (bound : SourceBound registry environment world body)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
    OperationReturns.AllocationReturn (signature registry) environment [.resource identity]
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ :=
  ⟨.enterCell binder identity payload body scope answer tail closed, source_entry_certificate bound closed fresh⟩

theorem checked_source_entry
    (checked : check registry environment world body = true)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed)
    (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
    OperationReturns.AllocationReturn (signature registry) environment [.resource identity]
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ :=
  source_entry_constructs (check_iff_source_bound.mp checked) closed fresh


/-- An actual named allocation chooses an identity fresh in issuance history.
    The finite template check supplies that same event's return bound. -/
theorem resource_named_preserves_checked
    (step : NamedAccessStep ambient
      ⟨⟨⟨.resource binder (.integer payload) body, scope, tail⟩, issued, completed⟩, activations⟩ after)
    (templateChecked : check declarations environment (ScopedTyping.resourceWorld issued) body = true)
    (checked : OperationReturns.ConfigurationChecked (signature declarations) environment
      ⟨.resource binder (.integer payload) body, scope, tail⟩) :
    OperationReturns.ConfigurationChecked (signature declarations) environment after.execution.configuration := by
  cases step.execution with
  | event after created discharged raw freshOwners freshHandlers =>
      cases raw with
      | focus plain focus _ =>
          cases plain
          cases focus with
          | resource notValue => exact False.elim (notValue trivial)
      | @startCleanup action saved closed scope tail => exact False.elim closed.1
      | plug | leaveHandler | leaveCell | leaveClause =>
          simp_all [ScopedExpressions.ClosedValue, Code.IsValue]
      | enterCell binder identity payload body scope answer tail closed =>
          have fresh : identity ∉ ScopedTyping.resourceWorld issued := by
            intro member
            exact (List.nodup_append.mp freshOwners).2.2 (.resource identity)
              (ScopedTyping.mem_resource_world.mp member) (.resource identity) List.mem_cons_self rfl
          obtain ⟨resources, known, contained⟩ := opened_source_bound
            (check_iff_source_bound.mp templateChecked) closed (identity := identity)
          exact ⟨Or.inl ⟨resources, known, fun member => fresh (contained member)⟩, checked⟩

theorem checked_resource_entry_progress
    (valid : ScopedPortJoint.Valid (signature declarations) policy registry ambient
      ⟨⟨⟨.resource binder (.integer payload) body, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (templateChecked : check declarations environment (ScopedTyping.resourceWorld issued) body = true)
    (checked : OperationReturns.ConfigurationChecked (signature declarations) environment
      ⟨.resource binder (.integer payload) body, scope, tail⟩) :
    ∃ after,
      NamedAccessStep ambient
        ⟨⟨⟨.resource binder (.integer payload) body, scope, tail⟩, issued, completed⟩, activations⟩ after ∧
      ScopedPortJoint.Valid (signature declarations) policy registry ambient after result outgoing ∧
      OperationReturns.ConfigurationChecked (signature declarations) environment after.execution.configuration := by
  obtain ⟨after, step, next⟩ := ScopedPortJoint.resource_entry_constructs_joint_configuration valid trivial
  exact ⟨after, step, next, resource_named_preserves_checked step templateChecked checked⟩

namespace Examples

def registry : DeclarationRegistry := fun _ => none
def environment : ResultSummaries.Environment := fun _ => .unknown

theorem copied_read_template_checked :
    check registry environment [] TemplateSupport.Examples.copiedReadClosure = true ∧
    TemplateSupport.check environment [] TemplateSupport.Examples.copiedReadClosure = false := ⟨rfl, rfl⟩

theorem retained_reader_rejected :
    check registry environment []
      (.lambda 0 (.perform (.cell (.bound 4)) 0 (.resourceRef (.bound 4)))) = false := rfl

theorem copied_template_entry (identity : Nat) :
    let body := TemplateSupport.Examples.copiedReadClosure
    let after : Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind 4 identity), .none,
      .push (.cell identity 41 .none ReturnBoundaries.Examples.callbackAnswer) .nil⟩
    RawStep ⟨.resource 4 (.integer 41) body, .none, .nil⟩ after [.resource identity] [] ∧
    OperationReturns.AllocationReturn (signature registry) environment [.resource identity] after := by
  exact checked_source_entry copied_read_template_checked.1 rfl (by simp)

def getReference : FamilyTemplate := ⟨[0], [⟨.unit, .reference (.bound 0)⟩]⟩
def referenceRegistry : DeclarationRegistry := fun family => if family = 9 then some getReference else none

def returningReference : Code := .bind 3
  (.perform (.user 9 [.resource (.bound 4)]) 0 .unit) (.lambda 0 (.variable 3))

theorem declared_reference_capture_rejected :
    infer referenceRegistry (runtimeEnv environment) returningReference = some [.bound 4] ∧
    check referenceRegistry environment [] returningReference = false := by decide

theorem declared_outer_reference_capture_accepted :
    check referenceRegistry environment [8]
      (.bind 3 (.perform (.user 9 [.resource (.activation 8)]) 0 .unit) (.lambda 0 (.variable 3))) = true := by decide

def getInteger : FamilyTemplate := ⟨[], [⟨.unit, .integer⟩]⟩
def integerRegistry : DeclarationRegistry := fun family => if family = 83 then some getInteger else none

theorem generic_copied_integer_checked :
    check integerRegistry environment []
      (.bind 3 (.perform (.user 83 []) 0 .unit) (.lambda 0 (.variable 3))) = true := by decide

theorem callable_result_remains_unknown :
    check (fun _ => some (⟨[], [⟨.unit, .function .unit .integer [] []⟩]⟩ : FamilyTemplate)) environment []
      (.perform (.user 83 []) 0 .unit) = false := by decide

theorem unknown_call_remains_unknown :
    check registry environment [] (.app (.lambda 0 (.integer 41)) .unit) = false := rfl

theorem unopened_capture_not_erased :
    check registry environment [] (.lambda 0 (.resourceRef (.bound 4))) = false ∧
    (OperationResults.analyze (signature registry) environment (.lambda 0 (.resourceRef (.bound 4)))).support = some [] :=
  ⟨rfl, rfl⟩

def copiedInitial : Code := .resource 4 (.integer 41) TemplateSupport.Examples.copiedReadClosure
def copiedState : NamedState := ⟨⟨⟨copiedInitial, .none, .nil⟩, [], []⟩, []⟩
def policy : Syntax.TicketPolicy := fun _ => ActionRequirements.resumeOnly

theorem copied_initial_typed :
    ScopedPorts.Typed (signature registry) [] ScopedPorts.TypeEnv.empty .none [] copiedInitial
      (.function .unit .integer []) := by
  refine .resource (residual := []) .integer ?_ (List.nil_subset _) (List.nil_subset _) (List.nil_subset _)
  intro identity fresh
  change ScopedPorts.Typed (signature registry) [identity] ScopedPorts.TypeEnv.empty .none [.cell identity]
    (.bind 3 (.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)))
      (.lambda 0 (.variable 3))) (.function .unit .integer [])
  exact .bind (.perform rfl List.mem_cons_self (.reference List.mem_cons_self) (List.nil_subset _))
    (.lambda (.variable rfl (List.nil_subset _)) (List.nil_subset _))

theorem copied_initial_valid :
    ScopedPortJoint.Valid (signature registry) policy (fun _ => none) [] copiedState (.function .unit .integer []) [] :=
  ScopedPortJoint.initial_configuration_valid copied_initial_typed
    (.resource .integer (.bind (.perform .resourceRef) (.lambda .variable))) rfl

/-- Concrete initial-state nonvacuity of the joint entry theorem. It establishes
    one fresh allocation step; later execution and final release are separate. -/
theorem copied_initial_joint_entry :
    ∃ after, NamedAccessStep [] copiedState after ∧
      ScopedPortJoint.Valid (signature registry) policy (fun _ => none) [] after (.function .unit .integer []) [] ∧
      OperationReturns.ConfigurationChecked (signature registry) environment after.execution.configuration :=
  checked_resource_entry_progress copied_initial_valid copied_read_template_checked.1 trivial

end Examples

end Ash.OneShot.DeclarationTemplates

#print axioms Ash.OneShot.DeclarationTemplates.infer_instantiate
#print axioms Ash.OneShot.DeclarationTemplates.runtime_agreement
#print axioms Ash.OneShot.DeclarationTemplates.check_iff_source_bound
#print axioms Ash.OneShot.DeclarationTemplates.infer_runtime_instantiate
#print axioms Ash.OneShot.DeclarationTemplates.check_fresh_opening
#print axioms Ash.OneShot.DeclarationTemplates.source_bound_runtime_iff
#print axioms Ash.OneShot.DeclarationTemplates.fresh_opening_runtime_iff
#print axioms Ash.OneShot.DeclarationTemplates.opened_source_bound
#print axioms Ash.OneShot.DeclarationTemplates.source_entry_certificate
#print axioms Ash.OneShot.DeclarationTemplates.source_entry_constructs
#print axioms Ash.OneShot.DeclarationTemplates.checked_source_entry
#print axioms Ash.OneShot.DeclarationTemplates.resource_named_preserves_checked
#print axioms Ash.OneShot.DeclarationTemplates.checked_resource_entry_progress
#print axioms Ash.OneShot.DeclarationTemplates.Examples.copied_read_template_checked
#print axioms Ash.OneShot.DeclarationTemplates.Examples.retained_reader_rejected
#print axioms Ash.OneShot.DeclarationTemplates.Examples.copied_template_entry
#print axioms Ash.OneShot.DeclarationTemplates.Examples.declared_reference_capture_rejected
#print axioms Ash.OneShot.DeclarationTemplates.Examples.declared_outer_reference_capture_accepted
#print axioms Ash.OneShot.DeclarationTemplates.Examples.generic_copied_integer_checked
#print axioms Ash.OneShot.DeclarationTemplates.Examples.callable_result_remains_unknown
#print axioms Ash.OneShot.DeclarationTemplates.Examples.unknown_call_remains_unknown
#print axioms Ash.OneShot.DeclarationTemplates.Examples.unopened_capture_not_erased

#print axioms Ash.OneShot.DeclarationTemplates.Examples.copied_initial_typed
#print axioms Ash.OneShot.DeclarationTemplates.Examples.copied_initial_valid
#print axioms Ash.OneShot.DeclarationTemplates.Examples.copied_initial_joint_entry
