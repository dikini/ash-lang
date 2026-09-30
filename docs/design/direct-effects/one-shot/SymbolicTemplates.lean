import DeclarationSubstitution

/-!
Finite symbolic-world return checks, transported through actual lexical
resource opening. Captured ordinary support is snapshotted before a shadowing
binder masks the body environment. This layer reuses the existing inference
and execution grammars; metadata realization is not whole-term admission.
-/

namespace Ash.OneShot.SymbolicTemplates
open Instantiation ScopedExpressions ScopedExecution
open TemplateSupport (Bound SupportEnv mapBound lift runtimeEnv)
open DeclarationResults (signature)

def snapshot (resources : Instantiation.Environment) (environment : SupportEnv) : SupportEnv :=
  fun name => mapBound resources (environment name)

def bindSupport (environment : SupportEnv) (name : Nat) (bound : Bound) : SupportEnv :=
  fun other => if other = name then bound else environment other

/-- Membership is checked on symbolic resource identities. A scoped caller
    must keep outer snapshots distinct from a newly shadowing lexical name. -/
def check (declarations : DeclarationRegistry) (environment : SupportEnv)
    (world : List ResourceName) (code : Code) : Bool :=
  match DeclarationTemplates.infer declarations environment code with
  | none => false
  | some names => decide (names ⊆ world)

theorem check_iff_bound : check declarations environment world code = true ↔
    ∃ names, DeclarationTemplates.infer declarations environment code = some names ∧ names ⊆ world := by
  cases known : DeclarationTemplates.infer declarations environment code with
  | none => simp [check, known]
  | some names => simp [check, known]

theorem check_world_mono
    (checked : check declarations environment world code = true)
    (included : world ⊆ larger) :
    check declarations environment larger code = true := by
  obtain ⟨names, known, contained⟩ := check_iff_bound.mp checked
  exact check_iff_bound.mpr ⟨names, known, fun _ member => included (contained member)⟩

theorem check_transport
    (checked : check declarations environment world code = true) :
    check declarations (snapshot resources environment)
      (world.map (ResourceName.instantiate resources)) (code.instantiate resources) = true := by
  obtain ⟨names, known, contained⟩ := check_iff_bound.mp checked
  apply check_iff_bound.mpr
  refine ⟨names.map (ResourceName.instantiate resources), ?_, ?_⟩
  · change DeclarationTemplates.infer declarations (fun name => mapBound resources (environment name))
      (code.instantiate resources) = _
    rw [DeclarationTemplates.infer_instantiate, known]
    rfl
  · intro name member
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨source, contained present, rfl⟩

theorem available_iff_subset (names : List ResourceName) :
    TemplateSupport.available world names = true ↔ names ⊆ world.map ResourceName.activation := by
  induction names with
  | nil => simp [TemplateSupport.available]
  | cons name rest ih => cases name with
      | bound name => simp [TemplateSupport.available, List.cons_subset, List.mem_map]
      | activation identity => simp [TemplateSupport.available, List.cons_subset, List.mem_map, ih]

theorem runtime_world_check (code : Code) :
    check declarations (runtimeEnv environment) (world.map ResourceName.activation) code =
      DeclarationTemplates.check declarations environment world code := by
  apply Bool.eq_iff_iff.mpr
  unfold check DeclarationTemplates.check
  cases known : DeclarationTemplates.infer declarations (runtimeEnv environment) code with
  | none => rfl
  | some names => simpa using (available_iff_subset names (world := world)).symm

theorem realized_world_map (realized : ListRealizes (NameRealizes resources) source target) :
    source.map (ResourceName.instantiate resources) = target.map ResourceName.activation :=
  list_instantiation_realizes (fun _ _ checked => name_instantiation_realizes checked) realized

/-- Equality relates support metadata. It does not assert that an actual
    lexical value inhabits that bound or that a listed resource is live. -/
theorem realized_check
    (checked : check declarations sourceEnvironment sourceWorld code = true)
    (world : ListRealizes (NameRealizes resources) sourceWorld targetWorld)
    (environment : snapshot resources sourceEnvironment = runtimeEnv targetEnvironment) :
    DeclarationTemplates.check declarations targetEnvironment targetWorld (code.instantiate resources) = true := by
  have transported := check_transport (resources := resources) checked
  rw [environment, realized_world_map world, runtime_world_check] at transported
  exact transported

theorem realized_check_in_world
    (checked : check declarations sourceEnvironment sourceWorld code = true)
    (world : ListRealizes (NameRealizes resources) sourceWorld realizedWorld)
    (included : realizedWorld ⊆ targetWorld)
    (environment : snapshot resources sourceEnvironment = runtimeEnv targetEnvironment) :
    DeclarationTemplates.check declarations targetEnvironment targetWorld (code.instantiate resources) = true := by
  have transported := check_transport (resources := resources) checked
  rw [environment, realized_world_map world] at transported
  have weakened := check_world_mono transported (List.map_subset _ included)
  rw [runtime_world_check] at weakened
  exact weakened

theorem snapshot_binding (initializer : Code) :
    snapshot resources (bindSupport environment name (DeclarationTemplates.infer declarations environment initializer)) =
      bindSupport (snapshot resources environment) name
        (DeclarationTemplates.infer declarations (snapshot resources environment) (initializer.instantiate resources)) := by
  funext other
  by_cases same : other = name
  · simp only [snapshot, bindSupport, if_pos same]
    exact (DeclarationTemplates.infer_instantiate initializer environment resources).symm
  · simp only [snapshot, bindSupport, if_neg same]

theorem snapshot_runtime_stable (resources : Instantiation.Environment) :
    snapshot resources (runtimeEnv environment) = runtimeEnv environment := by
  funext name
  exact TemplateSupport.map_lift _

theorem realized_snapshot_stable
    (realized : snapshot earlier sourceEnvironment = runtimeEnv targetEnvironment)
    (later : Instantiation.Environment) :
    snapshot later (snapshot earlier sourceEnvironment) = snapshot earlier sourceEnvironment := by
  rw [realized, snapshot_runtime_stable]

theorem masked_binder_missing (resources : Instantiation.Environment) (binder : Nat) :
    resources.mask binder binder = none := by simp [Environment.mask]

/-- The constructor transports the actual resource declaration. Its body
    uses the masked environment; captured outer support must already have
    been snapshotted before that lexical shadowing boundary. -/
theorem symbolic_entry_certificate
    (checked : check declarations sourceEnvironment sourceWorld body = true)
    (world : ListRealizes (NameRealizes (resources.mask binder)) sourceWorld targetWorld)
    (environment : snapshot (resources.mask binder) sourceEnvironment = runtimeEnv targetEnvironment)
    (closed : ((Code.resource binder (.integer payload) body).instantiate resources).ResourceClosed)
    (fresh : identity ∉ targetWorld) :
    RawStep ⟨(Code.resource binder (.integer payload) body).instantiate resources, scope, tail⟩
      ⟨(body.instantiate (resources.mask binder)).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
    OperationReturns.AllocationReturn (signature declarations) targetEnvironment [.resource identity]
      ⟨(body.instantiate (resources.mask binder)).instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ :=
  DeclarationTemplates.checked_source_entry (realized_check checked world environment) closed fresh

theorem symbolic_resource_entry_progress
    (valid : ScopedPortJoint.Valid (signature declarations) policy registry ambient
      ⟨⟨⟨(Code.resource binder (.integer payload) body).instantiate resources, scope, tail⟩,
        issued, completed⟩, activations⟩ result outgoing)
    (templateChecked : check declarations sourceEnvironment sourceWorld body = true)
    (world : ListRealizes (NameRealizes (resources.mask binder)) sourceWorld realizedWorld)
    (included : realizedWorld ⊆ ScopedTyping.resourceWorld issued)
    (environment : snapshot (resources.mask binder) sourceEnvironment = runtimeEnv targetEnvironment)
    (checked : OperationReturns.ConfigurationChecked (signature declarations) targetEnvironment
      ⟨(Code.resource binder (.integer payload) body).instantiate resources, scope, tail⟩) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨(Code.resource binder (.integer payload) body).instantiate resources, scope, tail⟩,
        issued, completed⟩, activations⟩ after ∧
      ScopedPortJoint.Valid (signature declarations) policy registry ambient after result outgoing ∧
      OperationReturns.ConfigurationChecked (signature declarations) targetEnvironment after.execution.configuration :=
  DeclarationTemplates.checked_resource_entry_progress valid
    (realized_check_in_world templateChecked world included environment) checked

namespace Examples

def declarations : DeclarationRegistry := fun _ => none
def outerOpening : Instantiation.Environment := Instantiation.Environment.empty.bind 4 8
def innerOpening : Instantiation.Environment := Instantiation.Environment.empty.bind 4 9
def unresolved : SupportEnv := fun name => if name = 3 then some [.bound 4] else none
def saved : SupportEnv := snapshot outerOpening unresolved
def runtime : ResultSummaries.Environment := fun name => if name = 3 then .resource 8 else .unknown

def aliasBody : Code := .lambda 0 (.bind 1 (.variable 3) (.integer 42))
def directBody : Code := .lambda 0 (.bind 1 (.resourceRef (.bound 4)) (.integer 42))

theorem saved_alias_records_outer : saved 3 = some [.activation 8] := rfl

theorem saved_environment_realized : saved = runtimeEnv runtime := by
  funext name
  by_cases same : name = 3 <;> simp [saved, snapshot, unresolved, runtimeEnv, runtime,
    ResultSummaries.Summary.support, lift, mapBound,
    same, ResourceName.instantiate, outerOpening, Environment.bind]

theorem saved_alias_stable_under_shadowing : snapshot innerOpening saved = saved :=
  realized_snapshot_stable saved_environment_realized innerOpening

theorem snapshot_unknown_stays_unknown (resources : Instantiation.Environment) :
    snapshot resources unresolved 7 = none := rfl

/-- Bare symbolic membership cannot distinguish these terms when the old
    alias still uses the same numeral as the newly shadowing binder. -/
theorem unsnapshotted_membership_conflates_scopes :
    check declarations unresolved [.bound 4] aliasBody = true ∧
    check declarations unresolved [.bound 4] directBody = true := ⟨rfl, rfl⟩

theorem masked_shadow_has_no_realization (identity : Nat) :
    ¬ NameRealizes (outerOpening.mask 4) (.bound 4) identity := by
  intro realized
  cases realized with
  | bound known => simp [Environment.mask] at known

theorem distinct_acquisitions_cannot_share_one_name
    (resources : Instantiation.Environment)
    (outer : NameRealizes resources (.bound 4) 8) :
    ¬ NameRealizes resources (.bound 4) 9 := by
  intro inner
  have impossible : (8 : Nat) = 9 := name_realization_unique outer inner
  contradiction

theorem saved_alias_passes_inner_reference_fails :
    check declarations saved [.activation 8] aliasBody = true ∧
    check declarations saved [.activation 8] directBody = false := ⟨rfl, rfl⟩

theorem masked_saved_environment : snapshot (outerOpening.mask 4) saved = runtimeEnv runtime := by
  rw [saved_environment_realized, snapshot_runtime_stable]

theorem alias_template_runtime_check :
    DeclarationTemplates.check declarations runtime [8]
      (aliasBody.instantiate (outerOpening.mask 4)) = true :=
  realized_check saved_alias_passes_inner_reference_fails.1
    (.cons .activation .nil) masked_saved_environment

theorem inner_opening_keeps_saved_outer_identity :
    (directBody.instantiate (outerOpening.mask 4)).instantiate innerOpening =
      .lambda 0 (.bind 1 (.resourceRef (.activation 9)) (.integer 42)) ∧
    snapshot innerOpening saved 3 = some [.activation 8] := ⟨rfl, rfl⟩

/-- Initializer lookup precedes introduction of the resource binder. -/
theorem initializer_uses_outer_body_masks_it :
    (Code.resource 4 (.resourceRef (.bound 4)) directBody).instantiate outerOpening =
      .resource 4 (.resourceRef (.activation 8)) directBody := rfl

/-- Distinct names may denote the same outer acquisition. Opening need not
    be injective, and support lists preserve this aliasing. -/
theorem noninjective_outer_aliases :
    ListRealizes (NameRealizes ((Environment.empty.bind 5 8).bind 6 8))
      [.bound 5, .bound 6] [8, 8] ∧
    [.bound 5, .bound 6].map (ResourceName.instantiate ((Environment.empty.bind 5 8).bind 6 8)) =
      [.activation 8, .activation 8] :=
  ⟨.cons (.bound rfl) (.cons (.bound rfl) .nil), rfl⟩

/-- This certificate constructs entry only. It assumes no independent proof
    that the outer identity is live or that the remaining stack is valid. -/
theorem alias_entry_certificate :
    RawStep ⟨(Code.resource 4 (.integer 99) aliasBody).instantiate outerOpening, scope, tail⟩
      ⟨(aliasBody.instantiate (outerOpening.mask 4)).instantiate innerOpening, scope,
        .push (.cell 9 99 scope answer) tail⟩ [.resource 9] [] ∧
    OperationReturns.AllocationReturn (signature declarations) runtime [.resource 9]
      ⟨(aliasBody.instantiate (outerOpening.mask 4)).instantiate innerOpening, scope,
        .push (.cell 9 99 scope answer) tail⟩ :=
  symbolic_entry_certificate saved_alias_passes_inner_reference_fails.1
    (.cons .activation .nil) masked_saved_environment rfl (by decide)

/-- The actual replacement value is checked against the snapshotted bound;
    support-environment equality alone is not that value certificate. -/
theorem actual_outer_alias_replacement :
    TemplateSubstitution.BindingsChecked runtime [(3, ResultSummaries.Examples.retainingConstant 8)] ∧
    DeclarationTemplates.check declarations runtime [8]
      (aliasBody.subst 3 (ResultSummaries.Examples.retainingConstant 8)) = true := by
  have binding : TemplateSubstitution.BindingsChecked runtime [(3, ResultSummaries.Examples.retainingConstant 8)] :=
    TemplateSubstitution.Examples.outer_function_checked
  refine ⟨binding, ?_⟩
  exact DeclarationSubstitution.checked_replacements_preserve_check
    (declarations := declarations) (world := [8]) (body := aliasBody) (by rfl)
    (binder := 4) (payload := 99) rfl binding

theorem aliased_world_checks_in_larger_issued_world :
    DeclarationTemplates.check declarations (fun _ => .unknown) [8, 12]
      ((Code.pair (.resourceRef (.bound 5)) (.resourceRef (.bound 6))).instantiate
        ((Environment.empty.bind 5 8).bind 6 8)) = true := by
  apply realized_check_in_world (sourceEnvironment := fun _ => none)
    (sourceWorld := [.bound 5, .bound 6]) (realizedWorld := [8, 8])
  · rfl
  · exact noninjective_outer_aliases.1
  · intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst name
    exact List.mem_cons_self
  · rfl

theorem actual_outer_alias_bind_then_inner_entry :
    RawStep ⟨.bind 3 (ResultSummaries.Examples.retainingConstant 8)
        (.resource 4 (.integer 99) aliasBody), scope, tail⟩
      ⟨.resource 4 (.integer 99) (aliasBody.subst 3 (ResultSummaries.Examples.retainingConstant 8)), scope, tail⟩ [] [] ∧
    RawStep ⟨.resource 4 (.integer 99) (aliasBody.subst 3 (ResultSummaries.Examples.retainingConstant 8)), scope, tail⟩
      ⟨(aliasBody.subst 3 (ResultSummaries.Examples.retainingConstant 8)).instantiate innerOpening, scope,
        .push (.cell 9 99 scope answer) tail⟩ [.resource 9] [] ∧
    OperationReturns.AllocationReturn (signature declarations) runtime [.resource 9]
      ⟨(aliasBody.subst 3 (ResultSummaries.Examples.retainingConstant 8)).instantiate innerOpening, scope,
        .push (.cell 9 99 scope answer) tail⟩ := by
  have binding := actual_outer_alias_replacement.1
  cases binding with
  | cons closed bound rest =>
      apply DeclarationSubstitution.bind_then_entry (declarations := declarations) (environment := runtime)
        (name := 3) (body := aliasBody) (binder := 4) (payload := 99) (identity := 9)
        (world := [8]) (by rfl) rfl closed
        ((DeclarationSubstitution.closed_value_bound_iff closed).mpr bound)
      · simp [ClosedExcept, aliasBody, Code.dependencies, Syntax.without]
      · decide

end Examples

end Ash.OneShot.SymbolicTemplates

#print axioms Ash.OneShot.SymbolicTemplates.check_iff_bound
#print axioms Ash.OneShot.SymbolicTemplates.check_world_mono
#print axioms Ash.OneShot.SymbolicTemplates.check_transport
#print axioms Ash.OneShot.SymbolicTemplates.available_iff_subset
#print axioms Ash.OneShot.SymbolicTemplates.runtime_world_check
#print axioms Ash.OneShot.SymbolicTemplates.realized_world_map
#print axioms Ash.OneShot.SymbolicTemplates.realized_check
#print axioms Ash.OneShot.SymbolicTemplates.realized_check_in_world
#print axioms Ash.OneShot.SymbolicTemplates.snapshot_binding
#print axioms Ash.OneShot.SymbolicTemplates.snapshot_runtime_stable
#print axioms Ash.OneShot.SymbolicTemplates.realized_snapshot_stable
#print axioms Ash.OneShot.SymbolicTemplates.masked_binder_missing
#print axioms Ash.OneShot.SymbolicTemplates.symbolic_entry_certificate
#print axioms Ash.OneShot.SymbolicTemplates.symbolic_resource_entry_progress
#print axioms Ash.OneShot.SymbolicTemplates.Examples.saved_alias_records_outer
#print axioms Ash.OneShot.SymbolicTemplates.Examples.saved_environment_realized
#print axioms Ash.OneShot.SymbolicTemplates.Examples.saved_alias_stable_under_shadowing
#print axioms Ash.OneShot.SymbolicTemplates.Examples.snapshot_unknown_stays_unknown
#print axioms Ash.OneShot.SymbolicTemplates.Examples.unsnapshotted_membership_conflates_scopes
#print axioms Ash.OneShot.SymbolicTemplates.Examples.masked_shadow_has_no_realization
#print axioms Ash.OneShot.SymbolicTemplates.Examples.distinct_acquisitions_cannot_share_one_name
#print axioms Ash.OneShot.SymbolicTemplates.Examples.saved_alias_passes_inner_reference_fails
#print axioms Ash.OneShot.SymbolicTemplates.Examples.masked_saved_environment
#print axioms Ash.OneShot.SymbolicTemplates.Examples.alias_template_runtime_check
#print axioms Ash.OneShot.SymbolicTemplates.Examples.inner_opening_keeps_saved_outer_identity
#print axioms Ash.OneShot.SymbolicTemplates.Examples.initializer_uses_outer_body_masks_it
#print axioms Ash.OneShot.SymbolicTemplates.Examples.noninjective_outer_aliases
#print axioms Ash.OneShot.SymbolicTemplates.Examples.alias_entry_certificate
#print axioms Ash.OneShot.SymbolicTemplates.Examples.actual_outer_alias_replacement
#print axioms Ash.OneShot.SymbolicTemplates.Examples.aliased_world_checks_in_larger_issued_world
#print axioms Ash.OneShot.SymbolicTemplates.Examples.actual_outer_alias_bind_then_inner_entry
