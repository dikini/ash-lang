import SourceScheduledCells

/-! The scheduled source shares the existing runtime registry, access, ledger,
completion and usage invariants. Retained runtime disposal certificates derive
the typed-plan interface used by scheduled source preservation. -/
namespace Ash.OneShot.SourceScheduledExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value Environment)
open SourcePlannedSources (Expression)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Annotations Saved)

section

variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

structure Run [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (declarations : Instantiation.DeclarationRegistry)
    (policy : Syntax.TicketPolicy) (contracts : Contracts) (registry : CoherentSourceTypes.Owners.Registry)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (annotations : Annotations) (state : NamedState)
    {receiving : SourceDependencyCapture.Scope} {hints : Hints receiving} (forest : Forest hints)
    (output : Value) (demand : List Nat) (row : Footprint) (resultBound : CallableContracts.Contract)
    (evidence : SourcePlannedFrames.DeclarationEvidence := SourcePlannedFrames.recipeEvidence) : Prop where
  coherent : contracts.erase.erase = registry.contracts
  current : DeclaredExecution.Valid operations.erase.erase declarations policy registry tables [] [] state output.erase.erase demand row resultBound
  annotationHistory : ∀ owner captured, annotations owner = some captured → Owner.ticket owner ∈ state.execution.issued
  actions : ∃ tickets,
    ConfigurationUsage policy tickets state.execution.configuration ∧
    UsageRegistryHistory tickets state.execution.issued ∧
    SourceScheduledState.State operations policy contracts tables families required tickets annotations
      (ScopedTyping.resourceWorld state.execution.issued) [] [] state.execution.configuration.scope
      state.execution.configuration.expression state.execution.configuration.stack forest output demand row evidence ∧
    DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld state.execution.issued)
      registry tickets state.execution.configuration.stack

theorem Run.erase [SourceScheduledChecks.DeclarationProjection admission certification]
    (run : Run operations declarations policy contracts registry tables families required annotations state forest output demand row resultBound evidence) :
    DeclaredConnectedSources.Run operations.erase.erase declarations policy registry tables state output.erase.erase demand row resultBound := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  exact ⟨run.current, actions, usage, history, run.coherent ▸ source.erase, retained⟩

/-- Evaluate the annotated requirements and check both the closed effect row
and literal resource support. This computes finite admission data only;
source typing and structural scheduling remain separate judgments. -/
def checkInitial (code : Code) (requirements : RecursiveRequirements.Requirements demand) : Bool :=
  match RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available []) requirements with
  | none => false
  | some row => checkFootprint [] row && decide (Syntax.resourceDependencies code.dependencies = [])

omit admission certification in
/-- With no outside interpretation, only an empty residual row is admitted. -/
theorem checkFootprint_empty_iff : checkFootprint [] row = true ↔ row = [] := by
  cases row <;> simp [checkFootprint, checkRequest]

omit admission certification in
/-- The executable check supplies an empty initial row and resource support.
Reuse the established evaluator soundness/completeness theorem. -/
theorem checkInitial_iff : checkInitial code requirements = true ↔
    RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements [] ∧
    Syntax.resourceDependencies code.dependencies = [] := by
  rw [RecursiveRequirements.checked_iff]
  cases evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available []) requirements with
  | none => simp [checkInitial, evaluated]
  | some actual => simp [checkInitial, evaluated, checkFootprint_empty_iff]

omit admission certification in
/-- Combining the finite checks preserves their previous admission boundary;
no formerly admitted row or program is discarded by choosing the empty row. -/
theorem checkInitial_iff_previous : checkInitial code requirements = true ↔
    ∃ row, RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row ∧
      checkFootprint [] row = true ∧ Syntax.resourceDependencies code.dependencies = [] := by
  constructor
  · intro admitted
    obtain ⟨checked, support⟩ := checkInitial_iff.mp admitted
    exact ⟨[], checked, rfl, support⟩
  · rintro ⟨row, checked, accepted, support⟩
    have empty := checkFootprint_empty_iff.mp accepted
    subst row
    exact checkInitial_iff.mpr ⟨checked, support⟩

/-- One finite check supplies evaluation, effect-row acceptance and closed
resource support. Source typing, scheduling, completion and declaration
signature agreement are the remaining initial admission premises. -/
theorem initial_run {plan : SourceDeclarationPlans.Plan dependencies}
    (source : Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (contextual : SourceScheduledChecks.Local [] (fun _ => none) (OwnerPhaseTransitions.available []) [] plan .nil)
    (admitted : checkInitial code requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code resultBound)
    (signature : operations.erase.erase.ports = DeclarationResults.signature declarations) :
    demand = [] ∧ Run operations declarations policy (fun _ => none) (fun _ => none) tables families required (fun _ => none)
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ .nil output [] [] resultBound evidence := by
  obtain ⟨evaluated, supported⟩ := checkInitial_iff.mp admitted
  have accepted : checkFootprint [] [] = true := rfl
  have support : decide (Syntax.resourceDependencies code.dependencies = []) = true := by simpa using supported
  obtain ⟨empty, existing⟩ := DeclaredConnectedSources.initial_run
    (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase source))
    evaluated accepted result signature support (tables := tables)
  obtain ⟨actions, usage, history, oldSource, retained⟩ := existing.actions
  have permissions : Syntax.UsageExtension (fun _ => none) actions := by intro owner rights known; cases known
  have checked := SourceScheduledTransport.local_transport contextual (fun _ ready => ready) permissions
  exact ⟨empty, rfl, existing.current, (by intro owner captured known; cases known), actions, usage, history,
    empty ▸ SourceScheduledState.initial source empty checked evaluated accepted, retained⟩

/-- Reuse runtime assembly for a step that allocates no continuation. Its
scheduled successor uses the actual resource world and advanced action map. -/
theorem assemble_entry [SourceScheduledChecks.DeclarationProjection admission certification]
    (coherent : contracts.erase.erase = registry.contracts)
    (current : DeclaredExecution.Valid operations.erase.erase declarations policy registry tables [] [] before output.erase.erase demand row resultBound)
    (raw : RawStep before.execution.configuration after created discharged)
    (freshOwners : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup)
    (checks : AccessChecks before.execution.configuration [])
    (usage : ConfigurationUsage policy actions before.execution.configuration)
    (history : UsageRegistryHistory actions before.execution.issued)
    (annotationHistory : ∀ owner captured, annotations owner = some captured → Owner.ticket owner ∈ before.execution.issued)
    (retained : DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld before.execution.issued)
      registry actions before.execution.configuration.stack)
    (source : SourceScheduledState.State operations policy contracts nextTables nextFamilies nextRequired
      (ScopedActionUsage.advance actions after created) annotations (ScopedTyping.resourceWorld (before.execution.issued ++ created)) [] []
      after.scope after.expression after.stack forest output nextDemand nextRow evidence)
    (results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results
      (ScopedTyping.resourceWorld (before.execution.issued ++ created)) after resultBound)
    (update : registry.runtime.joint.usage = advanceUsageTickets policy registry.runtime.joint.usage after created)
    (noTickets : ∀ owner, Owner.ticket owner ∉ created) :
    Run operations declarations policy contracts registry nextTables nextFamilies nextRequired annotations
      (ScopedPortJoint.advanceState before after created discharged) forest output nextDemand nextRow resultBound evidence := by
  have existing := DeclaredConnectedSources.assemble_entry current raw freshOwners freshHandlers checks usage history
    retained (coherent ▸ source.erase) results update noTickets
  have usageChecks := usage_checks_from_allocation_and_access history freshOwners checks
  have extension := ScopedActionUsage.advance_extends (after := after) usageChecks.allocation
  have unique : (ownedTickets after.stack).Nodup := by
    cases source with
    | checked _ _ _ _ _ _ _ unique _ _ _ => exact unique
  have larger : ScopedTyping.resourceWorld before.execution.issued ⊆
      ScopedTyping.resourceWorld (before.execution.issued ++ created) := by
    rw [ScopedTyping.resource_world_append]
    exact List.subset_append_left _ _
  exact ⟨coherent, existing.current,
    (fun owner captured known => List.mem_append_left _ (annotationHistory owner captured known)),
    _, ScopedActionUsage.raw_step_preserves raw usageChecks usage,
    ScopedActionUsage.raw_step_preserves_history raw history, source,
    DeclaredClosingInvariant.raw_step_preserves_retained raw retained (fun _ _ known => known)
      extension larger (.none noTickets) unique⟩


end

/-- Retained disposal evidence supplies the actual plan's effect interface.
The theorem requires an actual access-checked step, not an extra PlanTyped
premise or a separately supplied successor check. -/
theorem Run.discard_preserves
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row resultBound)
    (step : NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after) :
    ∃ owner remaining, ∃ nextForest : Saved,
      Run operations declarations policy contracts registry tables families required annotations after nextForest.forest output remaining row resultBound ∧
      demand = owner :: remaining := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  cases step with
  | mk execution access => cases execution with
    | event after created discharged raw freshOwners freshHandlers =>
      have actual := raw
      cases raw with
      | focus plain focus tail => cases focus
      | plug plain value impossible scope tail => cases impossible.1
      | leaveHandler handler value impossible scope tail => cases impossible.1
      | leaveCell identity payload answer savedScope scope value impossible tail => cases impossible.1
      | startCleanup action saved impossible scope tail => cases impossible.1
      | leaveClause ticket answer value impossible scope caller tail => cases impossible.1
      | discard binder owner identity scope caller input answer front capture tail plan resolved built =>
        obtain ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ := usage
        obtain ⟨actualOwner, rights, actionKnown, actualResolved, _, permitted⟩ := ScopedActionUsage.discard_requires_action code
        cases Option.some.inj (actualResolved.symm.trans resolved)
        obtain ⟨record, savedRights, known, savedKnown, checked⟩ :=
          retained owner capture (RecursiveRecords.located_below front .here)
        have sameRights := Option.some.inj (actionKnown.symm.trans savedKnown)
        obtain ⟨certificate⟩ := checked (sameRights ▸ permitted)
        have samePlan := Option.some.inj (certificate.built.symm.trans built)
        have erasedKnown : contracts.erase.erase owner = some record.annotation := by
          rw [run.coherent]
          simp [CoherentSourceTypes.Owners.Registry.contracts, known]
        obtain ⟨annotated, annotatedKnown, annotatedSame⟩ := Option.map_eq_some_iff.mp erasedKnown
        obtain ⟨contract, contractKnown, contractSame⟩ := Option.map_eq_some_iff.mp annotatedKnown
        have combined := (congrArg SourceDependencyAnnotations.Contract.erase contractSame).trans annotatedSame
        have effectsSame := congrArg CoherentSourceTypes.Owners.Contract.closeEffects combined
        change contract.closeEffects = record.annotation.closeEffects at effectsSame
        have typed : ScopedPorts.PlanTyped operations.erase.erase.ports (ScopedTyping.resourceWorld issued) contract.closeEffects plan := by
          rw [effectsSame]
          exact samePlan ▸ certificate.typed
        obtain ⟨remaining, nextForest, _, successor, accounting, _, _⟩ :=
          SourceScheduledDisposal.discard_cut_preserves source contractKnown resolved built typed (closeId := identity)
        have results := (CompletionFrames.discard_step resolved built run.current.results (closeId := identity)).2
        have joined := assemble_entry run.coherent run.current actual freshOwners freshHandlers access
          ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ history run.annotationHistory retained
          (by simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld, ScopedActionUsage.advance] using successor)
          (by simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results) rfl (by simp)
        exact ⟨owner, remaining, nextForest, joined, accounting⟩

/-- The retained certificate supplies existence of an access-checked step;
scheduled preservation keeps the exact richer source for its successor. -/
theorem Run.discard_progress
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row resultBound) :
    ∃ after owner remaining, ∃ nextForest : Saved,
      NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Run operations declarations policy contracts registry tables families required annotations after nextForest.forest output remaining row resultBound ∧
      demand = owner :: remaining := by
  obtain ⟨after, _, _, step, _, _⟩ := DeclaredClosingInvariant.discard_progress run.erase.shared.prepared
  obtain ⟨owner, remaining, nextForest, successor, accounting⟩ := run.discard_preserves step
  exact ⟨after, owner, remaining, nextForest, step, successor, accounting⟩

end Ash.OneShot.SourceScheduledExecution

#print axioms Ash.OneShot.SourceScheduledExecution.Run.erase
#print axioms Ash.OneShot.SourceScheduledExecution.initial_run
#print axioms Ash.OneShot.SourceScheduledExecution.assemble_entry
#print axioms Ash.OneShot.SourceScheduledExecution.Run.discard_preserves
#print axioms Ash.OneShot.SourceScheduledExecution.Run.discard_progress

#print axioms Ash.OneShot.SourceScheduledExecution.checkInitial_iff

#print axioms Ash.OneShot.SourceScheduledExecution.checkFootprint_empty_iff

#print axioms Ash.OneShot.SourceScheduledExecution.checkInitial_iff_previous
