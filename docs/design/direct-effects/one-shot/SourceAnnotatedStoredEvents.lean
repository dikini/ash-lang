import SourceAnnotatedStoredExactControl
import SourceAnnotatedStoredCheckedEntries
import SourceAnnotatedStoredExecutionFocus
import SourceAnnotatedStoredExecutionResumption
import SourceAnnotatedStoredExecutionDisposal
import SourceAnnotatedStoredExecutionCapture
import SourceAnnotatedStoredBoundCapture
import SourceAnnotatedExecutionEvents

/-! The existing operational events preserve joint runtime source and the actual
stored packet stack under the current recipe declaration policy. Events contain
no intermediate runtime invariants. A second theorem preserves admitted bound
snapshots and stored declarations for every non-capture event under generic
policies. The inherited-capture route is joined to those cases below; admission
of the bounded-capture route remains separate. -/
namespace Ash.OneShot.SourceAnnotatedStoredEvents
open SourceAnnotatedExecutionEvents (Step Steps)
open SourceAnnotatedExecution (AtPackets)
open SourceAnnotatedRuntime (NamedState)
open SourceScheduledSavedPlans (Saved)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingStoredBounds (StackBounds)
open ScopedExecution (NamedAccessStep)

/-- Every actual event constructs its successor joint source and proof registry.
Only the initial source invariant is supplied. -/
theorem step_preserves {output : SourcePlannedTyping.Value}
    {before after : NamedState} {families : SourceDependencyFrames.Families}
    {stored : StackBounds families before.execution.configuration.stack}
    {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints receiving} {forest : Forest hints}
    (event : SourceAnnotatedExecutionEvents.Step operations.erase.erase.ports output.erase.erase.port before after)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before plan forest output demand row bound stored) :
    NamedAccessStep [] before.erase after.erase ∧
    ∃ nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved,
    ∃ nextDependencies, ∃ nextPlan : SourceDeclarationPlans.Plan nextDependencies,
    ∃ nextStored : StackBounds nextFamilies after.execution.configuration.stack, ∃ nextDemand nextRow,
      AtPackets operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after nextPlan saved.forest output nextDemand nextRow bound nextStored ∧ nextRow ⊆ row := by
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued) :=
    ⟨_, plan, .absent, _, _, forest, .absent forest⟩
  cases event with
  | discard resolved built fresh =>
      obtain ⟨remaining, nextSnapshot, step, next, _, _⟩ := run.discard_at_snapshot snapshot resolved built fresh
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, nextSnapshot.forest⟩, _, nextSnapshot.plan, _, remaining, _, next, List.Subset.refl _⟩
  | readCell selected =>
      obtain ⟨nextStored, nextRow, step, next, included, _⟩ := run.read_step_snapshot snapshot selected
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, forest⟩, _, .pure, nextStored, _, nextRow, next, included.subset⟩
  | writeCell selected =>
      obtain ⟨nextStored, nextRow, step, next, included, _⟩ := run.write_step_snapshot snapshot selected
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, forest⟩, _, .pure, nextStored, _, nextRow, next, included.subset⟩
  | capture cut isValue selected ports fresh =>
      obtain ⟨_, _, _, offered, _, found⟩ := run.atPlan.run.selected_clause cut
      obtain ⟨contract, record, captured, waiting, actual, nextDemand, nextRow, annotation,
        step, ⟨nextDependencies, nextPlan, nextStored, packetsSame, next, _⟩,
        balance, included, owners, shape, argument, known⟩ :=
        run.capture_preserves_retaining SourceAnnotatedAllocationData.noClauseEvidence cut isValue selected found fresh (by
          intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting plannedCut family bodies chosen
          trivial)
      have portKnown := CoherentSourceTypes.port_lookup
        (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known))
      have inputSame := (Prod.mk.inj (Option.some.inj (portKnown.symm.trans ports))).2
      rw [inputSame] at shape
      subst actual
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, _⟩, _, nextPlan, nextStored, nextDemand, nextRow, next, included⟩
  | ordinary reduction =>
      obtain ⟨nextSnapshot, remaining, nextRow, step, next, _, included, _⟩ := run.ordinary_step_snapshot snapshot reduction
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, nextSnapshot.forest⟩, _, nextSnapshot.plan, _, remaining, nextRow, next, included.subset⟩
  | returned transition =>
      obtain ⟨nextStored, remaining, nextSnapshot, step, next, _, _, _⟩ := run.return_step_snapshot snapshot transition
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, nextSnapshot.forest⟩, _, nextSnapshot.plan, nextStored, remaining, _, next, List.Subset.refl _⟩
  | resume resolved isValue =>
      obtain ⟨remaining, nextSnapshot, step, next, _, _⟩ := run.resume_preserves_snapshot snapshot resolved isValue
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, nextSnapshot.forest⟩, _, nextSnapshot.plan, _, remaining, _, next, List.Subset.refl _⟩
  | focus position ports =>
      obtain ⟨nextSnapshot, step, next, _⟩ := run.focus_snapshot snapshot position ports
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, nextSnapshot.forest⟩, _, nextSnapshot.plan, _, _, _, next, List.Subset.refl _⟩
  | resource fresh ports =>
      obtain ⟨nextSnapshot, nextRow, step, next, included, _⟩ := run.resource_entry_snapshot snapshot fresh ports
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, nextSnapshot.forest⟩, _, nextSnapshot.plan, _, _, nextRow, next, included.subset⟩
  | handler fresh ports =>
      obtain ⟨table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, packet, nextStored, step, next, _, _, _⟩ := run.handler_entry_snapshot snapshot fresh ports
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, nextSnapshot.forest⟩, _, nextSnapshot.plan, nextStored, _, _, next, List.Subset.refl _⟩
  | cleanup fresh ports =>
      obtain ⟨nextSnapshot, step, next, _⟩ := run.cleanup_entry_snapshot snapshot fresh ports
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, nextSnapshot.forest⟩, _, nextSnapshot.plan, _, _, _, next, List.Subset.refl _⟩

end Ash.OneShot.SourceAnnotatedStoredEvents

#print axioms Ash.OneShot.SourceAnnotatedStoredEvents.step_preserves

namespace Ash.OneShot.SourceAnnotatedStoredEvents
open SourceAnnotatedExecution (AtPackets)
open SourceAnnotatedRuntime (NamedState)
open SourceConsumingStoredBounds (StackBounds)
open SourceBoundSnapshots (Snapshot)
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]

/-- Every event that creates no continuation ticket preserves admission of its
exact successor snapshot and stored declarations. The policy transport premise
is declaration-signature invariance; no successor admission is assumed. Capture
creates a fresh ticket and is the separate remaining case. -/
theorem noncapture_preserves_admission
    (transport : ∀ {before after families required}
      {first : SourceDeclarationPlans.ClausePlans before families}
      {second : SourceDeclarationPlans.ClausePlans after families},
      nested.accepts required first →
      SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
      nested.accepts required second)
    {output : SourcePlannedTyping.Value} {before after : NamedState}
    {stored : StackBounds families before.execution.configuration.stack}
    (event : SourceAnnotatedExecutionEvents.Step operations.erase.erase.ports output.erase.erase.port before after)
    (noNewTickets : RecursiveCompletion.retiredTickets after.execution.issued =
      RecursiveCompletion.retiredTickets before.execution.issued)
    (snapshot : Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (snapshotAdmitted : snapshot.Admitted)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld before.execution.issued) required)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound stored evidence) :
    ScopedExecution.NamedAccessStep [] before.erase after.erase ∧
    ∃ nextTables nextFamilies nextRequired,
    ∃ nextWorld, ∃ nextSnapshot : Snapshot nextWorld,
    ∃ nextStored : StackBounds nextFamilies after.execution.configuration.stack,
    ∃ nextDemand nextRow,
      AtPackets operations declarations policy contracts registry nextTables nextFamilies nextRequired annotations
        after nextSnapshot.plan nextSnapshot.forest output nextDemand nextRow bound nextStored evidence ∧
      nextRow ⊆ row ∧ nextSnapshot.Admitted ∧
      nextStored.Admitted nextWorld nextRequired ∧
      nextWorld = ScopedTyping.resourceWorld after.execution.issued := by
  cases event
  case capture =>
    have impossible := congrArg List.length noNewTickets
    simp [SourceAnnotatedRuntime.advanceState, RecursiveCompletion.retiredTickets, List.filterMap_append] at impossible
  case discard resolved built fresh =>
    obtain ⟨remaining, nextSnapshot, step, next, _, _, admitted, packets⟩ :=
      run.discard_at_snapshot_admitted snapshot snapshotAdmitted stored storedAdmitted resolved built fresh
    exact ⟨step, _, _, _, _, nextSnapshot, _, remaining, _, next, List.Subset.refl _, admitted, packets, by simp [SourceAnnotatedRuntime.advanceState, ScopedTyping.resourceWorld]⟩
  case readCell selected =>
    obtain ⟨nextStored, nextRow, step, next, included, moved⟩ := run.read_step_snapshot snapshot selected
    exact ⟨step, _, _, _, _, Snapshot.value snapshot.pending, nextStored, _, nextRow, next, included.subset,
      SourceBoundSnapshots.Snapshot.value_admitted snapshotAdmitted.2, moved.admitted storedAdmitted, by simp [SourceAnnotatedRuntime.advanceState]⟩
  case writeCell selected =>
    obtain ⟨nextStored, nextRow, step, next, included, moved⟩ := run.write_step_snapshot snapshot selected
    exact ⟨step, _, _, _, _, Snapshot.value snapshot.pending, nextStored, _, nextRow, next, included.subset,
      SourceBoundSnapshots.Snapshot.value_admitted snapshotAdmitted.2, moved.admitted storedAdmitted, by simp [SourceAnnotatedRuntime.advanceState]⟩
  case ordinary reduction =>
    obtain ⟨nextSnapshot, remaining, nextRow, step, next, _, included, moved⟩ := run.ordinary_step_snapshot snapshot reduction
    exact ⟨step, _, _, _, _, nextSnapshot, _, remaining, nextRow, next, included.subset,
      moved.admitted snapshotAdmitted, storedAdmitted, by simp [SourceAnnotatedRuntime.advanceState]⟩
  case returned transition =>
    obtain ⟨nextStored, remaining, nextSnapshot, step, next, _, moved, packets⟩ := run.return_step_snapshot snapshot transition
    exact ⟨step, _, _, _, _, nextSnapshot, nextStored, remaining, _, next, List.Subset.refl _,
      moved.admitted snapshotAdmitted, packets.admitted storedAdmitted, by simp [SourceAnnotatedRuntime.advanceState]⟩
  case resume resolved isValue =>
    obtain ⟨remaining, nextSnapshot, step, next, _, _, admitted, packets⟩ :=
      run.resume_preserves_snapshot_admitted snapshot snapshotAdmitted stored storedAdmitted resolved isValue
    exact ⟨step, _, _, _, _, nextSnapshot, _, remaining, _, next, List.Subset.refl _, admitted, packets, by simp [SourceAnnotatedRuntime.advanceState, ScopedTyping.resourceWorld]⟩
  case focus position ports =>
    obtain ⟨nextSnapshot, step, next, moved⟩ := run.focus_snapshot snapshot position ports
    exact ⟨step, _, _, _, _, nextSnapshot, _, _, _, next, List.Subset.refl _, moved.admitted snapshotAdmitted,
      StackBounds.Admitted.push .plain storedAdmitted, by simp [SourceAnnotatedRuntime.advanceState]⟩
  case resource fresh ports =>
    obtain ⟨nextSnapshot, nextRow, step, next, included, moved⟩ := run.resource_entry_snapshot snapshot fresh ports
    exact ⟨step, _, _, _, _, nextSnapshot, _, _, nextRow, next, included.subset, moved.admitted snapshotAdmitted,
      StackBounds.Admitted.push .cell (storedAdmitted.world_weaken (List.subset_append_left _ _)),
      by simp [SourceAnnotatedRuntime.advanceState, ScopedTyping.resourceWorld]⟩
  case handler fresh ports =>
    rename_i activations hint body stack issued completed handler
    obtain ⟨table, clauseFamilies, declarationRequirements, nextSnapshot, actualPlans, packet, nextStored,
      step, next, moved, origin, packetShape⟩ := run.handler_entry_snapshot snapshot fresh ports
    have packets := origin.admitted (requirements := required) transport snapshotAdmitted
    obtain ⟨freshStack, same⟩ := packetShape
    have storedNext : nextStored.Admitted (ScopedTyping.resourceWorld issued)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) := by
      rw [same]
      exact .push (.handler packets)
        (storedAdmitted.registries_congr (SourceScheduledHandlers.register_agrees freshStack)
          (SourceScheduledHandlers.register_agrees freshStack))
    exact ⟨step, _, _, _, _, nextSnapshot, nextStored, _, _, next, List.Subset.refl _, moved.admitted snapshotAdmitted, storedNext, by simp [SourceAnnotatedRuntime.advanceState]⟩
  case cleanup fresh ports =>
    obtain ⟨nextSnapshot, step, next, moved⟩ := run.cleanup_entry_snapshot snapshot fresh ports
    exact ⟨step, _, _, _, _, nextSnapshot, _, _, _, next, List.Subset.refl _, moved.admitted snapshotAdmitted,
      StackBounds.Admitted.push .armed storedAdmitted,
      by simp [SourceAnnotatedRuntime.advanceState, ScopedTyping.resourceWorld]⟩
end Ash.OneShot.SourceAnnotatedStoredEvents
#print axioms Ash.OneShot.SourceAnnotatedStoredEvents.noncapture_preserves_admission

namespace Ash.OneShot.SourceAnnotatedStoredEvents
open SourceAnnotatedExecution (AtPackets)
open SourceAnnotatedRuntime (NamedState)
open SourceConsumingStoredBounds (StackBounds HandlerBounds)
open SourceBoundSnapshots (Snapshot)

/-- Restrict only the packet for the current requested effect. Unrelated
installed packets may remain bounded. This is a finite route lookup, not a
successor-source or future-execution premise. -/
def inheritedRequest (code : SourceAnnotatedCode.Term)
    (stored : StackBounds families stack) : Prop :=
  ∀ hint requested operation operand,
    code = .perform hint (Instantiation.freezeEffect requested) operation operand →
    ∀ handler (packet : HandlerBounds families handler),
      stored.handlerAt requested = some ⟨handler, packet⟩ → packet.admission = .inherited

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  [SourceStructuralHandlerEntry.DeclarationRetention admission evidence []]

/-- Join inherited capture to the ten non-capture admission cases for the
actual annotated event target. The route check is on this event's selected
packet; this theorem does not admit the separate bounded-capture route. -/
theorem step_preserves_inherited_admission
    (admitRecipe : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts [] required plans)
    (certifyRecipe : ∀ {world clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) [] world plans)
    (transport : ∀ {before after families required}
      {first : SourceDeclarationPlans.ClausePlans before families}
      {second : SourceDeclarationPlans.ClausePlans after families},
      nested.accepts required first →
      SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
      nested.accepts required second)
    {output : SourcePlannedTyping.Value} {before after : NamedState}
    {stored : StackBounds families before.execution.configuration.stack}
    (event : SourceAnnotatedExecutionEvents.Step operations.erase.erase.ports output.erase.erase.port before after)
    (route : inheritedRequest before.execution.configuration.expression stored)
    (snapshot : Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (snapshotAdmitted : snapshot.Admitted)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld before.execution.issued) required)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound stored evidence) :
    ScopedExecution.NamedAccessStep [] before.erase after.erase ∧
    ∃ nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations,
    ∃ nextWorld, ∃ nextSnapshot : Snapshot nextWorld,
    ∃ nextStored : StackBounds nextFamilies after.execution.configuration.stack,
    ∃ nextDemand nextRow,
      AtPackets operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after nextSnapshot.plan nextSnapshot.forest output nextDemand nextRow bound nextStored evidence ∧
      nextRow ⊆ row ∧ nextSnapshot.Admitted ∧
      nextStored.Admitted nextWorld nextRequired ∧
      nextWorld = ScopedTyping.resourceWorld after.execution.issued := by
  by_cases unchanged : RecursiveCompletion.retiredTickets after.execution.issued =
      RecursiveCompletion.retiredTickets before.execution.issued
  ·
    obtain ⟨step, nextTables, nextFamilies, nextRequired, nextWorld, nextSnapshot, nextStored,
      nextDemand, nextRow, next, included, admitted, packets, worldSame⟩ :=
      noncapture_preserves_admission transport event unchanged snapshot snapshotAdmitted storedAdmitted run
    exact ⟨step, contracts, registry, nextTables, nextFamilies, nextRequired, annotations,
      nextWorld, nextSnapshot, nextStored, nextDemand, nextRow, next, included, admitted, packets, worldSame⟩
  cases event
  case capture cut isValue selected ports fresh =>
    rename_i requested operation parameter binder argumentPort inputPort issued owner hint scope completed activations
      whole capture tail handler code operand
    obtain ⟨packet, packetAt⟩ := stored.handlerAt_cut cut
    have inherited := route _ _ _ _ rfl _ packet packetAt
    have offeredAt : ∃ offered, ProtectionContracts.lookup operation (tables handler.erase) = some offered := by
      obtain ⟨actions, _, _, source, _⟩ := run.actions
      cases source with
      | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
          capScope, tailScope, annotation, frame, saved, waiting, rest⟩ :=
          SourceDependencyFrames.capture_segments cut.erase pending.forget.erase.source.source.erase
        cases frame with
        | handler scope annotation clauses coverage unique declarations capabilities modes =>
          obtain ⟨offered, found, _⟩ := SourceTemplates.selected_clause_mode selected.erase modes
          exact ⟨offered, found⟩
    obtain ⟨offered, found⟩ := offeredAt
    obtain ⟨contract, record, captured, actual, nextDemand, nextRow, nextSnapshot, nextStored,
      _, step, next, _, included, _, _, admitted, packets, _, shape, argument, known⟩ :=
      run.capture_recipe_snapshot_admitted_with admitRecipe certifyRecipe snapshot snapshotAdmitted
        stored storedAdmitted packet packetAt inherited cut isValue selected found fresh
    have portKnown := CoherentSourceTypes.port_lookup
      (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known))
    have inputSame := (Prod.mk.inj (Option.some.inj (portKnown.symm.trans ports))).2
    rw [inputSame] at shape
    subst actual
    exact ⟨step, _, _, _, _, _, _, _, nextSnapshot, nextStored, nextDemand, nextRow,
      next, included, admitted, packets, by simp [SourceAnnotatedRuntime.advanceState, ScopedTyping.resourceWorld]⟩
  all_goals exact False.elim (unchanged (by
    simp [SourceAnnotatedRuntime.advanceState, RecursiveCompletion.retiredTickets, List.filterMap_append]))

end Ash.OneShot.SourceAnnotatedStoredEvents

#print axioms Ash.OneShot.SourceAnnotatedStoredEvents.step_preserves_inherited_admission
