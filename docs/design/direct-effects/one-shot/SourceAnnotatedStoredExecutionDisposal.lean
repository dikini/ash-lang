import SourceAnnotatedStoredDisposal
import SourceAnnotatedStoredExecution
import SourceAnnotatedRuntimeDisposal

/-! Disposal retains the same packet/source data through the actual named
execution step. Existing retained certificates supply the typed closing plan. -/
namespace Ash.OneShot.SourceAnnotatedExecution

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledSavedPlans (Saved)

/-- The retained certificate is tied to the actual annotated capture, so every
supplied closing plan produces exactly its annotated closing control. -/
theorem AtPackets.discard_at_snapshot {front capture tail : SourceAnnotatedRuntime.Stack}
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families (front.append (.live owner input answer capture caller tail))}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored evidence)
    (resolved : scope.resolve binder = some owner)
    (builtAnnotated : SourceAnnotatedRuntime.makePlan capture = some annotatedPlan)
    (freshOwners : (issued ++ [Owner.close identity]).Nodup) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
          issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨.unit .unit, scope,
        (SourceAnnotatedRuntime.closeControl scope annotatedPlan).append
          (.push (.closing identity scope) (front.append (.spent owner answer caller tail)))⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.close identity] [.ticket owner]).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.close identity] [.ticket owner]) nextSnapshot.plan nextSnapshot.forest output remaining row resultBound (stored.discard scope identity annotatedPlan) evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Discarded owner snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨_, _, _, admitted, _, _⟩ := DeclaredClosingInvariant.discard_progress run.atPlan.run.erase.erase.shared.prepared
  have access : AccessChecks
      ⟨.discard binder, scope, (front.append (.live owner input answer capture caller tail)).erase⟩ [] := admitted.checks
  let plan := annotatedPlan.map SourceAnnotatedRuntime.CloseEntry.erase
  have built : makePlan capture.erase = some plan := by
    rw [SourceAnnotatedRuntime.makePlan_erase, builtAnnotated]
    rfl
  obtain ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ := usage
  obtain ⟨actualOwner, rights, actionKnown, actualResolved, _, permitted⟩ := ScopedActionUsage.discard_requires_action code
  cases Option.some.inj (actualResolved.symm.trans resolved)
  have located : SourceTemplates.CapturedIn owner capture.erase
      (front.erase.append (.live owner input answer capture.erase caller tail.erase)) :=
    RecursiveRecords.located_below front.erase .here
  obtain ⟨record, savedRights, known, savedKnown, checked⟩ :=
    retained owner capture.erase (by
      simpa only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using located)
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
  obtain ⟨restored, restoredStored, remaining, nextSnapshot, restoredSame, actual, successor, accounting, _, _, ⟨actualPlan, actualBuilt, exactRestored, packetsSame⟩, moved⟩ :=
    SourceAnnotatedStoredDisposal.discard_cut_preserves_snapshot snapshot source contractKnown resolved built typed (closeId := identity)
  cases Option.some.inj (actualBuilt.symm.trans builtAnnotated)
  subst restored
  cases eq_of_heq packetsSame
  let next : SourceAnnotatedRuntime.Configuration := ⟨.unit .unit, scope,
    (SourceAnnotatedRuntime.closeControl scope annotatedPlan).append
      (.push (.closing identity scope) (front.append (.spent owner answer caller tail)))⟩
  have nextSame : next.erase = ⟨.unit, scope, (closeControl scope plan).append
      (.push (.closing identity scope) (front.erase.append (.spent owner answer caller tail.erase)))⟩ := by
    simp only [next, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase, restoredSame]
  have actualRaw : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.discard hint binder, scope,
        front.append (.live owner input answer capture caller tail)⟩)
      next.erase [.close identity] [.ticket owner] := by
    simpa only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase, next] using actual
  have freshHandlers : (activations ++ enteredActivations
      (SourceAnnotatedRuntime.Configuration.erase ⟨.discard hint binder, scope,
        front.append (.live owner input answer capture caller tail)⟩) next.erase).Nodup := by
    simpa only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.NamedState.erase,
      SourceAnnotatedCode.Term.erase, enteredActivations, List.append_nil]
      using run.current.names.unique
  have previousResults := run.current.results
  simp only [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
    SourceAnnotatedCode.Term.erase, SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] at previousResults
  have results := (CompletionFrames.discard_step resolved built previousResults (closeId := identity)).2
  have joined := assemble_entry_atPackets (after := next) run.coherent run.current actualRaw freshOwners freshHandlers access
    ⟨currentDemand, pendingDemand, code, control, accessible, balance, unique⟩ history run.annotationHistory retained
    (by simpa [next, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      ScopedTyping.resource_world_append, ScopedTyping.resourceWorld, ScopedActionUsage.advance] using successor)
    (by simpa [nextSame, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results)
    (by rw [nextSame]; rfl) (by simp)
  exact ⟨remaining, nextSnapshot, ⟨.event _ _ _ _ actualRaw freshOwners freshHandlers, access⟩, joined, accounting, moved⟩

open SourceConsumingStoredBounds (StackBounds)
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem AtPackets.discard_at_snapshot_admitted {front capture tail : SourceAnnotatedRuntime.Stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families (front.append (.live owner input answer capture caller tail)))
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored evidence)
    (resolved : scope.resolve binder = some owner)
    (builtAnnotated : SourceAnnotatedRuntime.makePlan capture = some annotatedPlan)
    (freshOwners : (issued ++ [Owner.close identity]).Nodup) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
          issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨.unit .unit, scope,
        (SourceAnnotatedRuntime.closeControl scope annotatedPlan).append
          (.push (.closing identity scope) (front.append (.spent owner answer caller tail)))⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.close identity] [.ticket owner]).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.close identity] [.ticket owner]) nextSnapshot.plan nextSnapshot.forest output remaining row resultBound (stored.discard scope identity annotatedPlan) evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Discarded owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧
      (stored.discard scope identity annotatedPlan).Admitted (ScopedTyping.resourceWorld issued) required := by
  obtain ⟨remaining, nextSnapshot, step, next, accounting, moved⟩ :=
    AtPackets.discard_at_snapshot snapshot run resolved builtAnnotated freshOwners
  exact ⟨remaining, nextSnapshot, step, next, accounting, moved, moved.admitted admitted,
    storedAdmitted.discard scope identity annotatedPlan⟩

theorem AtPackets.discard_preserves_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families stack)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored evidence)
    (step : NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack.erase⟩, issued, completed⟩, activations⟩ after) :
    ∃ successor : SourceAnnotatedRuntime.NamedState, ∃ owner remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ nextStored : StackBounds families successor.execution.configuration.stack,
      successor.erase = after ∧
      AtPackets operations declarations policy contracts registry tables families required annotations successor nextSnapshot.plan nextSnapshot.forest output remaining row resultBound nextStored evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Discarded owner snapshot nextSnapshot ∧ nextSnapshot.Admitted ∧
      nextStored.Admitted (ScopedTyping.resourceWorld issued) required ∧
      ScopedTyping.resourceWorld successor.execution.issued = ScopedTyping.resourceWorld issued := by
  cases step with
  | mk execution access => cases execution with
    | event after created discharged raw freshOwners freshHandlers =>
      obtain ⟨owner, identity, caller, input, answer, front, capture, tail, plan,
        stackSame, resolved, built, afterSame, createdSame, dischargedSame⟩ :=
        SourceAnnotatedRuntime.raw_discard_shape raw
      subst stack
      subst after
      subst created
      subst discharged
      obtain ⟨annotatedPlan, actualBuilt, planSame⟩ := SourceAnnotatedRuntime.makePlan_of_raw capture built
      subst plan
      obtain ⟨remaining, nextSnapshot, _, next, accounting, moved, nextAdmitted, storedNext⟩ :=
        AtPackets.discard_at_snapshot_admitted snapshot admitted stored storedAdmitted run resolved actualBuilt freshOwners
      let successor := SourceAnnotatedRuntime.advanceState
        ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
          issued, completed⟩, activations⟩
        ⟨.unit .unit, scope, (SourceAnnotatedRuntime.closeControl scope annotatedPlan).append
          (.push (.closing identity scope) (front.append (.spent owner answer caller tail)))⟩
        [.close identity] [.ticket owner]
      refine ⟨successor, owner, remaining, nextSnapshot, stored.discard scope identity annotatedPlan,
        ?_, next, accounting, moved, nextAdmitted, storedNext, ?_⟩
      · simp only [successor, SourceAnnotatedRuntime.advanceState, SourceAnnotatedRuntime.NamedState.erase,
          SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
          SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase,
          SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedRuntime.closeControl_erase]
      · simp [successor, SourceAnnotatedRuntime.advanceState, ScopedTyping.resourceWorld]

/-- Disposal progress uses the retained certificate's actual step, then
preserves the original annotations and installed packets through that step. -/
theorem AtPackets.discard_progress_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families stack)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row resultBound stored evidence) :
    ∃ after : SourceAnnotatedRuntime.NamedState, ∃ owner remaining,
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ nextStored : StackBounds families after.execution.configuration.stack,
      NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack.erase⟩, issued, completed⟩, activations⟩ after.erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations after
        nextSnapshot.plan nextSnapshot.forest output remaining row resultBound nextStored evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Discarded owner snapshot nextSnapshot ∧ nextSnapshot.Admitted ∧
      nextStored.Admitted (ScopedTyping.resourceWorld issued) required ∧
      ScopedTyping.resourceWorld after.execution.issued = ScopedTyping.resourceWorld issued := by
  obtain ⟨after, _, _, step, _, _⟩ := DeclaredClosingInvariant.discard_progress run.atPlan.run.erase.erase.shared.prepared
  obtain ⟨successor, owner, remaining, nextSnapshot, nextStored, same, valid, accounting, moved,
    nextAdmitted, storedNext, sameWorld⟩ :=
    AtPackets.discard_preserves_snapshot_admitted snapshot admitted stored storedAdmitted run step
  exact ⟨successor, owner, remaining, nextSnapshot, nextStored, same ▸ step, valid, accounting, moved,
    nextAdmitted, storedNext, sameWorld⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.discard_at_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.discard_at_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.discard_preserves_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.discard_progress_snapshot_admitted
