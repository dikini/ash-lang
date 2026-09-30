import SourceAnnotatedRuntimeDisposal
import SourceConsumingBoundDisposal

/-! Disposal preserves admitted source snapshots and the original caller's
handler packets on the exact successor selected by the stored certificate. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceConsumingStoredBounds (StackBounds)
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem AtPlan.discard_at_snapshot_admitted {front capture tail : SourceAnnotatedRuntime.Stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families (front.append (.live owner input answer capture caller tail)))
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound evidence)
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
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.close identity] [.ticket owner]) nextSnapshot.plan nextSnapshot.forest output remaining row resultBound evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Discarded owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧
      (stored.discard scope identity annotatedPlan).Admitted (ScopedTyping.resourceWorld issued) required := by
  obtain ⟨remaining, nextSnapshot, step, next, accounting, moved⟩ :=
    AtPlan.discard_at_snapshot snapshot run resolved builtAnnotated freshOwners
  exact ⟨remaining, nextSnapshot, step, next, accounting, moved, moved.admitted admitted,
    storedAdmitted.discard scope identity annotatedPlan⟩

theorem AtPlan.discard_preserves_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families stack)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound evidence)
    (step : NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack.erase⟩, issued, completed⟩, activations⟩ after) :
    ∃ successor : SourceAnnotatedRuntime.NamedState, ∃ owner remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ nextStored : StackBounds families successor.execution.configuration.stack,
      successor.erase = after ∧
      AtPlan operations declarations policy contracts registry tables families required annotations successor nextSnapshot.plan nextSnapshot.forest output remaining row resultBound evidence ∧
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
        AtPlan.discard_at_snapshot_admitted snapshot admitted stored storedAdmitted run resolved actualBuilt freshOwners
      refine ⟨_, owner, remaining, nextSnapshot, stored.discard scope identity annotatedPlan,
        ?_, next, accounting, moved, nextAdmitted, storedNext, ?_⟩
      · simp only [SourceAnnotatedRuntime.advanceState, SourceAnnotatedRuntime.NamedState.erase,
          SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
          SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase,
          SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedRuntime.closeControl_erase]
      · simp [SourceAnnotatedRuntime.advanceState, ScopedTyping.resourceWorld]

/-- Disposal progress uses the retained certificate's actual step, then
preserves the original annotations and installed packets through that step. -/
theorem AtPlan.discard_progress_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families stack)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row resultBound evidence) :
    ∃ after : SourceAnnotatedRuntime.NamedState, ∃ owner remaining,
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ nextStored : StackBounds families after.execution.configuration.stack,
      NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack.erase⟩, issued, completed⟩, activations⟩ after.erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations after
        nextSnapshot.plan nextSnapshot.forest output remaining row resultBound evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Discarded owner snapshot nextSnapshot ∧ nextSnapshot.Admitted ∧
      nextStored.Admitted (ScopedTyping.resourceWorld issued) required ∧
      ScopedTyping.resourceWorld after.execution.issued = ScopedTyping.resourceWorld issued := by
  obtain ⟨after, _, _, step, _, _⟩ := DeclaredClosingInvariant.discard_progress run.run.erase.erase.shared.prepared
  obtain ⟨successor, owner, remaining, nextSnapshot, nextStored, same, valid, accounting, moved,
    nextAdmitted, storedNext, sameWorld⟩ :=
    AtPlan.discard_preserves_snapshot_admitted snapshot admitted stored storedAdmitted run step
  exact ⟨successor, owner, remaining, nextSnapshot, nextStored, same ▸ step, valid, accounting, moved,
    nextAdmitted, storedNext, sameWorld⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.discard_at_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.discard_preserves_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.discard_progress_snapshot_admitted
