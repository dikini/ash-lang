import SourceAnnotatedExecutionResumption
import SourceConsumingBoundResumption

/-! One-shot resumption joins the original snapshot annotations, installed
packets and shared runtime on the same successor. Ownership and access proofs
are reused from the established execution theorem. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceConsumingStoredBounds (StackBounds)
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
variable {front capture tail : SourceAnnotatedRuntime.Stack}

theorem AtPlan.resume_preserves_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families (front.append (.live owner inputType answerType capture caller tail)))
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (resolved : scope.resolve binder = some owner) (isValue : value.erase.IsValue) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let after : SourceAnnotatedRuntime.Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨.resume hint binder value, scope,
        front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]) nextSnapshot.plan nextSnapshot.forest output remaining row bound evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Resumed owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧ stored.resume.Admitted (ScopedTyping.resourceWorld issued) required := by
  obtain ⟨remaining, nextSnapshot, step, next, accounting, moved⟩ :=
    AtPlan.resume_preserves_snapshot snapshot run resolved isValue
  exact ⟨remaining, nextSnapshot, step, next, accounting, moved, moved.admitted admitted, storedAdmitted.resume⟩

/-- Source usage locates the actual owner; no live-cut or successful future
check is an additional input to this progress result. -/
theorem AtPlan.resume_progress_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families stack)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : value.erase.IsValue) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ owner remaining,
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ nextStored : StackBounds families after.stack,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.resume hint binder value, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner])
        nextSnapshot.plan nextSnapshot.forest output remaining row bound evidence ∧
      demand = owner :: remaining ∧ SourceBoundSnapshots.Resumed owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧ nextStored.Admitted (ScopedTyping.resourceWorld issued) required := by
  obtain ⟨owner, front, capture, tail, input, answer, caller, resolved, stackSame⟩ := run.run.resume_location
  subst stack
  obtain ⟨remaining, nextSnapshot, step, next, accounting, moved, nextAdmitted, storedNext⟩ :=
    AtPlan.resume_preserves_snapshot_admitted snapshot admitted stored storedAdmitted run resolved isValue
  exact ⟨⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩,
    owner, remaining, nextSnapshot, stored.resume, step, next, accounting, moved, nextAdmitted, storedNext⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.resume_preserves_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.resume_progress_snapshot_admitted
