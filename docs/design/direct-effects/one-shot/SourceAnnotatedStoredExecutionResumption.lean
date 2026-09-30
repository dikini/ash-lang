import SourceBoundRecords
import SourceAnnotatedStoredResumption
import SourceAnnotatedStoredExecution
import SourceAnnotatedExecutionResumption

/-! One-shot resumption restores the actual annotated capture under every
caller prefix. Existing runtime proofs supply completion and access checks. -/
namespace Ash.OneShot.SourceAnnotatedExecution

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution
open SourceScheduledSavedPlans (Saved)
variable {front capture tail : SourceAnnotatedRuntime.Stack}

/-- Resumption preserves the common runtime at every actual annotated live
cut and consumes the selected continuation owner exactly once. -/
theorem AtPackets.resume_preserves_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (resolved : scope.resolve binder = some owner) (isValue : value.erase.IsValue) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let after : SourceAnnotatedRuntime.Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨.resume hint binder value, scope,
        front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]) nextSnapshot.plan nextSnapshot.forest output remaining row bound stored.resume evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Resumed owner snapshot nextSnapshot ∧
      ∀ {Payload : SourceBoundSnapshots.RecordFamily.{0} (ScopedTyping.resourceWorld issued)}
        (records : snapshot.pending.Records Payload),
        ∃ nextRecords : nextSnapshot.pending.Records Payload,
          SourceBoundSnapshots.RecordResumption owner Payload records nextRecords := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  have previous := run.current
  simp only [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
    SourceAnnotatedCode.Term.erase, SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] at previous
  have closed := (ContinuationBounds.resume_operand_bound (environment := fun _ => .unknown)
    resolved (DeclaredReturnAdmission.ports previous.source) isValue).1
  obtain ⟨remaining, nextSnapshot, next, accounting, trace, moved⟩ := SourceAnnotatedStoredResumption.resume_cut_preserves_snapshot snapshot source resolved closed
  obtain ⟨runtimeRemaining, step, current, runtimeAccounting⟩ := DeclaredExecution.resume_preserves previous resolved isValue
  have raw : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩)
      (SourceAnnotatedRuntime.Configuration.erase ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩)
      [] [.ticket owner] := by
    simpa only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using
      RawStep.resume binder owner scope caller inputType answerType front.erase capture.erase tail.erase value.erase closed resolved
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using previous.ledger.2
  have joined := assemble_entry_atPackets run.coherent run.current raw freshOwners
    (by simpa only [ScopedPortJoint.advanceState, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using current.names.unique)
    (by simpa only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using step.checks)
    usage history run.annotationHistory retained
    (by simpa only [ScopedActionUsage.advance, List.append_nil] using next)
    (by simpa only [ScopedPortJoint.advanceState, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using current.results)
    rfl (by simp)
  refine ⟨remaining, nextSnapshot, ?_, joined, accounting, moved, fun records => moved.carry_records records⟩
  simpa only [SourceAnnotatedRuntime.advanceState, ScopedPortJoint.advanceState, SourceAnnotatedRuntime.NamedState.erase,
    SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
    SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using step

open SourceConsumingStoredBounds (StackBounds)
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem AtPackets.resume_preserves_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families (front.append (.live owner inputType answerType capture caller tail)))
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (resolved : scope.resolve binder = some owner) (isValue : value.erase.IsValue) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let after : SourceAnnotatedRuntime.Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨.resume hint binder value, scope,
        front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]) nextSnapshot.plan nextSnapshot.forest output remaining row bound stored.resume evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Resumed owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧ stored.resume.Admitted (ScopedTyping.resourceWorld issued) required := by
  obtain ⟨remaining, nextSnapshot, step, next, accounting, moved, _⟩ :=
    AtPackets.resume_preserves_snapshot snapshot run resolved isValue
  exact ⟨remaining, nextSnapshot, step, next, accounting, moved, moved.admitted admitted, storedAdmitted.resume⟩

/-- Source usage locates the actual owner; no live-cut or successful future
check is an additional input to this progress result. -/
theorem AtPackets.resume_progress_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families stack)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound stored evidence)
    (isValue : value.erase.IsValue) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ owner remaining,
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ nextStored : StackBounds families after.stack,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.resume hint binder value, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner])
        nextSnapshot.plan nextSnapshot.forest output remaining row bound nextStored evidence ∧
      demand = owner :: remaining ∧ SourceBoundSnapshots.Resumed owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧ nextStored.Admitted (ScopedTyping.resourceWorld issued) required := by
  obtain ⟨owner, front, capture, tail, input, answer, caller, resolved, stackSame⟩ := run.atPlan.run.resume_location
  subst stack
  obtain ⟨remaining, nextSnapshot, step, next, accounting, moved, nextAdmitted, storedNext⟩ :=
    AtPackets.resume_preserves_snapshot_admitted snapshot admitted stored storedAdmitted run resolved isValue
  exact ⟨⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩,
    owner, remaining, nextSnapshot, stored.resume, step, next, accounting, moved, nextAdmitted, storedNext⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.resume_preserves_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.resume_preserves_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.resume_progress_snapshot_admitted
