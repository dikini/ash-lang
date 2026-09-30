import SourceAnnotatedStoredExecution
import SourceAnnotatedStoredCells
import SourceAnnotatedBoundAdmission

/-! Builtin replies preserve the actual packet stack through cell updates.
The existing request selection proof chooses a builtin step or handler cut. -/
namespace Ash.OneShot.SourceAnnotatedExecution
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution

theorem AtPackets.builtin_step_preserves_snapshot
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound stored evidence)
    (isValue : operand.erase.IsValue)
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, stack.erase⟩ rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack, ∃ nextRow,
      after.erase = rawAfter ∧
      let nextSnapshot := SourceBoundSnapshots.Snapshot.value snapshot.pending
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand nextRow bound nextStored evidence ∧ nextRow.Sublist row ∧
      (∃ identity old new, ∃ update : SourceAnnotatedRuntime.CellUpdate identity old new stack after.stack,
        SourceAnnotatedRuntime.CellPackets update stored nextStored) := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨after, nextStored, nextRow, same, next, included, packets⟩ :=
    SourceAnnotatedStoredCells.builtin_step_preserves_atPackets run.current.signature source raw isValue
  subst rawAfter
  obtain ⟨runtimeRow, step, current, runtimeIncluded⟩ := DeclaredExecution.builtin_step_preserves run.current isValue raw
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨after, nextStored, nextRow, rfl, step, ?_, included, packets⟩
  apply assemble_entry_atPackets run.coherent run.current raw freshOwners current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [SourceBoundSnapshots.Snapshot.value, ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp
theorem AtPackets.request_selection_snapshot
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound stored evidence)
    (isValue : operand.erase.IsValue) :
    (∃ after : SourceAnnotatedRuntime.Configuration,
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack, ∃ nextRow,
      let nextSnapshot := SourceBoundSnapshots.Snapshot.value snapshot.pending
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand nextRow bound nextStored evidence ∧
      nextRow.Sublist row ∧
      (∃ identity old new, ∃ update : SourceAnnotatedRuntime.CellUpdate identity old new stack after.stack,
        SourceAnnotatedRuntime.CellPackets update stored nextStored)) ∨
    (∃ capture tail handler, HandlerCut requested stack.erase capture tail handler) := by
  rcases RecursiveRequestProgress.request_selection run.current.signature
      (DeclaredSourceStates.checked_state_erase run.current.source) isValue with
    ⟨rawAfter, rawRow, raw, source, included⟩ | selected
  · obtain ⟨after, nextStored, nextRow, _, step, next, included, packets⟩ :=
      AtPackets.builtin_step_preserves_snapshot snapshot run isValue raw
    exact Or.inl ⟨after, nextStored, nextRow, step, next, included, packets⟩
  · exact Or.inr selected

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem AtPackets.builtin_step_preserves_snapshot_admitted
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound stored evidence)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (isValue : operand.erase.IsValue)
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, stack.erase⟩ rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack, ∃ nextRow,
      after.erase = rawAfter ∧
      let nextSnapshot := SourceBoundSnapshots.Snapshot.value snapshot.pending
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand nextRow bound nextStored evidence ∧ nextRow.Sublist row ∧
      (∃ identity old new, ∃ update : SourceAnnotatedRuntime.CellUpdate identity old new stack after.stack,
        SourceAnnotatedRuntime.CellPackets update stored nextStored) ∧ nextSnapshot.Admitted ∧ nextStored.Admitted (ScopedTyping.resourceWorld issued) required := by
  obtain ⟨after, nextStored, nextRow, same, step, successor, included, ⟨identity, old, new, update, packets⟩⟩ :=
    AtPackets.builtin_step_preserves_snapshot snapshot run isValue raw
  exact ⟨after, nextStored, nextRow, same, step, successor, included, ⟨identity, old, new, update, packets⟩,
    SourceBoundSnapshots.Snapshot.value_admitted admitted.2, packets.admitted storedAdmitted⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.builtin_step_preserves_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.request_selection_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.builtin_step_preserves_snapshot_admitted
