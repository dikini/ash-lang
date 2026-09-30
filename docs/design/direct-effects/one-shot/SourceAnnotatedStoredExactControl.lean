import SourceAnnotatedStoredExecutionReturns
import SourceAnnotatedStoredExecutionComputation
import SourceAnnotatedStoredExecutionCells
import SourceAnnotatedExecutionExactControl

/-! Preserve the supplied annotated event target while retaining the actual
source snapshot and packet stack. Existing runtime proofs supply ownership,
access and completion; erasure is never used to equate source annotations. -/
namespace Ash.OneShot.SourceAnnotatedExecution
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution
open RecursiveCompletion (retiredTickets)

theorem AtPackets.return_step_snapshot
    {before : SourceAnnotatedRuntime.NamedState}
    {after : SourceAnnotatedRuntime.Configuration}
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families before.execution.configuration.stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound stored evidence)
    (event : SourceAnnotatedRuntime.ReturnStep before.execution.configuration after [] discharged) :
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] discharged).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] discharged) nextSnapshot.plan nextSnapshot.forest output remaining row bound nextStored evidence ∧
      demand = retiredTickets discharged ++ remaining ∧
      SourceAnnotatedRuntime.ReturnBounds event snapshot nextSnapshot ∧
      SourceAnnotatedRuntime.ReturnPackets event stored nextStored := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨nextStored, remaining, nextSnapshot, next, accounting, _, _, moved, packets⟩ :=
    SourceAnnotatedStoredReturns.return_preserves_snapshot snapshot source event
  have isValue := event.is_value
  have raw := event.erase
  obtain ⟨runtimeRemaining, step, current, runtimeAccounting, empty⟩ :=
    DeclaredExecution.value_step_preserves run.current isValue raw
  have freshOwners : (before.execution.issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨nextStored, remaining, nextSnapshot, step, ?_, accounting, moved, packets⟩
  apply assemble_entry_atPackets (after := after) run.coherent run.current raw freshOwners current.names.unique
    step.checks usage history run.annotationHistory retained
  · simpa only [SourceBoundSnapshots.Snapshot.value, ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

theorem AtPackets.ordinary_step_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (event : SourceAnnotatedCode.Reduction code scope afterCode afterScope) :
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued), ∃ remaining nextRow,
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨afterCode, afterScope, stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output remaining nextRow bound stored evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ SourceBoundSnapshots.Computed event.rule snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨nextSnapshot, remaining, nextRow, _, next, moved, accounting, included⟩ :=
    SourceAnnotatedStoredComputation.ordinary_snapshot snapshot source event
  have ready : RecursiveExpressions.Ready code.erase := by
    cases event with
    | bind closed environment => exact .bind closed.1
    | beta closed closure => exact .app closed.1
    | ifTrue | ifFalse => exact .branch
  have raw := SourceAnnotatedRuntime.ordinary_executes event stack
  obtain ⟨runtimeRemaining, runtimeRow, step, current, runtimeAccounting, runtimeIncluded⟩ :=
    SourceScheduledExecution.ready_preserves run.atPlan.run.erase ready raw
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨nextSnapshot, remaining, nextRow, step, ?_, accounting, included, moved⟩
  apply assemble_entry_atPackets (after := ⟨afterCode, afterScope, stack⟩) run.coherent run.current raw freshOwners
    current.current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [SourceBoundSnapshots.Snapshot.value, ScopedActionUsage.advance, List.append_nil] using next
  · exact current.current.results
  · rfl
  · simp

theorem AtPackets.read_step_snapshot {stack afterStack : SourceAnnotatedRuntime.Stack}
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 0
        (.resourceRef referenceHint (.activation identity)), scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound stored evidence)
    (selected : SourceAnnotatedRuntime.CellUpdate identity payload payload stack afterStack) :
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families afterStack, ∃ nextRow,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 0
          (.resourceRef referenceHint (.activation identity)), scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨.integer .integer payload, scope, afterStack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) (SourceBoundSnapshots.Snapshot.value snapshot.pending).plan
        (SourceBoundSnapshots.Snapshot.value snapshot.pending).forest output demand nextRow bound nextStored evidence ∧ nextRow.Sublist row ∧ SourceAnnotatedRuntime.CellPackets selected stored nextStored := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨nextStored, nextRow, raw, next, included, _, packets⟩ :=
    SourceAnnotatedStoredCells.read_preserves_atPackets (by rw [run.current.signature]; rfl) source selected
  obtain ⟨runtimeRow, step, current, runtimeIncluded⟩ := DeclaredExecution.builtin_step_preserves run.current trivial raw
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨nextStored, nextRow, step, ?_, included, packets⟩
  apply assemble_entry_atPackets (after := ⟨.integer .integer payload, scope, afterStack⟩) run.coherent run.current raw
    freshOwners current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [SourceBoundSnapshots.Snapshot.value, ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

theorem AtPackets.write_step_snapshot {stack afterStack : SourceAnnotatedRuntime.Stack}
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 1
        (.pair pairHint (.resourceRef referenceHint (.activation identity)) (.integer integerHint new)), scope, stack⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (selected : SourceAnnotatedRuntime.CellUpdate identity old new stack afterStack) :
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families afterStack, ∃ nextRow,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 1
          (.pair pairHint (.resourceRef referenceHint (.activation identity)) (.integer integerHint new)), scope, stack⟩,
          issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨.unit .unit, scope, afterStack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) (SourceBoundSnapshots.Snapshot.value snapshot.pending).plan
        (SourceBoundSnapshots.Snapshot.value snapshot.pending).forest output demand nextRow bound nextStored evidence ∧ nextRow.Sublist row ∧ SourceAnnotatedRuntime.CellPackets selected stored nextStored := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨nextStored, nextRow, raw, next, included, _, packets⟩ :=
    SourceAnnotatedStoredCells.write_preserves_atPackets (by rw [run.current.signature]; rfl) source selected
  obtain ⟨runtimeRow, step, current, runtimeIncluded⟩ :=
    DeclaredExecution.builtin_step_preserves run.current ⟨trivial, trivial⟩ raw
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨nextStored, nextRow, step, ?_, included, packets⟩
  apply assemble_entry_atPackets (after := ⟨.unit .unit, scope, afterStack⟩) run.coherent run.current raw
    freshOwners current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [SourceBoundSnapshots.Snapshot.value, ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.return_step_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.ordinary_step_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.read_step_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.write_step_snapshot
