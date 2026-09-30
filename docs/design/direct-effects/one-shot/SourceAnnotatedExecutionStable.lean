import SourceAnnotatedExecutionCapture
import SourceAnnotatedExecutionFocus
import SourceScheduledRuntimeCells
import SourceAnnotatedRuntimeCells

/-! Returned values and builtin replies reuse the existing runtime completion
proofs while retaining the actual annotated successor source. -/
namespace Ash.OneShot.SourceAnnotatedExecution

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
variable [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution
open SourceScheduledSavedPlans (Saved)
open RecursiveCompletion (retiredTickets)

/-- A value in a plain context has a combined execution successor carrying
exactly the queued source bounds. Closedness follows from the original source
invariant; no raw step or successor admission is assumed. -/
theorem AtPlan.plug_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨value, scope, .push (.plain plain) tail⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : value.erase.IsValue) :
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨value, scope, .push (.plain plain) tail⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨plain.context.plug value, plain.scope, tail⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output demand row bound evidence ∧
      SourceBoundSnapshots.Returned plain.context snapshot next := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  have closed := DeclaredSourceStates.value_closed run.current.source isValue
  obtain ⟨nextSnapshot, raw, next, returned⟩ := SourceAnnotatedRuntimeReturns.plug_snapshot snapshot source closed
  obtain ⟨runtimeRemaining, step, current, accounting, empty⟩ :=
    DeclaredExecution.value_step_preserves run.current isValue raw
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨nextSnapshot, step, ?_, returned⟩
  apply assemble_entry_atPlan run.coherent run.current raw freshOwners current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

/-- Every raw value-return step lifts to the annotated runtime, including
cleanup completion and ticket retirement. -/
theorem AtPlan.value_step_preserves_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations before snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : before.execution.configuration.expression.erase.IsValue)
    (raw : RawStep before.execution.configuration.erase rawAfter created discharged) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
      after.erase = rawAfter ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after created discharged).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after created discharged) nextSnapshot.plan nextSnapshot.forest output remaining row bound evidence ∧
      demand = retiredTickets discharged ++ remaining ∧ created = [] ∧
      (∃ lifted : SourceAnnotatedRuntime.ReturnStep before.execution.configuration after created discharged,
        SourceAnnotatedRuntime.ReturnBounds lifted snapshot nextSnapshot) := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨after, remaining, nextSnapshot, same, next, accounting, noCreated, trace, moved⟩ :=
    SourceAnnotatedRuntimeReturns.raw_return_preserves_snapshot snapshot source raw isValue
  subst rawAfter
  subst created
  obtain ⟨runtimeRemaining, step, current, runtimeAccounting, empty⟩ :=
    DeclaredExecution.value_step_preserves run.current isValue raw
  have freshOwners : (before.execution.issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨after, remaining, nextSnapshot, rfl, step, ?_, accounting, rfl, moved⟩
  apply assemble_entry_atPlan run.coherent run.current raw freshOwners current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

theorem Run.value_step_preserves
    (run : Run operations declarations policy contracts registry tables families required annotations before forest output demand row bound evidence)
    (isValue : before.execution.configuration.expression.erase.IsValue)
    (raw : RawStep before.execution.configuration.erase rawAfter created discharged) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ remaining, ∃ saved : Saved,
      after.erase = rawAfter ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after created discharged).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after created discharged) saved.forest output remaining row bound evidence ∧
      demand = retiredTickets discharged ++ remaining ∧ created = [] := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  cases source with
  | checked current scope pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued) :=
        ⟨_, rootPlan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
      have indexed : AtPlan operations declarations policy contracts registry tables families required annotations
          before snapshot.plan snapshot.forest output demand row bound evidence :=
        ⟨run.coherent, run.current, run.annotationHistory, actions, usage, history,
          .checked current scope pending closing templates matched contextual unique evaluated accepted accounting, retained⟩
      obtain ⟨after, remaining, nextSnapshot, same, step, next, accounting, empty, _⟩ :=
        AtPlan.value_step_preserves_snapshot snapshot indexed isValue raw
      exact ⟨after, remaining, ⟨_, _, nextSnapshot.forest⟩, same, step, next.run, accounting, empty⟩

/-- A returned value is terminal exactly at the empty stack; otherwise the
existing raw progress proof supplies a step whose annotations are retained. -/
theorem Run.value_progress
    (run : Run operations declarations policy contracts registry tables families required annotations before forest output demand row bound evidence)
    (isValue : before.execution.configuration.expression.erase.IsValue) :
    before.execution.configuration.stack = .nil ∨
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ discharged remaining, ∃ saved : Saved,
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] discharged).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] discharged) saved.forest output remaining row bound evidence ∧
      demand = retiredTickets discharged ++ remaining := by
  rcases DeclaredSourceStates.value_progress run.current.source isValue with terminal | ⟨rawAfter, discharged, raw⟩
  · left
    change before.execution.configuration.stack.erase = .nil at terminal
    cases stackSame : before.execution.configuration.stack <;>
      simp_all only [SourceAnnotatedRuntime.Stack.erase, reduceCtorEq]
  · obtain ⟨after, remaining, saved, same, step, next, accounting, empty⟩ := run.value_step_preserves isValue raw
    exact Or.inr ⟨after, discharged, remaining, saved, step, next, accounting⟩

/-- Every nonterminal returned value has a snapshot-preserving combined step.
The original value progress theorem supplies the raw transition; all eight
return forms are covered by the shared snapshot preservation proof. -/
theorem AtPlan.value_progress_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : before.execution.configuration.expression.erase.IsValue) :
    before.execution.configuration.stack = .nil ∨
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ discharged remaining,
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] discharged).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] discharged) nextSnapshot.plan nextSnapshot.forest output remaining row bound evidence ∧
      demand = retiredTickets discharged ++ remaining ∧
      (∃ lifted : SourceAnnotatedRuntime.ReturnStep before.execution.configuration after [] discharged,
        SourceAnnotatedRuntime.ReturnBounds lifted snapshot nextSnapshot) := by
  rcases DeclaredSourceStates.value_progress run.current.source isValue with terminal | ⟨rawAfter, discharged, raw⟩
  · left
    change before.execution.configuration.stack.erase = .nil at terminal
    cases stackSame : before.execution.configuration.stack <;>
      simp_all only [SourceAnnotatedRuntime.Stack.erase, reduceCtorEq]
  · obtain ⟨after, remaining, nextSnapshot, _, step, next, accounting, _, moved⟩ :=
      AtPlan.value_step_preserves_snapshot snapshot run isValue raw
    exact Or.inr ⟨after, discharged, remaining, nextSnapshot, step, next, accounting, moved⟩

/-- Every raw builtin reply to a ready request preserves the annotated runtime.
Its operation signature is authenticated by the shared invariant. -/
theorem AtPlan.builtin_step_preserves_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : operand.erase.IsValue)
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, stack.erase⟩ rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ nextRow,
      after.erase = rawAfter ∧
      let nextSnapshot := SourceBoundSnapshots.Snapshot.value snapshot.pending
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand nextRow bound evidence ∧ nextRow.Sublist row := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨after, nextRow, same, next, included⟩ :=
    SourceAnnotatedRuntimeCells.builtin_step_preserves_atPlan run.current.signature source raw isValue
  subst rawAfter
  obtain ⟨runtimeRow, step, current, runtimeIncluded⟩ := DeclaredExecution.builtin_step_preserves run.current isValue raw
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨after, nextRow, rfl, step, ?_, included⟩
  apply assemble_entry_atPlan run.coherent run.current raw freshOwners current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [SourceBoundSnapshots.Snapshot.value, ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

theorem Run.builtin_step_preserves
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound evidence)
    (isValue : operand.erase.IsValue)
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, stack.erase⟩ rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ nextRow,
      after.erase = rawAfter ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) forest output demand nextRow bound evidence ∧ nextRow.Sublist row := by
  obtain ⟨_, plan, indexed⟩ := run.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, plan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
  obtain ⟨after, nextRow, same, step, next, included⟩ :=
    AtPlan.builtin_step_preserves_snapshot snapshot indexed isValue raw
  exact ⟨after, nextRow, same, step, next.run, included⟩

/-- Existing exact request selection either supplies a builtin step retaining
the snapshot, or identifies the actual selected handler cut. This does not
assume admission of that handler's captured continuation. -/
theorem AtPlan.request_selection_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : operand.erase.IsValue) :
    (∃ after : SourceAnnotatedRuntime.Configuration, ∃ nextRow,
      let nextSnapshot := SourceBoundSnapshots.Snapshot.value snapshot.pending
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand nextRow bound evidence ∧
      nextRow.Sublist row) ∨
    (∃ capture tail handler, HandlerCut requested stack.erase capture tail handler) := by
  rcases RecursiveRequestProgress.request_selection run.current.signature
      (DeclaredSourceStates.checked_state_erase run.current.source) isValue with
    ⟨rawAfter, rawRow, raw, source, included⟩ | selected
  · obtain ⟨after, nextRow, _, step, next, included⟩ :=
      AtPlan.builtin_step_preserves_snapshot snapshot run isValue raw
    exact Or.inl ⟨after, nextRow, step, next, included⟩
  · exact Or.inr selected

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.value_step_preserves
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.value_progress
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.builtin_step_preserves

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.plug_snapshot

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.value_step_preserves_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.value_progress_snapshot

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.builtin_step_preserves_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.request_selection_snapshot
