import SourceAnnotatedExecutionCheckedEntries

/-! Ordinary reduction, returns and builtin replies preserve the supplied annotated target.
The existing source theorems and runtime completion proofs do the work; erasure
is not used to infer equality between independently annotated successors. -/
namespace Ash.OneShot.SourceAnnotatedRuntime

theorem ReturnStep.is_value (event : ReturnStep before after created discharged) :
    before.expression.erase.IsValue := by
  cases event <;> first | exact (by assumption : ScopedExpressions.ClosedValue _).1 | trivial

end Ash.OneShot.SourceAnnotatedRuntime

namespace Ash.OneShot.SourceAnnotatedExecution

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution
open SourceScheduledSavedPlans (Saved)
open RecursiveCompletion (retiredTickets)

theorem Run.return_step
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound evidence)
    (event : SourceAnnotatedRuntime.ReturnStep before.execution.configuration after [] discharged) :
    ∃ remaining, ∃ saved : Saved,
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] discharged).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] discharged) saved.forest output remaining row bound evidence ∧
      demand = retiredTickets discharged ++ remaining := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨remaining, saved, next, accounting, _, _⟩ :=
    SourceAnnotatedRuntimeReturns.return_preserves source event
  have isValue := event.is_value
  have raw := event.erase
  obtain ⟨runtimeRemaining, step, current, runtimeAccounting, empty⟩ :=
    DeclaredExecution.value_step_preserves run.current isValue raw
  have freshOwners : (before.execution.issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨remaining, saved, step, ?_, accounting⟩
  apply assemble_entry (after := after) run.coherent run.current raw freshOwners current.names.unique
    step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

theorem Run.ordinary_step
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (event : SourceAnnotatedCode.Reduction code scope afterCode afterScope) :
    ∃ remaining nextRow,
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨afterCode, afterScope, stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) forest output remaining nextRow bound evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨remaining, nextRow, next, accounting, included⟩ :=
    SourceAnnotatedRuntimeComputation.ordinary_preserves source event
  have ready : RecursiveExpressions.Ready code.erase := by
    cases event with
    | bind closed environment => exact .bind closed.1
    | beta closed closure => exact .app closed.1
    | ifTrue | ifFalse => exact .branch
  have raw := SourceAnnotatedRuntime.ordinary_executes event stack
  obtain ⟨runtimeRemaining, runtimeRow, step, current, runtimeAccounting, runtimeIncluded⟩ :=
    SourceScheduledExecution.ready_preserves run.erase ready raw
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨remaining, nextRow, step, ?_, accounting, included⟩
  apply assemble_entry (after := ⟨afterCode, afterScope, stack⟩) run.coherent run.current raw freshOwners
    current.current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.current.results
  · rfl
  · simp

theorem Run.read_step {stack afterStack : SourceAnnotatedRuntime.Stack}
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 0
        (.resourceRef referenceHint (.activation identity)), scope, stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound evidence)
    (selected : SourceAnnotatedRuntime.CellUpdate identity payload payload stack afterStack) :
    ∃ nextRow,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 0
          (.resourceRef referenceHint (.activation identity)), scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨.integer .integer payload, scope, afterStack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) forest output demand nextRow bound evidence ∧ nextRow.Sublist row := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨nextRow, raw, next, included, _⟩ :=
    SourceAnnotatedRuntimeCells.read_preserves (by rw [run.current.signature]; rfl) source selected
  obtain ⟨runtimeRow, step, current, runtimeIncluded⟩ := DeclaredExecution.builtin_step_preserves run.current trivial raw
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨nextRow, step, ?_, included⟩
  apply assemble_entry (after := ⟨.integer .integer payload, scope, afterStack⟩) run.coherent run.current raw
    freshOwners current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

theorem Run.write_step {stack afterStack : SourceAnnotatedRuntime.Stack}
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 1
        (.pair pairHint (.resourceRef referenceHint (.activation identity)) (.integer integerHint new)), scope, stack⟩,
        issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (selected : SourceAnnotatedRuntime.CellUpdate identity old new stack afterStack) :
    ∃ nextRow,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 1
          (.pair pairHint (.resourceRef referenceHint (.activation identity)) (.integer integerHint new)), scope, stack⟩,
          issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨.unit .unit, scope, afterStack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) forest output demand nextRow bound evidence ∧ nextRow.Sublist row := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨nextRow, raw, next, included, _⟩ :=
    SourceAnnotatedRuntimeCells.write_preserves (by rw [run.current.signature]; rfl) source selected
  obtain ⟨runtimeRow, step, current, runtimeIncluded⟩ :=
    DeclaredExecution.builtin_step_preserves run.current ⟨trivial, trivial⟩ raw
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨nextRow, step, ?_, included⟩
  apply assemble_entry (after := ⟨.unit .unit, scope, afterStack⟩) run.coherent run.current raw
    freshOwners current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.return_step
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.ordinary_step
#print axioms Ash.OneShot.SourceAnnotatedRuntime.ReturnStep.is_value
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.read_step
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.write_step
