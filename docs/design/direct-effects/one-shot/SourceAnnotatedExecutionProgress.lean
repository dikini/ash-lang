import SourceAnnotatedExecutionEntries
import SourceScheduledProgress

/-! Exhaustive progress reuses the existing typed current-form classification.
Each actual annotated successor carries the same shared runtime invariant. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledSavedPlans (Saved)

/-- Retained handler coverage selects the actual annotated clause and its
advertised capability entry. -/
theorem Run.selected_clause
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ forest output demand row bound)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler) :
    ∃ parameter binder code offered,
      SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code ∧
      lookup operation (tables handler.erase) = some offered := by
  obtain ⟨parameter, binder, rawCode, offered, selected, found⟩ := run.erase.selected_clause cut.erase
  obtain ⟨code, lifted, same⟩ := SourceAnnotatedRuntime.ClauseAt.of_raw selected
  exact ⟨parameter, binder, code, offered, lifted, found⟩

private theorem successor_witness {before after : SourceAnnotatedRuntime.NamedState}
    (next : Run operations declarations policy contracts registry tables families required annotations
      after forest output demand row bound)
    (step : NamedAccessStep [] before.erase after.erase) :
    ∃ after nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved, ∃ nextDemand nextRow,
      NamedAccessStep [] before.erase after.erase ∧
      Run operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after saved.forest output nextDemand nextRow bound :=
  ⟨after, contracts, registry, tables, families, required, annotations, ⟨_, _, forest⟩, demand, row, step, next⟩

/-- From the shared annotated invariant, a configuration is terminal or has an
actual step and a successor invariant. Initial admission remains separate. -/
theorem Run.progress
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound) :
    (before.execution.configuration.expression.erase.IsValue ∧ before.execution.configuration.stack = .nil) ∨
    ∃ after nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved, ∃ nextDemand nextRow,
      NamedAccessStep [] before.erase after.erase ∧
      Run operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after saved.forest output nextDemand nextRow bound := by
  obtain ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ := before
  obtain ⟨input, current, stackTyped⟩ := DeclaredReturnAdmission.ports run.current.source
  cases current with
  | checked scopeTyped typed =>
    simp only [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase] at typed
    have form := ScopedPortProgress.typed_current_form typed
    change ScopedPortProgress.CurrentForm code.erase at form
    generalize same : code.erase = erased at form typed
    cases form with
    | value isValue =>
      have actualValue : code.erase.IsValue := same ▸ isValue
      rcases run.value_progress actualValue with terminal | ⟨after, discharged, remaining, saved, step, next, accounting⟩
      · exact Or.inl ⟨isValue, terminal⟩
      · exact Or.inr (successor_witness next step)
    | focus position =>
      obtain ⟨child, context, lifted, _, _⟩ := SourceAnnotatedCode.focus_lift (same ▸ position)
      obtain ⟨plain, saved, contextSame, scopeSame, guard, step, next⟩ := run.focus_progress lifted
      exact Or.inr (successor_witness next step)
    | bind isValue =>
      have ready : RecursiveExpressions.Ready code.erase := same ▸ .bind isValue
      obtain ⟨after, remaining, nextRow, step, next, accounting, included⟩ := run.ready_progress ready
      exact Or.inr (successor_witness next step)
    | app functionValue argumentValue => cases typed with
      | app function argument available =>
        obtain ⟨parameter, body, functionSame⟩ := ScopedPorts.typed_function_value function functionValue
        have ready : RecursiveExpressions.Ready code.erase := by rw [same, functionSame]; exact .app argumentValue
        obtain ⟨after, remaining, nextRow, step, next, accounting, included⟩ := run.ready_progress ready
        exact Or.inr (successor_witness next step)
    | branch isValue => cases typed with
      | branch condition yes no =>
        obtain ⟨flag, conditionSame⟩ := ScopedPorts.typed_boolean_value condition isValue
        have ready : RecursiveExpressions.Ready code.erase := by rw [same, conditionSame]; exact .branch
        obtain ⟨after, remaining, nextRow, step, next, accounting, included⟩ := run.ready_progress ready
        exact Or.inr (successor_witness next step)
    | request isValue =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      rcases same with ⟨rfl, rfl, rfl⟩
      rcases RecursiveRequestProgress.request_selection run.current.signature
          (DeclaredSourceStates.checked_state_erase run.current.source) isValue with
        ⟨rawAfter, rawRow, raw, rawSource, included⟩ | ⟨rawCapture, rawTail, rawHandler, cut⟩
      · obtain ⟨after, nextRow, same, step, next, included⟩ := run.builtin_step_preserves isValue raw
        exact Or.inr (successor_witness next step)
      · obtain ⟨capture, tail, handler, lifted, _, _, _⟩ := SourceAnnotatedRuntime.HandlerCut.of_raw cut
        obtain ⟨parameter, binder, body, offered, selected, found⟩ := run.selected_clause lifted
        obtain ⟨owner, contract, record, captured, waiting, after, nextDemand, nextRow,
          annotation, step, next, accounting, included, owners⟩ := run.capture_progress lifted isValue selected found
        exact Or.inr (successor_witness next step)
    | handler =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      rcases same with ⟨rfl, rfl, rfl⟩
      obtain ⟨handler, table, clauseFamilies, declarationRequirements, saved, fresh, step, next⟩ := run.handler_progress
      exact Or.inr (successor_witness next step)
    | resume isValue =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      rcases same with ⟨rfl, rfl⟩
      obtain ⟨after, owner, remaining, saved, step, next, accounting⟩ := run.resume_progress isValue
      exact Or.inr (successor_witness next step)
    | discard =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      cases same
      obtain ⟨after, owner, remaining, saved, step, next, accounting⟩ := run.discard_progress
      exact Or.inr (successor_witness next step)
    | resource isValue =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      rcases same with ⟨rfl, rfl, rfl⟩
      obtain ⟨identity, payload, answer, saved, initialSame, step, next⟩ := run.resource_progress isValue
      exact Or.inr (successor_witness next step)
    | cleanup isValue =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      rcases same with ⟨rfl, rfl⟩
      obtain ⟨action, saved, step, next⟩ := run.cleanup_progress isValue
      exact Or.inr (successor_witness next step)

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.selected_clause
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.progress
