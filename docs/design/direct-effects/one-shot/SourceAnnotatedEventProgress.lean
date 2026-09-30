import SourceAnnotatedEventSelection

/-! Exhaustive progress targets exactly the relation used by universal
preservation. The current-form classification and existing selection lemmas
supply the cases; finite executions store only operational events. -/
namespace Ash.OneShot.SourceAnnotatedExecutionEvents
open ScopedExpressions ScopedExecution
open SourceAnnotatedRuntime (NamedState advanceState)
open SourceAnnotatedExecution (Run)

/-- A nonallocating ready request selects an actual annotated cell. -/
theorem builtin_event
    (raw : RawStep ⟨.perform effect operation operand.erase, scope, stack.erase⟩ rawAfter [] [])
    (isValue : operand.erase.IsValue) :
    ∃ after, Step signature result
      ⟨⟨⟨.perform hint effect operation operand, scope, stack⟩, issued, completed⟩, activations⟩ after := by
  have ordinary := ScopedPortProgress.nonallocating_request_is_ordinary raw rfl isValue
  generalize same : (Configuration.mk (.perform effect operation operand.erase) scope stack.erase) = rawBefore at ordinary
  have requested : rawBefore.expression = .perform effect operation operand.erase := by rw [← same]
  cases ordinary <;> try cases requested
  case read selected =>
    simp only [Configuration.mk.injEq, Code.perform.injEq] at same
    rcases same with ⟨⟨rfl, rfl, operandSame⟩, rfl, rfl⟩
    cases operand <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at operandSame
    cases operandSame
    obtain ⟨after, lifted, _⟩ := SourceAnnotatedRuntime.CellUpdate.of_raw selected
    exact ⟨_, .readCell lifted⟩
  case write selected =>
    simp only [Configuration.mk.injEq, Code.perform.injEq] at same
    rcases same with ⟨⟨rfl, rfl, operandSame⟩, rfl, rfl⟩
    cases operand <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at operandSame
    rename_i pairHint reference integer
    simp only [Code.pair.injEq] at operandSame
    obtain ⟨referenceSame, integerSame⟩ := operandSame
    cases reference <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at referenceSame
    cases referenceSame
    cases integer <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at integerSame
    cases integerSame
    obtain ⟨after, lifted, _⟩ := SourceAnnotatedRuntime.CellUpdate.of_raw selected
    exact ⟨_, .writeCell lifted⟩

/-- Capture selection reuses the established signature and clause evidence. -/
theorem capture_event
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ forest output demand row bound)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue) :
    ∃ after, Step operations.erase.erase.ports output.erase.erase.port
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ after := by
  obtain ⟨parameter, binder, body, offered, selected, found⟩ := run.selected_clause cut
  obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) run.current.ledger.2
  obtain ⟨contract, record, captured, waiting, actual, nextDemand, nextRow, annotation,
    step, next, balance, included, owners, shape, argument, known⟩ :=
    run.capture_preserves cut isValue selected found fresh
  have portKnown := CoherentSourceTypes.port_lookup
    (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known))
  exact ⟨_, .capture cut isValue selected portKnown fresh⟩

/-- Every admitted state is terminal or has a step of the very same annotated
relation whose universal preservation was proved. No next-state invariant is
assumed to choose that event. Initial source admission remains separate. -/
theorem progress
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound) :
    (before.execution.configuration.expression.erase.IsValue ∧ before.execution.configuration.stack = .nil) ∨
    ∃ after, Step operations.erase.erase.ports output.erase.erase.port before after := by
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
      rcases value_event run actualValue with terminal | event
      · exact Or.inl ⟨isValue, terminal⟩
      · exact Or.inr event
    | focus position =>
      obtain ⟨child, context, lifted, _, _⟩ := SourceAnnotatedCode.focus_lift (same ▸ position)
      obtain ⟨plain, saved, contextSame, scopeSame, guard, _, _⟩ := run.focus_progress lifted
      have event := Step.focus (contextSame.symm ▸ lifted) guard
        (issued := issued) (completed := completed) (activations := activations)
        (signature := operations.erase.erase.ports)
      exact Or.inr ⟨_, by simpa only [scopeSame] using event⟩
    | bind isValue =>
      exact Or.inr (ready_event run (same ▸ .bind isValue))
    | app functionValue argumentValue => cases typed with
      | app function argument available =>
        obtain ⟨parameter, body, functionSame⟩ := ScopedPorts.typed_function_value function functionValue
        have ready : RecursiveExpressions.Ready code.erase := by rw [same, functionSame]; exact .app argumentValue
        exact Or.inr (ready_event run ready)
    | branch isValue => cases typed with
      | branch condition yes no =>
        obtain ⟨flag, conditionSame⟩ := ScopedPorts.typed_boolean_value condition isValue
        have ready : RecursiveExpressions.Ready code.erase := by rw [same, conditionSame]; exact .branch
        exact Or.inr (ready_event run ready)
    | request isValue =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      rcases same with ⟨rfl, rfl, rfl⟩
      rcases RecursiveRequestProgress.request_selection run.current.signature
          (DeclaredSourceStates.checked_state_erase run.current.source) isValue with
        ⟨rawAfter, rawRow, raw, rawSource, included⟩ | ⟨rawCapture, rawTail, rawHandler, cut⟩
      · exact Or.inr (builtin_event raw isValue)
      · obtain ⟨capture, tail, handler, lifted, _, _, _⟩ := SourceAnnotatedRuntime.HandlerCut.of_raw cut
        exact Or.inr (capture_event run lifted isValue)
    | handler =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      rcases same with ⟨rfl, rfl, rfl⟩
      exact Or.inr (handler_event run)
    | resume isValue =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      rcases same with ⟨rfl, rfl⟩
      exact Or.inr (resume_event run isValue)
    | discard =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      cases same
      exact Or.inr (discard_event run)
    | resource isValue =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      rcases same with ⟨rfl, rfl, rfl⟩
      exact Or.inr (resource_event run isValue)
    | cleanup isValue =>
      cases code <;> simp [SourceAnnotatedCode.Term.erase] at same
      rcases same with ⟨rfl, rfl⟩
      exact Or.inr (cleanup_event run isValue)

/-- Any finite supplied execution from one admitted state ends in a terminal
state or can take another event. Intermediate admission follows by induction. -/
theorem finite_progress
    (trace : Steps operations.erase.erase.ports output.erase.erase.port count before after)
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound) :
    (after.execution.configuration.expression.erase.IsValue ∧ after.execution.configuration.stack = .nil) ∨
    ∃ next, Step operations.erase.erase.ports output.erase.erase.port after next := by
  obtain ⟨_, _, _, _, _, _, _, saved, nextDemand, nextRow, next, _⟩ := steps_preserve trace run
  exact progress next

end Ash.OneShot.SourceAnnotatedExecutionEvents

#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.builtin_event
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.capture_event
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.progress
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.finite_progress
