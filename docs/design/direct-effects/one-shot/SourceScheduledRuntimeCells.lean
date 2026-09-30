import SourceScheduledRuntimeEntries
import SourceScheduledFreshRequests

/-! Builtin request replies preserve the scheduled runtime. Existing exact
selection distinguishes a builtin transition from a handler capture boundary. -/
namespace Ash.OneShot.SourceScheduledExecution
open ScopedExpressions ScopedExecution

/-- The retained source and declared operation signature discharge builtin
typing for exact dependency lookup. No value-operand or extra typing premise
is needed; this concerns the request after its operand has been evaluated. -/
theorem Run.request_builtin_typed
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound)
    (found : SourceDependencyCapture.select requested operation receiving = some selected) :
    SourceHandlerCoverage.BuiltinTyped operation selected := by
  obtain ⟨answer, expression, pending⟩ := DeclaredReturnAdmission.ports before.current.source
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, known, admitted, operandTyped⟩ := ScopedPorts.typed_perform_inversion expression
      rw [before.current.signature] at known
      exact SourceHandlerCoverage.selected_typed_of_signature known found

/-- Coverage of the retained request's old interface supplies its primitive
check under a covering caller handler. This does not transport the whole saved
computation or its callbacks. -/
theorem Run.request_covered
    {actions : Syntax.UsageTickets}
    {hints : SourceContextualHints.Hints receiving} {forest : SourceRetainedPlans.Forest hints}
    {frontHints : SourceContextualHints.Hints frontScope} (front : SourceRetainedPlans.Forest frontHints)
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound)
    (covered : SourceHandlerCoverage.check requested table clauseFamilies receiving = true)
    (found : SourceDependencyCapture.select requested operation receiving = some selected)
    (passed : SourceHandlerRequirements.reaches requested frontScope = true) :
    SourceScheduledChecks.Local outward actions phases (ScopedTyping.resourceWorld issued)
      (.request (effect := requested) (operation := operation))
      (front.append (.handler (effect := requested) (table := table) (families := clauseFamilies)
        (required := declarationRequirements) forest)) :=
  SourceScheduledFreshRequests.request_from_coverage front forest covered found
    (before.request_builtin_typed found) passed

theorem builtin_step_preserves
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound)
    (isValue : operand.IsValue)
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩ after [] []) :
    ∃ nextRow,
      let state : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] []) forest output demand nextRow bound ∧ nextRow.Sublist row := by
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  obtain ⟨nextRow, next, included⟩ := SourceScheduledCells.builtin_step_preserves before.current.signature source raw rfl isValue
  obtain ⟨runtimeRow, step, current, runtimeIncluded⟩ := DeclaredExecution.builtin_step_preserves before.current isValue raw
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  refine ⟨nextRow, step, ?_, included⟩
  apply assemble_entry before.coherent before.current raw freshOwners current.names.unique step.checks usage history before.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

theorem request_selection
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound)
    (isValue : operand.IsValue) :
    (∃ after nextRow,
      let state : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] []) forest output demand nextRow bound ∧ nextRow.Sublist row) ∨
    (∃ capture tail handler, HandlerCut requested stack capture tail handler) := by
  rcases RecursiveRequestProgress.request_selection before.current.signature
      (DeclaredSourceStates.checked_state_erase before.current.source) isValue with
    ⟨after, nextRow, raw, source, included⟩ | selected
  · obtain ⟨nextRow, step, next, included⟩ := builtin_step_preserves before isValue raw
    exact Or.inl ⟨after, nextRow, step, next, included⟩
  · exact Or.inr selected


end Ash.OneShot.SourceScheduledExecution

#print axioms Ash.OneShot.SourceScheduledExecution.builtin_step_preserves
#print axioms Ash.OneShot.SourceScheduledExecution.request_selection
#print axioms Ash.OneShot.SourceScheduledExecution.Run.request_builtin_typed
#print axioms Ash.OneShot.SourceScheduledExecution.Run.request_covered
