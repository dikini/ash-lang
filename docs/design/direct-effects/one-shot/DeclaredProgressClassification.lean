import DeclaredInstallationProgress

/-! Exhaustive classification of what the current strengthened invariant proves.
Terminal configurations and constructed preserving steps are separated from the
three annotation/capture forms still needing a source-admission connection.
The last alternative is a syntactic classifier, not permission to execute or
an assumed future preservation theorem.
-/
namespace Ash.OneShot.DeclaredClosingInvariant
open ScopedExpressions ScopedExecution CoherentSourceTypes

/-- Current usage identifies the resumption owner without a supplied boundary. -/
theorem resume_owner
    (checked : CodeDemand policy actions scope (.resume binder value) demand) :
    ∃ owner, scope.resolve binder = some owner ∧ demand = [owner] := by
  cases checked with
  | idle scope checked => cases checked
  | consume known checked => cases checked with
      | resume permitted operand => exact ⟨_, by simp [Execution.Scope.resolve], rfl⟩

/-- Derive the live boundary from current usage and reuse the existing
recomposition proof. No owner, cut or resolution premise is supplied. -/
theorem resume_progress
    (before : Prepared operations declarations policy registry tables
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : value.IsValue) :
    ∃ after owner remaining,
      NamedAccessStep [] ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Prepared operations declarations policy registry tables after output remaining row bound ∧
      demand = owner :: remaining := by
  obtain ⟨actions, usage, history, requests, closing⟩ := before.actions
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := usage
  obtain ⟨owner, resolved, same⟩ := resume_owner code
  have present : owner ∈ activeTickets stack := accessible (same ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := ScopedPortJoint.active_ticket_has_boundary present
  subst stack
  obtain ⟨remaining, step, next, accounting⟩ := resume_preserves before resolved isValue
  exact ⟨_, owner, remaining, step, next, accounting⟩

/-- These constructors record only current syntax, value/focus facts and the
actual handler cut. None supplies a successor or asserts that admission holds. -/
inductive AnnotationOrCapture : Configuration → Prop where
  | focus (position : Focus code child context) : AnnotationOrCapture ⟨code, scope, stack⟩
  | cleanup (isValue : callback.IsValue) : AnnotationOrCapture ⟨.cleanup callback body, scope, stack⟩
  | capture (isValue : operand.IsValue) (cut : HandlerCut requested stack captured tail handler) :
      AnnotationOrCapture ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩

/-- Reuse the existing exhaustive typed-current-form and canonical-value
lemmas. The final alternative is an explicit remaining proof obligation, so
this theorem is not the completed progress theorem. -/
theorem classified_progress
    (before : Prepared operations declarations policy registry tables
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound) :
    (code.IsValue ∧ stack = .nil) ∨
    (∃ nextTables after remaining nextRow,
      NamedAccessStep [] ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Prepared operations declarations policy registry nextTables after output remaining nextRow bound) ∨
    AnnotationOrCapture ⟨code, scope, stack⟩ := by
  obtain ⟨actions, usage, history, requests, closing⟩ := before.actions
  obtain ⟨input, effects, expression, ports, connected⟩ := requests
  cases expression with
  | checked scopeTyped typed =>
      have form := ScopedPortProgress.typed_current_form typed
      cases form with
      | value isValue =>
          rcases value_progress before isValue with terminal | ⟨after, discharged, remaining, step, next, accounting⟩
          · exact Or.inl ⟨isValue, terminal⟩
          · exact Or.inr (Or.inl ⟨_, _, remaining, row, step, next⟩)
      | focus position => exact Or.inr (Or.inr (.focus position))
      | bind isValue =>
          obtain ⟨after, remaining, nextRow, step, next, accounting, included⟩ := ready_progress before (.bind isValue)
          exact Or.inr (Or.inl ⟨_, _, remaining, nextRow, step, next⟩)
      | app functionValue argumentValue => cases typed with
          | app function argument available =>
              obtain ⟨parameter, body, same⟩ := ScopedPorts.typed_function_value function functionValue
              subst_vars
              obtain ⟨after, remaining, nextRow, step, next, accounting, included⟩ := ready_progress before (.app argumentValue)
              exact Or.inr (Or.inl ⟨_, _, remaining, nextRow, step, next⟩)
      | branch isValue => cases typed with
          | branch condition yes no =>
              obtain ⟨flag, same⟩ := ScopedPorts.typed_boolean_value condition isValue
              subst_vars
              obtain ⟨after, remaining, nextRow, step, next, accounting, included⟩ := ready_progress before .branch
              exact Or.inr (Or.inl ⟨_, _, remaining, nextRow, step, next⟩)
      | request isValue =>
          rcases request_selection before isValue with ⟨after, nextRow, step, next, included⟩ | ⟨capture, tail, handler, cut⟩
          · exact Or.inr (Or.inl ⟨_, _, demand, nextRow, step, next⟩)
          · exact Or.inr (Or.inr (.capture isValue cut))
      | handler =>
          obtain ⟨handler, table, fresh, step, next⟩ := handler_progress before
          exact Or.inr (Or.inl ⟨_, _, demand, row, step, next⟩)
      | resume isValue =>
          obtain ⟨after, owner, remaining, step, next, accounting⟩ := resume_progress before isValue
          exact Or.inr (Or.inl ⟨_, after, remaining, row, step, next⟩)
      | discard =>
          obtain ⟨after, owner, remaining, step, next, accounting⟩ := discard_progress before
          exact Or.inr (Or.inl ⟨_, after, remaining, row, step, next⟩)
      | resource isValue =>
          obtain ⟨identity, payload, answer, same, step, next⟩ := resource_progress before isValue
          exact Or.inr (Or.inl ⟨_, _, demand, row, step, next⟩)
      | cleanup isValue => exact Or.inr (Or.inr (.cleanup isValue))

end Ash.OneShot.DeclaredClosingInvariant

#print axioms Ash.OneShot.DeclaredClosingInvariant.resume_owner
#print axioms Ash.OneShot.DeclaredClosingInvariant.resume_progress
#print axioms Ash.OneShot.DeclaredClosingInvariant.classified_progress
