import DeclaredSharedComputation

/-! A returned value has no immediate requests, so existing source-value
transport supplies a shared current annotation. This connects the existing
recomposition and builtin proofs without a new source or execution induction.
-/
namespace Ash.OneShot.DeclaredSourceInterfaces
open ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements Checked)

theorem value_state
    (checked : DeclaredSourceStates.CheckedState operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue)
    (connected : ScopedActionInterfaces.ConfigurationConnected operations.ports contracts.ports actions world
      ⟨value, scope, stack⟩ output.port []) :
    State operations policy contracts tables actions world outside scope value stack output demand row := by
  obtain ⟨input, requirements, records, disposals, summary, ⟨ticket, scopeTyped⟩,
    pending, closing, unique, evaluated, accepted⟩ := DeclaredSourceStates.value_pending checked isValue
  obtain ⟨otherInput, effects, expression, ports, caller⟩ := connected
  have current : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
      ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables stack)) [] :=
    Checked.request (row := []) (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  exact .checked (DeclaredSourceValues.expression summary _) scopeTyped pending closing unique
    (by simpa only [List.nil_append] using Checked.sequence current evaluated) accepted rfl
    (ScopedActionInterfaces.input_weaken caller (List.nil_subset _))

/-- At a value, the prior invariant already supplies the shared witness.
This does not assert such a converse for arbitrary current expressions. -/
theorem prepared_value_run
    (before : DeclaredClosingInvariant.Prepared operations declarations policy registry tables state output demand row bound)
    (isValue : state.execution.configuration.expression.IsValue) :
    Run operations declarations policy registry tables state output demand row bound := by
  obtain ⟨actions, usage, history, connected, retained⟩ := before.actions
  exact ⟨before.current, actions, usage, history, value_state before.current.source isValue connected, retained⟩

private theorem resume_result_value
    (raw : RawStep before after created discharged)
    (same : before.expression = .resume binder value) (isValue : value.IsValue) :
    after.expression.IsValue := by
  cases raw <;> try cases same
  all_goals try
    have impossible : ClosedValue (.resume binder value) := by assumption
    cases impossible.1
  case focus plain tail focused =>
    generalize position : plain.context = context at focused
    cases focused with
    | resume notValue => exact False.elim (notValue isValue)
  case resume => assumption

private theorem discard_result_value
    (raw : RawStep before after created discharged)
    (same : before.expression = .discard binder) : after.expression.IsValue := by
  cases raw <;> try cases same
  all_goals try
    have impossible : ClosedValue (.discard binder) := by assumption
    cases impossible.1
  case focus plain tail focused => cases focused
  case discard => trivial

private theorem builtin_result_value
    (raw : RawStep before after [] [])
    (same : before.expression = .perform effect operation operand) (isValue : operand.IsValue) :
    after.expression.IsValue := by
  have ordinary := ScopedPortProgress.nonallocating_request_is_ordinary raw same isValue
  cases ordinary with
  | bind | beta | ifTrue | ifFalse => cases same
  | read | write => trivial

theorem resume_progress
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : value.IsValue) :
    ∃ after owner remaining,
      NamedAccessStep [] ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Run operations declarations policy registry tables after output remaining row bound ∧
      demand = owner :: remaining := by
  obtain ⟨after, owner, remaining, step, next, accounting⟩ :=
    DeclaredClosingInvariant.resume_progress before.prepared isValue
  obtain ⟨created, discharged, raw, issuedSame, completedSame, fresh⟩ := DeclaredClosingInvariant.named_event_parts step
  exact ⟨after, owner, remaining, step, prepared_value_run next (resume_result_value raw rfl isValue), accounting⟩

theorem discard_progress
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound) :
    ∃ after owner remaining,
      NamedAccessStep [] ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Run operations declarations policy registry tables after output remaining row bound ∧
      demand = owner :: remaining := by
  obtain ⟨after, owner, remaining, step, next, accounting⟩ := DeclaredClosingInvariant.discard_progress before.prepared
  obtain ⟨created, discharged, raw, issuedSame, completedSame, fresh⟩ := DeclaredClosingInvariant.named_event_parts step
  exact ⟨after, owner, remaining, step, prepared_value_run next (discard_result_value raw rfl), accounting⟩

theorem builtin_step_preserves
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      output demand row bound)
    (isValue : operand.IsValue)
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩ after [] []) :
    ∃ nextRow,
      let state : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] []) output demand nextRow bound ∧ nextRow.Sublist row := by
  obtain ⟨nextRow, step, next, included⟩ := DeclaredClosingInvariant.builtin_step_preserves before.prepared isValue raw
  exact ⟨nextRow, step, prepared_value_run next (builtin_result_value raw rfl isValue), included⟩

theorem request_selection
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      output demand row bound)
    (isValue : operand.IsValue) :
    (∃ after nextRow,
      let state : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] []) output demand nextRow bound ∧ nextRow.Sublist row) ∨
    (∃ capture tail handler, HandlerCut requested stack capture tail handler) := by
  rcases RecursiveRequestProgress.request_selection before.current.signature
      (DeclaredSourceStates.checked_state_erase before.current.source) isValue with
    ⟨after, nextRow, raw, source, included⟩ | selected
  · obtain ⟨nextRow, step, next, included⟩ := builtin_step_preserves before isValue raw
    exact Or.inl ⟨after, nextRow, step, next, included⟩
  · exact Or.inr selected

/-- Covers every actual returned-value transition whose successor is also a
value. Plugging a context and starting a callback need separate source proofs. -/
theorem value_step_preserves
    (before : Run operations declarations policy registry tables state output demand row bound)
    (isValue : state.execution.configuration.expression.IsValue)
    (raw : RawStep state.execution.configuration after created discharged)
    (afterValue : after.expression.IsValue) :
    ∃ remaining,
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after created discharged) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after created discharged) output remaining row bound ∧
      demand = RecursiveCompletion.retiredTickets discharged ++ remaining ∧ created = [] := by
  obtain ⟨remaining, step, next, accounting, empty⟩ := DeclaredExecution.value_step_preserves before.current isValue raw
  have prepared := DeclaredClosingInvariant.value_preserves_prepared before.prepared isValue step next
  exact ⟨remaining, step, prepared_value_run prepared afterValue, accounting, empty⟩

end Ash.OneShot.DeclaredSourceInterfaces

#print axioms Ash.OneShot.DeclaredSourceInterfaces.value_state
#print axioms Ash.OneShot.DeclaredSourceInterfaces.prepared_value_run
#print axioms Ash.OneShot.DeclaredSourceInterfaces.resume_progress
#print axioms Ash.OneShot.DeclaredSourceInterfaces.discard_progress
#print axioms Ash.OneShot.DeclaredSourceInterfaces.builtin_step_preserves
#print axioms Ash.OneShot.DeclaredSourceInterfaces.request_selection
#print axioms Ash.OneShot.DeclaredSourceInterfaces.value_step_preserves
