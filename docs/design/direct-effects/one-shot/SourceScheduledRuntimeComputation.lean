import SourceScheduledRuntimeControl

/-! Ready ordinary computation reuses the established bind, beta and branch
source proofs. The runtime join retains their actual successor and checked row. -/
namespace Ash.OneShot.SourceScheduledExecution
open ScopedExpressions ScopedExecution
open RecursiveExpressions (Ready ready_not_focus ready_not_value)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

theorem ready_step_preserves
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside scope code stack forest output demand row evidence)
    (ready : Ready code) (step : RawStep ⟨code, scope, stack⟩ next created completed) :
    ∃ remaining nextRow,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside next.scope next.expression next.stack forest output remaining nextRow evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ next.stack = stack ∧ created = [] ∧ completed = [] := by
  cases step with
  | focus plain focus tail => exact False.elim (ready_not_focus ready focus)
  | plug plain value closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveHandler handler value closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveCell identity payload answer savedScope scope value closed tail => exact False.elim (ready_not_value ready closed.1)
  | startCleanup action saved closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveClause ticket answer value closed scope caller tail => exact False.elim (ready_not_value ready closed.1)
  | bind parameter value body scope tail closed environmentReady =>
      exact ⟨_, _, SourceScheduledState.bind_preserves state closed, .refl _, .refl _, rfl, rfl, rfl⟩
  | beta parameter body value scope tail closed closureReady =>
      exact ⟨_, _, SourceScheduledState.beta_preserves state closed, .refl _, .refl _, rfl, rfl, rfl⟩
  | ifTrue yes no scope tail =>
      obtain ⟨remaining, nextRow, checked, same, included⟩ := SourceScheduledEntries.branch_preserves state
      exact ⟨remaining, nextRow, checked, same, included, rfl, rfl, rfl⟩
  | ifFalse yes no scope tail =>
      obtain ⟨remaining, nextRow, checked, same, included⟩ := SourceScheduledEntries.branch_preserves state
      exact ⟨remaining, nextRow, checked, same, included, rfl, rfl, rfl⟩
  | enterHandler | enterCell | enterCleanup | finishCleanup | capture | resume | discard | finishClose | retire | readCell | writeCell => cases ready

variable [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Every supplied ready-computation step preserves the scheduled invariant.
The successor is checked by the existing source and result proofs, rather than
selected by a lower-level progress theorem. -/
theorem ready_preserves
    (before : Run operations declarations policy contracts registry tables families required annotations state forest output demand row bound evidence)
    (ready : Ready state.execution.configuration.expression)
    (raw : RawStep state.execution.configuration after [] []) :
    ∃ remaining nextRow,
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] []) forest output remaining nextRow bound evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨actions, usage, history, shared, retained⟩ := before.actions
  obtain ⟨remaining, nextRow, next, accounting, included, sameStack, noCreated, noCompleted⟩ :=
    ready_step_preserves shared ready raw
  have results := DeclaredExecution.ready_step_results before.current.results ready raw
  have syntaxChecks (code : Code) (checked : Ready code) :
      AccessChecks ⟨code, state.execution.configuration.scope, state.execution.configuration.stack⟩ [] ∧
      enteredActivations ⟨code, state.execution.configuration.scope, state.execution.configuration.stack⟩ after = [] := by
    constructor
    · apply ScopedPortJoint.ordinary_access_checks (ready_not_value checked)
      · cases checked <;> intro requested operation operand impossible <;> cases impossible
      · cases checked <;> intro binder impossible <;> cases impossible
    · cases checked <;> rfl
  obtain ⟨checks, noEntry⟩ := syntaxChecks _ ready
  have freshOwners : (state.execution.issued ++ []).Nodup := by
    simpa [RunState.erase] using before.current.ledger.2
  have freshHandlers : (state.activations ++ enteredActivations state.execution.configuration after).Nodup := by
    simpa only [noEntry, List.append_nil] using before.current.names.unique
  refine ⟨remaining, nextRow, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_, accounting, included⟩
  apply assemble_entry before.coherent before.current raw freshOwners freshHandlers checks usage history before.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil] using results
  · rfl
  · simp

/-- Progress chooses a raw source step and reuses universal preservation for
that step. -/
theorem ready_progress
    (before : Run operations declarations policy contracts registry tables families required annotations state forest output demand row bound evidence)
    (ready : Ready state.execution.configuration.expression) :
    ∃ after remaining nextRow,
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] []) forest output remaining nextRow bound evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨after, _, _, raw, _⟩ := DeclaredSourceStates.ready_preserves before.current.source ready
  exact ⟨after, ready_preserves before ready raw⟩


end Ash.OneShot.SourceScheduledExecution

#print axioms Ash.OneShot.SourceScheduledExecution.ready_step_preserves
#print axioms Ash.OneShot.SourceScheduledExecution.ready_preserves
#print axioms Ash.OneShot.SourceScheduledExecution.ready_progress
