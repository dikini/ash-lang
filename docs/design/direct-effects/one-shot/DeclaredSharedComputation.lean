import DeclaredSourceInterfaces

/-! Ordinary computation retains the shared current-source annotation.
Substitution and branch selection reuse the existing hereditary source proofs;
runtime preservation uses the same actual step as the source witness.
-/
namespace Ash.OneShot.DeclaredSourceInterfaces
open ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements Checked evaluate)
open RecursiveExpressions (Ready ready_not_focus ready_not_value)

private theorem replace_current {requirements : Requirements currentDemand}
    (replacement : DeclaredSources.Expression operations policy contracts world allowed nextScope Environment.empty
      next input currentDemand reduced)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports nextScope nextTicket)
    (pending : DeclaredSourceFrames.Segment operations policy contracts tables world stack input output pendingDemand pendingRequirements records)
    (closing : DeclaredSourceClosing.Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
      (.sequence (requirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row)
    (accepted : ProtectionContracts.checkFootprint outside row = true)
    (accounting : demand = currentDemand ++ pendingDemand)
    (connected : ScopedActionInterfaces.Connected operations.ports contracts.ports actions world stack allowed [])
    (same : ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements) :
    State operations policy contracts tables actions world outside nextScope next stack output demand row := by
  refine .checked replacement scopeTyped pending closing unique ?_ accepted accounting connected
  apply RecursiveRequirements.evaluate_sound
  have original := RecursiveRequirements.checked_complete checked
  simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend] at original ⊢
  rw [same]
  exact original

theorem bind_preserves
    (state : State operations policy contracts tables actions world outside scope (.bind parameter value body) stack output demand row)
    (closed : ClosedValue value) :
    State operations policy contracts tables actions world outside scope (body.subst parameter value) stack output demand row := by
  cases state with
  | checked current scopeTyped pending closing unique checked accepted accounting connected =>
      obtain ⟨reduced, replacement, same⟩ := DeclaredSourceExpressions.bind_expression current closed
      exact replace_current replacement scopeTyped pending closing unique checked accepted accounting connected same

theorem beta_preserves
    (state : State operations policy contracts tables actions world outside scope (.app (.lambda parameter body) value) stack output demand row)
    (closed : ClosedValue value) :
    State operations policy contracts tables actions world outside .none (body.subst parameter value) stack output demand row := by
  cases state with
  | checked current scopeTyped pending closing unique checked accepted accounting connected =>
      obtain ⟨reduced, replacement, same⟩ := DeclaredSourceExpressions.beta_expression current closed
      exact replace_current replacement .none pending closing unique checked accepted accounting connected same

theorem branch_preserves
    (state : State operations policy contracts tables actions world outside scope (.branch (.boolean flag) yes no) stack output demand row) :
    ∃ remaining nextRow,
      State operations policy contracts tables actions world outside scope
        (if flag then yes else no) stack output remaining nextRow ∧ demand.Perm remaining ∧ nextRow.Sublist row := by
  cases state with
  | checked current scopeTyped pending closing unique checked accepted accounting connected =>
      subst demand
      obtain ⟨remaining, reduced, replacement, sameDemand, selected⟩ := DeclaredSourceExpressions.branch_expression current
      obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      have activeCheck := RecursiveRequirements.checked_prepend_iff.mp currentCheck
      obtain ⟨nextRow, nextCheck, included⟩ := selected _ _ _ _ activeCheck
      have nextPending := pendingCheck
      rw [RecursiveExpressions.spend_permutation sameDemand] at nextPending
      have includedWhole := included.append (List.Sublist.refl pendingRow)
      exact ⟨_, _, .checked replacement scopeTyped pending closing unique
        (.sequence (RecursiveRequirements.checked_prepend_iff.mpr nextCheck) nextPending)
        (ProtectionContracts.checked_footprint_subset accepted includedWhole.subset) rfl connected,
        sameDemand.append_right _, includedWhole⟩

theorem ready_step_preserves
    (state : State operations policy contracts tables actions world outside scope code stack output demand row)
    (ready : Ready code) (step : RawStep ⟨code, scope, stack⟩ next created completed) :
    ∃ remaining nextRow,
      State operations policy contracts tables actions world outside next.scope next.expression next.stack output remaining nextRow ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ next.stack = stack ∧ created = [] ∧ completed = [] := by
  cases step with
  | focus plain focus tail => exact False.elim (ready_not_focus ready focus)
  | plug plain value closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveHandler handler value closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveCell identity payload answer savedScope scope value closed tail => exact False.elim (ready_not_value ready closed.1)
  | startCleanup action saved closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveClause ticket answer value closed scope caller tail => exact False.elim (ready_not_value ready closed.1)
  | bind parameter value body scope tail closed environmentReady =>
      exact ⟨_, _, bind_preserves state closed, .refl _, .refl _, rfl, rfl, rfl⟩
  | beta parameter body value scope tail closed closureReady =>
      exact ⟨_, _, beta_preserves state closed, .refl _, .refl _, rfl, rfl, rfl⟩
  | ifTrue yes no scope tail =>
      obtain ⟨remaining, nextRow, checked, same, included⟩ := branch_preserves state
      exact ⟨remaining, nextRow, checked, same, included, rfl, rfl, rfl⟩
  | ifFalse yes no scope tail =>
      obtain ⟨remaining, nextRow, checked, same, included⟩ := branch_preserves state
      exact ⟨remaining, nextRow, checked, same, included, rfl, rfl, rfl⟩
  | enterHandler | enterCell | enterCleanup | finishCleanup | capture | resume | discard | finishClose | retire | readCell | writeCell => cases ready

/-- The runtime proof supplies the actual step and result contract. The shared
source proof supplies its own checked row and demand for that same successor. -/
theorem ready_progress
    (before : Run operations declarations policy registry tables state output demand row bound)
    (ready : Ready state.execution.configuration.expression) :
    ∃ after remaining nextRow,
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] []) output remaining nextRow bound ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨after, oldDemand, oldRow, step, current, oldAccounting, oldIncluded⟩ :=
    DeclaredExecution.ready_progress before.current ready
  obtain ⟨created, discharged, raw, issuedSame, completedSame, freshOwners⟩ := DeclaredClosingInvariant.named_event_parts step
  have createdSame : [] = created := List.append_cancel_left issuedSame
  have dischargedSame : [] = discharged := List.append_cancel_right completedSame
  subst created
  subst discharged
  obtain ⟨actions, usage, history, shared, retained⟩ := before.actions
  obtain ⟨remaining, nextRow, next, accounting, included, sameStack, noCreated, noCompleted⟩ :=
    ready_step_preserves shared ready raw
  refine ⟨after, remaining, nextRow, step, ?_, accounting, included⟩
  apply assemble_entry before.current raw freshOwners current.names.unique step.checks usage history retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

end Ash.OneShot.DeclaredSourceInterfaces

#print axioms Ash.OneShot.DeclaredSourceInterfaces.bind_preserves
#print axioms Ash.OneShot.DeclaredSourceInterfaces.beta_preserves
#print axioms Ash.OneShot.DeclaredSourceInterfaces.branch_preserves
#print axioms Ash.OneShot.DeclaredSourceInterfaces.ready_step_preserves
#print axioms Ash.OneShot.DeclaredSourceInterfaces.ready_progress
