import SourceScheduledValues
import SourceScheduledPhaseRestriction

/-! Retirement consumes one owner while preserving the actual retained source
plans. Phase restriction discharges the pending checks; the existing ownership
trace and requirement equations account for consumption. -/
namespace Ash.OneShot.SourceScheduledValues
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)
open RecursiveCompletion (retiredTickets)
open OwnerPhaseTransitions (available spendAll Trace)

/-- Retiring a ticket changes availability without invalidating the retained
stack's source checks. No check on the successor is assumed. -/
theorem retire
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope .unit (.push (.retiring owner) tail) wholeForest output demand row evidence) :
    ∃ remaining, demand = owner :: remaining ∧
      (∃ rest : SourceScheduledSavedPlans.Saved,
        SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
          scope .unit tail rest.forest output remaining row evidence) ∧
      Trace (available (ownedTickets (.push (.retiring owner) tail))) [owner] (available (ownedTickets tail)) := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, ⟨ticket, scopeTyped⟩, pending, closing,
    templates, matched, unique, checked, accepted⟩ := value_pending state trivial
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
    | retiring known interface => cases matched with
      | running matched =>
        obtain ⟨firstRow, tailRow, firstCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
        have ready := OwnerPhaseTransitions.trace_available (RecursiveRequirements.checked_trace firstCheck) owner List.mem_cons_self
        have firstEmpty : firstRow = [] := by
          have evaluated := RecursiveRequirements.checked_complete firstCheck
          simpa only [Requirements.prepend, RecursiveClosing.evaluate_retire, if_pos ready, Option.some.injEq] using evaluated.symm
        subst firstRow
        have phases := OwnerPhaseTransitions.spend_available_cons (List.nodup_cons.mp unique).1
        have next := tailCheck
        simp only [spendAll, ownedTickets, phases] at next
        have restricted := rest.phase_restrict (after := available (ownedTickets tail)) (by
          intro name member _
          have live : name ∈ tail.erase.liveTickets := by
            simpa only [SourceScheduledPhaseRestriction.owners_append, SourceDependencyOwners.owners,
              List.append_nil, SourceDependencyOwners.realized_owners rest.source.source.matches.realizes] using member
          exact if_pos (recursive_live_tickets_owned tail live))
        have templatesAfter := templates.transport (nextRoot := tail)
          (fun _ _ known => known) (fun _ _ known => known)
          (fun _ _ located => by cases located with | push inner => exact inner)
        refine ⟨_, rfl, ?_, .cons ready ?_⟩
        · exact ⟨⟨_, _, _⟩, value_configuration .unit trivial scopeTyped restricted closing templatesAfter matched
            (List.nodup_cons.mp unique).2 (by simpa only [same, List.nil_append] using next) accepted⟩
        · simpa only [ownedTickets, phases] using (Trace.nil (before := available (ownedTickets tail)))

/-- All returned-value transitions preserve the checked scheduled state and
account exactly for retired owners. This includes ticket retirement. -/
theorem value_step_preserves
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope value stack forest output demand row evidence)
    (isValue : value.IsValue)
    (step : RawStep ⟨value, scope, stack⟩ next created completed) :
    ∃ remaining, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack nextForest.forest output remaining row evidence ∧
      demand = retiredTickets completed ++ remaining ∧ created = [] ∧
      Trace (available (ownedTickets stack)) (retiredTickets completed) (available (ownedTickets next.stack)) := by
  cases step <;> try cases isValue
  case focus => exact False.elim (ScopedPorts.focus_is_not_value (by assumption) isValue)
  case plug =>
    obtain ⟨rest, dependencies, contextPlan, same, next⟩ := plug_preserves state (by assumption)
    exact ⟨_, rest, next, rfl, rfl, .nil⟩
  case leaveHandler =>
    obtain ⟨rest, next⟩ := leave_handler state (show ClosedValue _ from by assumption).1
    exact ⟨_, rest, next, rfl, rfl, .nil⟩
  case leaveCell =>
    obtain ⟨rest, next⟩ := leave_cell state (show ClosedValue _ from by assumption).1
    exact ⟨_, rest, next, rfl, rfl, .nil⟩
  case startCleanup =>
    obtain ⟨rest, next⟩ := start_cleanup state (by assumption)
    exact ⟨_, ⟨_, _, .running rest.forest⟩, next, rfl, rfl, .nil⟩
  case finishCleanup =>
    obtain ⟨rest, next⟩ := finish_cleanup state
    exact ⟨_, rest, next, rfl, rfl, .nil⟩
  case leaveClause =>
    obtain ⟨rest, next⟩ := leave_clause state (show ClosedValue _ from by assumption).1
    exact ⟨_, rest, next, rfl, rfl, .nil⟩
  case finishClose =>
    obtain ⟨rest, next⟩ := finish_close state
    exact ⟨_, rest, next, rfl, rfl, .nil⟩
  case retire =>
    obtain ⟨remaining, same, ⟨rest, preserved⟩, transition⟩ := retire state
    exact ⟨remaining, rest, preserved, same, rfl, transition⟩

end Ash.OneShot.SourceScheduledValues

#print axioms Ash.OneShot.SourceScheduledValues.retire
#print axioms Ash.OneShot.SourceScheduledValues.value_step_preserves
