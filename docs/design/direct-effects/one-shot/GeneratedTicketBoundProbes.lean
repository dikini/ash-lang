import CoreCallableGeneratedTicketBound
import GeneratedNestedHandlerProbes
namespace Ash.OneShot.GeneratedTicketBoundProbes
open ScopedExpressions ScopedExecution CoreCallableGeneratedChronology
open CoreCallableGeneratedCleanupCompletion CoreCallableGeneratedTicketBound
open CoreCallableRunningOccurrence CoreCallableReachableResume
open CoreTicketHistory

private def currentOf
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} (_generated : Generated start current count created discharged) : Endpoint graph := current

private def completedOwnership
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {after : Endpoint graph} (_completed : Completed start after count created discharged) : Prop :=
  CurrentOwnership graph cleanupOwners after.state data.scope after.lexical

/-- These are the retained SAME-start generated producers, with no new trace
fixture or substituted result. Their original target suffix is literally nil. -/
theorem nested_capture_bound :
    TicketBound (currentOf Nested.captured_trace).state (currentOf Nested.captured_trace).point.machine.stack :=
  Generated.ticket_bound Nested.captured_trace (TicketBound.empty _)
theorem nested_operand_bound :
    TicketBound (currentOf Nested.clause_operand_trace).state (currentOf Nested.clause_operand_trace).point.machine.stack :=
  Generated.ticket_bound Nested.clause_operand_trace (TicketBound.empty _)
theorem nested_resume_bound :
    TicketBound (currentOf Nested.resumed_trace).state (currentOf Nested.resumed_trace).point.machine.stack :=
  Generated.ticket_bound Nested.resumed_trace (TicketBound.empty _)
theorem nested_return_bound :
    TicketBound (currentOf Nested.nested_returned).state (currentOf Nested.nested_returned).lexical :=
  Generated.lexical_ticket_bound Nested.nested_returned (TicketBound.empty _)
theorem nested_completed_ownership : completedOwnership Nested.nested_completed :=
  Completed.current_ownership Nested.nested_completed (TicketBound.empty _)

theorem nested_capture_name :
    (currentOf Nested.captured_trace).point.machine.stack.erase.ticketNames = [0] := rfl
/-- Resumption consumes ownership but retains the spent historical ticket. -/
theorem nested_spent_name :
    (currentOf Nested.resumed_trace).point.machine.stack.erase.ticketNames = [0] := rfl
theorem nested_spent_capture_history :
    capturedTickets (currentOf Nested.resumed_trace).state.observations = [0] := rfl
/-- Normal spent return removes the name; the actual capture history remains. -/
theorem nested_retired_names :
    (currentOf Nested.nested_returned).lexical.erase.ticketNames = [] := rfl
theorem nested_retired_capture_history :
    capturedTickets (currentOf Nested.nested_returned).state.observations = [0] := rfl

/-- GeneralHistory carriers alone cannot supply the original current bound:
a dormant/spent target name without an actual captured event is rejected. -/
theorem unissued_spent_rejected (graph : CoreSyntax.Graph) (answer : Ty)
    (scope : Execution.Scope) :
    ¬ TicketBound (CoreMachine.initial graph) (.spent 0 answer scope .nil) := by
  intro bounded
  have impossible := bounded 0
  simp [CoreMachine.initial, capturedTickets, Stack.erase, Control.ticketNames] at impossible

#print axioms nested_capture_bound
#print axioms nested_operand_bound
#print axioms nested_resume_bound
#print axioms nested_return_bound
#print axioms nested_completed_ownership
#print axioms nested_capture_name
#print axioms nested_spent_name
#print axioms nested_spent_capture_history
#print axioms nested_retired_names
#print axioms nested_retired_capture_history
#print axioms unissued_spent_rejected
#check Operation.ticket_events
#check Operation.ticket_bound
#check Generated.ticket_bound
#check Generated.lexical_ticket_bound
#check Completed.current_ownership
end Ash.OneShot.GeneratedTicketBoundProbes
