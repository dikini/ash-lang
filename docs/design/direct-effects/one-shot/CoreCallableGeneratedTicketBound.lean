import CoreCallableGeneratedCleanupCompletion
namespace Ash.OneShot.CoreCallableGeneratedTicketBound
open ScopedExpressions ScopedExecution CoreCallableGeneratedChronology
open CoreCallableGeneratedCleanupCompletion CoreCallableReachableResume
open CoreCallableCleanupReachableTransport CoreCallableRunningOccurrence
open CoreTicketHistory

/-- A finite positive matching may contain more than one target step. Its
name bound sums exactly the named allocation ledger, including dormant names. -/
private theorem trace_names (trace : CoreUnwindRelation.Trace before after created discharged)
    (dynamicTicket : Nat) :
    after.stack.erase.ticketNames.count dynamicTicket ≤
      before.stack.erase.ticketNames.count dynamicTicket + created.count (.ticket dynamicTicket) := by
  induction trace with
  | refl => simp
  | next step rest ih =>
    have edge := step.ticket_name_bound dynamicTicket
    simp only [List.count_append]
    omega

private theorem issued_count (created : List Owner) (dynamicTicket : Nat) :
    (issuedTickets created).count dynamicTicket = created.count (.ticket dynamicTicket) := by
  induction created with
  | nil => rfl
  | cons owner rest ih =>
    simp only [issuedTickets] at ih
    cases owner <;> simp [issuedTickets, List.count_cons, ih]

/-- Event coupling is derived separately by each actual named producer. Only
capture emits a captured event; resume and spent return retain historical names. -/
theorem Operation.ticket_events {graph : CoreSyntax.Graph} {before after : Endpoint graph}
    (operation : Operation before after created discharged) :
    capturedTickets after.state.observations =
      capturedTickets before.state.observations ++ issuedTickets created := by
  cases operation with
  | bind input => simp [bind_result, issuedTickets, capturedTickets]
  | beta input => simp [beta_result, issuedTickets]
  | bindReturn input => simp [bind_return_result, issuedTickets]
  | handler input => simp [handler_result, issuedTickets, capturedTickets]
  | handlerReturn input => simp [handler_return_result, issuedTickets]
  | literal input => simp [literal_result, issuedTickets, capturedTickets]
  | entry input => simp [entry_result, issuedTickets, capturedTickets]
  | swap input => simp [swap_result, issuedTickets]
  | tuple input => simp [tuple_result, issuedTickets]
  | capture input => simp [capture_result, CoreGeneralCaptureResume.captureAfter, issuedTickets, capturedTickets]
  | resume input => simp [resume_result, CoreGeneralCaptureResume.resumeAfter, issuedTickets, capturedTickets]
  | spentReturn input => simp [spent_return_result, CoreGeneralRestoration.observedState, issuedTickets, capturedTickets]

/-- The operation's actual positive/ranked matching and actual observation
receipt produce the current bound. No successor bound enters this interface. -/
theorem Operation.ticket_bound {graph : CoreSyntax.Graph} {before after : Endpoint graph}
    (operation : Operation before after created discharged)
    (bounded : TicketBound before.state before.point.machine.stack) :
    TicketBound after.state after.point.machine.stack := by
  intro dynamicTicket
  have names := trace_names operation.actual.2.target_trace dynamicTicket
  have previous := bounded dynamicTicket
  rw [Operation.ticket_events operation, List.count_append, issued_count]
  omega

/-- The original suffix bound is a past/current start obligation. The actual
cleanup-start edge adds no captured event or target ticket. -/
theorem started_ticket_bound
    (start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget)
    (bounded : TicketBound (start_before start).state originalTarget) :
    TicketBound (started start).state (started start).point.machine.stack := by
  simpa [TicketBound, started, start_before, Endpoint.point, CoreCleanupRunFrames.attach,
    Stack.erase, ExecFrame.erase, Stack.append, LexicalUnwind.Machine.stack, CoreGeneralRestoration.startedState,
    CoreGeneralRestoration.returnedState, Control.ticketNames, capturedTickets] using bounded

/-- Every intermediate endpoint of this SAME-start generated execution retains
all its dormant and spent ticket names within actual capture history. -/
theorem Generated.ticket_bound
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (generated : Generated start current count created discharged)
    (initial : TicketBound (start_before start).state originalTarget) :
    TicketBound current.state current.point.machine.stack := by
  induction generated with
  | initial => exact started_ticket_bound start initial
  | next earlier operation ih => exact Operation.ticket_bound operation ih

/-- Strict focus contributes a prefix. Removing it only decreases ticket counts. -/
theorem Generated.lexical_ticket_bound
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (generated : Generated start current count created discharged)
    (initial : TicketBound (start_before start).state originalTarget) :
    TicketBound current.state current.lexical := by
  intro dynamicTicket
  have full := Generated.ticket_bound generated initial dynamicTicket
  simp only [Endpoint.point, CoreCleanupRunFrames.attach, LexicalUnwind.Machine.stack,
    erase_append, ticketNames_append, List.count_append] at full
  omega

/-- The generated producer supplies the formerly external current TicketBound.
Activation's current scope guards remain those of the retained completion API. -/
theorem finish_current_ownership_generated
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {generated : Generated start current count created discharged}
    (input : FinishInput generated)
    (initial : TicketBound (start_before start).state originalTarget) :
    CurrentOwnership graph cleanupOwners (finish_result input).after.state data.scope input.head.tail.target :=
  finish_current_ownership input (Generated.lexical_ticket_bound generated initial)

/-- A completed outcome exposes restored ownership with its bound produced by
SAME-start chronology. Only the original pre-start suffix bound remains input. -/
theorem Completed.current_ownership
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {after : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (completed : Completed start after count created discharged)
    (initial : TicketBound (start_before start).state originalTarget) :
    CurrentOwnership graph cleanupOwners after.state data.scope after.lexical := by
  cases completed with
  | finish generated input => exact finish_current_ownership_generated input initial

#print axioms Operation.ticket_events
#print axioms Operation.ticket_bound
#print axioms started_ticket_bound
#print axioms Generated.ticket_bound
#print axioms Generated.lexical_ticket_bound
#print axioms finish_current_ownership_generated
#print axioms Completed.current_ownership
end Ash.OneShot.CoreCallableGeneratedTicketBound
