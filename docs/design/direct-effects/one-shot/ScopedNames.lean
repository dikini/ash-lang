import ScopedClosure

/-!
Lifetime handler and ticket naming for scoped execution. Name allocation is
checked independently from resource-name closure, live support, and permissions.
The counted control forest includes dormant captures and retirement markers.
-/

namespace Ash.OneShot.ScopedExecution
open Instantiation ScopedExpressions
open Syntax (UseScope UseState)
open Typing (TicketType)

def enteredActivations (before after : Configuration) : List Nat :=
  match before.expression, after.stack with
  | .handle _ _ _, .push (.handler handler) _ => [handler.activation]
  | _, _ => []

theorem value_enters_no_activation (closed : ClosedValue value) :
    enteredActivations ⟨value, scope, stack⟩ after = [] := by
  have valueForm := closed.1
  cases value <;> simp_all [enteredActivations, Code.IsValue]

theorem focus_enters_no_activation (focus : Focus whole child context) :
    enteredActivations ⟨whole, scope, stack⟩ after = [] := by
  cases focus <;> rfl

/-- Per-name multiplicity bounds for every raw expression transition. These
    bounds do not assume the desired post-state naming invariant. -/
theorem raw_step_name_bounds (step : RawStep before after created discharged)
    (ticket activation : Nat) :
    after.stack.erase.ticketNames.count ticket ≤
      before.stack.erase.ticketNames.count ticket + created.count (.ticket ticket) ∧
    after.stack.erase.activations.count activation ≤
      before.stack.erase.activations.count activation + (enteredActivations before after).count activation := by
  cases step with
  | focus plain focus tail =>
      simp [focus_enters_no_activation focus, Stack.erase, ExecFrame.erase,
        PlainData.erase, Control.ticketNames, Control.activations, Frame.activation]
  | plug plain value closed scope tail =>
      simp [value_enters_no_activation closed, Stack.erase, ExecFrame.erase,
        PlainData.erase, Control.ticketNames, Control.activations, Frame.activation]
  | bind | beta | ifTrue | ifFalse => simp [enteredActivations]
  | enterHandler handler body tail =>
      simp [enteredActivations, Stack.erase, ExecFrame.erase, HandlerData.erase,
        Control.ticketNames, Control.activations, Frame.activation, List.count_cons]
  | leaveHandler handler value closed scope tail =>
      simp [value_enters_no_activation closed, Stack.erase, ExecFrame.erase, HandlerData.erase,
        Control.ticketNames, Control.activations, Frame.activation, List.count_cons]
  | enterCell binder identity payload body scope answer tail instantiationReady =>
      simp [enteredActivations, Stack.erase, ExecFrame.erase,
        Control.ticketNames, Control.activations, Frame.activation]
  | leaveCell identity payload answer savedScope scope value closed tail =>
      simp [value_enters_no_activation closed, Stack.erase, ExecFrame.erase,
        Control.ticketNames, Control.activations, Frame.activation]
  | enterCleanup action body tail =>
      simp [enteredActivations, Stack.erase, ExecFrame.erase, ActionData.erase,
        Control.ticketNames, Control.activations, Frame.activation]
  | startCleanup action saved closed scope tail =>
      simp [value_enters_no_activation closed, Stack.erase, ExecFrame.erase, ActionData.erase,
        Control.ticketNames, Control.activations, Frame.activation]
  | finishCleanup action saved closed scope tail =>
      simp [enteredActivations, Stack.erase, ExecFrame.erase, ActionData.erase,
        Control.ticketNames, Control.activations, Frame.activation]
  | capture requested operation parameter binder owner operand body scope whole cap tail handler
      output cut selected closed ready =>
      rw [handler_cut_reconstructs cut]
      by_cases same : ticket = owner <;>
        simp [enteredActivations, erase_append, Stack.erase, Control.ticketNames,
          Control.activations, List.count_append, List.count_cons, same] <;> omega
  | resume binder owner scope callerScope input answer front cap tail value closed resolved =>
      simp [enteredActivations, erase_append, Stack.erase, Control.ticketNames,
        Control.activations, List.count_append, List.count_cons]
      omega
  | discard binder owner closeId scope callerScope input answer front cap tail plan resolved build =>
      have erasedBuild : rawPlan cap.erase = some (plan.map CloseEntry.erase) := by
        rw [← make_plan_erases, build]
        rfl
      have bound := Execution.raw_plan_ticket_name_bound erasedBuild ticket
      simp [enteredActivations, erase_append, Stack.erase, close_control_erases,
        ExecFrame.erase, closeFrame, Control.ticketNames, Control.activations,
        Frame.activation, List.count_append, List.count_cons]
      omega
  | leaveClause owner answer value closed scope callerScope tail =>
      simp [value_enters_no_activation closed, Stack.erase, Control.ticketNames,
        Control.activations, List.count_cons]
  | finishClose identity scope callerScope tail =>
      simp [enteredActivations, Stack.erase, ExecFrame.erase, closeFrame,
        Control.ticketNames, Control.activations, Frame.activation]
  | retire owner scope tail =>
      simp [enteredActivations, Stack.erase, ExecFrame.erase, CloseItem.frame,
        Control.ticketNames, Control.activations, Frame.activation, List.count_cons]
  | readCell identity payload scope before after selected =>
      simp [enteredActivations, cell_update_erases selected]
  | writeCell identity old new scope before after selected =>
      simp [enteredActivations, cell_update_erases selected]

/-- Counts include spent names, dormant captures and retirement frames.
    Historical allocation bounds prevent duplicate occurrences when combined
    with fresh owner allocation and fresh handler-activation history. -/
structure NameHistory (state : RunState) (activations : List Nat) : Prop where
  tickets : ∀ ticket, state.configuration.stack.erase.ticketNames.count ticket ≤ state.issued.count (.ticket ticket)
  handlers : ∀ activation, state.configuration.stack.erase.activations.count activation ≤ activations.count activation
  unique : activations.Nodup

theorem history_gives_distinct_names (history : NameHistory state activations)
    (ledger : Ledger state.erase) : DistinctNames state.configuration.stack.erase := by
  constructor
  · exact List.nodup_iff_count.mpr fun ticket =>
      Nat.le_trans (history.tickets ticket) (List.nodup_iff_count.mp ledger.2 (.ticket ticket))
  · exact List.nodup_iff_count.mpr fun activation =>
      Nat.le_trans (history.handlers activation) (List.nodup_iff_count.mp history.unique activation)

theorem raw_step_preserves_name_history
    (step : RawStep before.configuration after created discharged)
    (history : NameHistory before activations)
    (fresh : (activations ++ enteredActivations before.configuration after).Nodup) :
    NameHistory ⟨after, before.issued ++ created, discharged ++ before.completed⟩
      (activations ++ enteredActivations before.configuration after) := by
  constructor
  · intro ticket
    have bound := (raw_step_name_bounds step ticket 0).1
    have previous := history.tickets ticket
    simp only [List.count_append]
    omega
  · intro activation
    have bound := (raw_step_name_bounds step 0 activation).2
    have previous := history.handlers activation
    simp only [List.count_append]
    omega
  · exact fresh

structure NamedState where
  execution : RunState
  activations : List Nat

/-- Handler activations are allocated freshly against history, alongside the
    existing fresh ownership events. Other operational rules are unchanged. -/
inductive NamedStep : NamedState → NamedState → Prop where
  | event (before : NamedState) (after : Configuration) (created discharged : List Owner)
      (step : RawStep before.execution.configuration after created discharged)
      (freshOwners : (before.execution.issued ++ created).Nodup)
      (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup) :
      NamedStep before ⟨⟨after, before.execution.issued ++ created, discharged ++ before.execution.completed⟩,
        before.activations ++ enteredActivations before.execution.configuration after⟩

theorem named_step_executes (step : NamedStep before after) :
    RunStep before.execution after.execution := by
  cases step with
  | event after created discharged raw freshOwners freshHandlers =>
      exact .event before.execution _ _ _ raw freshOwners

theorem named_step_preserves (step : NamedStep before after)
    (ledger : Ledger before.execution.erase) (history : NameHistory before.execution before.activations) :
    Ledger after.execution.erase ∧ NameHistory after.execution after.activations := by
  constructor
  · exact run_step_preserves_ledger (named_step_executes step) ledger
  · cases step with
    | event after created discharged raw freshOwners freshHandlers =>
        exact raw_step_preserves_name_history raw history freshHandlers

inductive NamedSteps : NamedState → NamedState → Prop where
  | refl (state : NamedState) : NamedSteps state state
  | next (first : NamedStep before middle) (rest : NamedSteps middle after) : NamedSteps before after

theorem named_steps_execute (steps : NamedSteps before after) :
    RunSteps before.execution after.execution := by
  induction steps with
  | refl => exact .refl _
  | next first rest ih => exact .next (named_step_executes first) ih

theorem named_steps_preserve (steps : NamedSteps before after)
    (ledger : Ledger before.execution.erase) (history : NameHistory before.execution before.activations) :
    Ledger after.execution.erase ∧ NameHistory after.execution after.activations := by
  induction steps with
  | refl => exact ⟨ledger, history⟩
  | next first rest ih =>
      obtain ⟨middleLedger, middleHistory⟩ := named_step_preserves first ledger history
      exact ih middleLedger middleHistory

theorem named_steps_activation_history_mono (steps : NamedSteps before after) :
    before.activations ⊆ after.activations := by
  induction steps with
  | refl => exact fun _ member => member
  | next first rest ih =>
      cases first with
      | event middle created discharged raw freshOwners freshHandlers =>
          exact fun _ member => ih (List.mem_append_left _ member)

theorem named_step_never_reallocates (step : NamedStep before after)
    (previous : activation ∈ before.activations) :
    activation ∉ enteredActivations before.execution.configuration after.execution.configuration := by
  cases step with
  | event after created discharged raw freshOwners freshHandlers =>
      intro newlyEntered
      exact (List.nodup_append.mp freshHandlers).2.2 activation previous activation newlyEntered rfl

theorem named_execution_never_reallocates
    (steps : NamedSteps initial before) (step : NamedStep before after)
    (previous : activation ∈ initial.activations) :
    activation ∉ enteredActivations before.execution.configuration after.execution.configuration :=
  named_step_never_reallocates step (named_steps_activation_history_mono steps previous)

inductive TicketBinding : TicketType → UseScope → Scope → UseState → Stack → Prop where
  | none : TicketBinding .none .none .none .available stack
  | live {front saved tail : Stack} {callerScope : Scope} :
      TicketBinding (.bound binder input answer residual closing)
      (.ticket binder rights) (.ticket binder owner) .available
      (front.append (.live owner input answer saved callerScope tail))
  | spent {front tail : Stack} {callerScope : Scope} :
      TicketBinding (.bound binder input answer residual closing)
      (.ticket binder rights) (.ticket binder owner) .consumed
      (front.append (.spent owner answer callerScope tail))

theorem ticket_binding_occurs
    (binding : TicketBinding ticket useScope (.ticket binder owner) state stack) :
    (owner, state) ∈ stack.erase.ticketStates := by
  cases binding with
  | live => simp [erase_append, Stack.erase, Typing.ticket_states_append, Control.ticketStates]
  | spent => simp [erase_append, Stack.erase, Typing.ticket_states_append, Control.ticketStates]

theorem ticket_binding_state_unique
    (names : stack.erase.ticketNames.Nodup)
    (left : TicketBinding ticket useScope (.ticket binder owner) state stack)
    (right : TicketBinding otherTicket otherUse (.ticket otherBinder owner) otherState stack) :
    state = otherState :=
  Typing.unique_ticket_state_in_list (by simpa only [Typing.ticket_states_names] using names)
    (ticket_binding_occurs left) (ticket_binding_occurs right)

theorem spent_binding_blocks_available
    (names : stack.erase.ticketNames.Nodup)
    (spent : TicketBinding ticket useScope (.ticket binder owner) .consumed stack) :
    ¬ TicketBinding otherTicket otherUse (.ticket otherBinder owner) .available stack := by
  intro available
  have impossible := ticket_binding_state_unique names spent available
  cases impossible

theorem named_execution_has_unique_ticket_state (steps : NamedSteps before after)
    (ledger : Ledger before.execution.erase) (history : NameHistory before.execution before.activations)
    (left : TicketBinding ticket useScope (.ticket binder owner) state after.execution.configuration.stack)
    (right : TicketBinding otherTicket otherUse (.ticket otherBinder owner) otherState after.execution.configuration.stack) :
    state = otherState := by
  obtain ⟨finalLedger, finalHistory⟩ := named_steps_preserve steps ledger history
  exact ticket_binding_state_unique (history_gives_distinct_names finalHistory finalLedger).1 left right

theorem available_binding_owns_ticket
    (binding : TicketBinding ticket useScope (.ticket binder owner) .available stack) :
    Owner.ticket owner ∈ stack.erase.owners := by
  cases binding with
  | live => simp [erase_append, Stack.erase, Control.owners]

theorem spent_binding_occurs
    (binding : TicketBinding ticket useScope (.ticket binder owner) .consumed stack) :
    owner ∈ stack.erase.spentNames := by
  cases binding with
  | spent => simp [erase_append, Stack.erase, Execution.spent_names_append, Control.spentNames]

theorem spent_name_count_le_completed (ledger : Ledger state.erase)
    (history : NameHistory state activations) (ticket : Nat) :
    state.configuration.stack.erase.spentNames.count ticket ≤ state.completed.count (.ticket ticket) := by
  have names := history.tickets ticket
  rw [Execution.ticket_name_count_accounting] at names
  have owners := ledger.1.count_eq (.ticket ticket)
  simp only [RunState.erase, List.count_append] at owners
  omega

/-- Combining name accounting with the ownership ledger places every retained
    spent marker's owner in the completion history. Neither invariant alone
    supplies this connection. -/
theorem spent_binding_was_discharged (ledger : Ledger state.erase)
    (history : NameHistory state activations)
    (binding : TicketBinding ticket useScope (.ticket binder owner) .consumed state.configuration.stack) :
    Owner.ticket owner ∈ state.completed := by
  have present := List.count_pos_iff.mpr (spent_binding_occurs binding)
  have bound := spent_name_count_le_completed ledger history owner
  exact List.count_pos_iff.mp (by omega)

theorem run_steps_completed_mono (steps : RunSteps before after) :
    before.completed ⊆ after.completed := by
  induction steps with
  | refl => exact fun _ member => member
  | next first rest ih =>
      cases first with
      | event middle created discharged raw fresh =>
          exact fun _ member => ih (List.mem_append_right _ member)

/-- A ticket discharged earlier cannot acquire an available runtime binding
    later, even after its spent clause boundary has left the active stack. -/
theorem completed_ticket_never_available (steps : RunSteps before after)
    (ledger : Ledger before.erase) (completed : Owner.ticket owner ∈ before.completed) :
    ¬ TicketBinding ticket useScope (.ticket binder owner) .available after.configuration.stack := by
  intro binding
  exact ledger_no_live_completed_alias (run_steps_preserve_ledger steps ledger)
    (available_binding_owns_ticket binding) (run_steps_completed_mono steps completed)

theorem consumed_binding_never_available (steps : RunSteps before after)
    (ledger : Ledger before.erase) (history : NameHistory before activations)
    (spent : TicketBinding ticket useScope (.ticket binder owner) .consumed before.configuration.stack) :
    ¬ TicketBinding otherTicket otherUse (.ticket otherBinder owner) .available after.configuration.stack :=
  completed_ticket_never_available steps ledger (spent_binding_was_discharged ledger history spent)


inductive NamedTrace : Configuration → Configuration → List Owner → List Owner → List Nat → Prop where
  | refl (configuration : Configuration) : NamedTrace configuration configuration [] [] []
  | next (first : RawStep before middle created discharged)
      (rest : NamedTrace middle after laterCreated laterDischarged laterActivations) :
      NamedTrace before after (created ++ laterCreated) (laterDischarged ++ discharged)
        (enteredActivations before middle ++ laterActivations)

theorem named_trace_enacts (trace : NamedTrace before after created discharged entered)
    (freshOwners : (issued ++ created).Nodup) (freshHandlers : (activations ++ entered).Nodup) :
    NamedSteps ⟨⟨before, issued, completed⟩, activations⟩
      ⟨⟨after, issued ++ created, discharged ++ completed⟩, activations ++ entered⟩ := by
  induction trace generalizing issued completed activations with
  | refl configuration => simpa using NamedSteps.refl (⟨⟨configuration, issued, completed⟩, activations⟩ : NamedState)
  | @next before middle made done after laterMade laterDone laterEntered first rest ih =>
      have allOwners : ((issued ++ made) ++ laterMade).Nodup := by simpa [List.append_assoc] using freshOwners
      have allHandlers : ((activations ++ enteredActivations before middle) ++ laterEntered).Nodup := by
        simpa [List.append_assoc] using freshHandlers
      have event := NamedStep.event ⟨⟨before, issued, completed⟩, activations⟩ middle made done first
        (List.nodup_append.mp allOwners).1 (List.nodup_append.mp allHandlers).1
      have following := ih (issued := issued ++ made) (completed := done ++ completed)
        (activations := activations ++ enteredActivations before middle) allOwners allHandlers
      simpa only [List.append_assoc] using NamedSteps.next event following

theorem named_execution_preserves_closure_ledger_and_history (steps : NamedSteps before after)
    (closed : before.execution.configuration.ResourceClosed) (ledger : Ledger before.execution.erase)
    (history : NameHistory before.execution before.activations) :
    after.execution.configuration.ResourceClosed ∧ Ledger after.execution.erase ∧
      NameHistory after.execution after.activations :=
  ⟨run_steps_preserve_resource_closure (named_steps_execute steps) closed, named_steps_preserve steps ledger history⟩

namespace NameExamples

def effect : Instance := .user 9 []
def handler (identity : Nat) : HandlerData := ⟨identity, effect, .nil, .none, .unit, rfl⟩
def handled : Code := .handle (freezeEffect effect) .unit .nil
def program : Code := .bind 1 handled handled
def context : PlainData := ⟨.bind 1 handled, .none, .unit, .unit, [], rfl⟩
def initial : NamedState := ⟨⟨⟨program, .none, .nil⟩, [], []⟩, []⟩
def terminal : NamedState := ⟨⟨⟨.unit, .none, .nil⟩, [], []⟩, [0, 1]⟩

/-- The same source handler expression is installed twice, with independent
    fresh runtime activations retained in history after both frames exit. -/
theorem sequential_handler_trace :
    NamedTrace initial.execution.configuration terminal.execution.configuration [] [] [0, 1] := by
  have e0 := RawStep.focus context (Focus.bind (initializer := handled) (by intro impossible; cases impossible)) Stack.nil
  have e1 := RawStep.enterHandler (handler 0) .unit (.push (.plain context) .nil)
  have e2 := RawStep.leaveHandler (handler 0) .unit Examples.unit_closed .none (.push (.plain context) .nil)
  have e3 := RawStep.plug context .unit Examples.unit_closed .none Stack.nil
  have e4 := RawStep.bind 1 .unit handled .none Stack.nil Examples.unit_closed (by intro _ impossible; cases impossible)
  have e5 := RawStep.enterHandler (handler 1) .unit Stack.nil
  have e6 := RawStep.leaveHandler (handler 1) .unit Examples.unit_closed .none Stack.nil
  exact .next e0 (.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.refl _)))))))

theorem sequential_handler_execution : NamedSteps initial terminal :=
  named_trace_enacts sequential_handler_trace (issued := []) (completed := []) (activations := []) (by decide) (by decide)

theorem sequential_handler_invariants :
    terminal.execution.configuration.ResourceClosed ∧ Ledger terminal.execution.erase ∧
      NameHistory terminal.execution terminal.activations := by
  apply named_execution_preserves_closure_ledger_and_history sequential_handler_execution
  · exact ⟨rfl, trivial⟩
  · exact ⟨.refl _, by decide⟩
  · refine ⟨?_, ?_, by decide⟩ <;> intro name <;> simp [initial, Stack.erase, Control.ticketNames, Control.activations]

theorem exited_handler_cannot_be_reallocated (steps : NamedSteps terminal before) (step : NamedStep before after) :
    0 ∉ enteredActivations before.execution.configuration after.execution.configuration :=
  named_execution_never_reallocates steps step (by simp [terminal])

end NameExamples

end Ash.OneShot.ScopedExecution

#print axioms Ash.OneShot.ScopedExecution.raw_step_name_bounds
#print axioms Ash.OneShot.ScopedExecution.named_steps_preserve
#print axioms Ash.OneShot.ScopedExecution.named_execution_has_unique_ticket_state
#print axioms Ash.OneShot.ScopedExecution.named_execution_never_reallocates
#print axioms Ash.OneShot.ScopedExecution.spent_binding_was_discharged
#print axioms Ash.OneShot.ScopedExecution.consumed_binding_never_available
#print axioms Ash.OneShot.ScopedExecution.named_execution_preserves_closure_ledger_and_history
#print axioms Ash.OneShot.ScopedExecution.NameExamples.sequential_handler_invariants
#print axioms Ash.OneShot.ScopedExecution.NameExamples.exited_handler_cannot_be_reallocated
