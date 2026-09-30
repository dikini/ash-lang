import Dispatch

/-!
Lifetime ticket-name and handler-activation evidence for the expression machine.
The naming invariant is separate from the ownership ledger and expression
typing. Fresh activation allocation is recorded explicitly. These proofs do
not certify source instantiation, effect availability, or cleanup safety.
-/

namespace Ash.OneShot.Execution
open Syntax Typing

theorem owned_ticket_count_le_names (control : Control) (ticket : Nat) :
    control.owners.count (.ticket ticket) ≤ control.ticketNames.count ticket := by
  induction control with
  | nil => simp [Control.owners, Control.ticketNames]
  | push frame rest ih =>
      cases kind : frame.kind <;>
        simp_all [Control.owners, Control.ticketNames, Frame.owners, List.count_cons]
  | live owner input answer saved rest ihSaved ihRest =>
      by_cases same : ticket = owner <;>
        simp_all [Control.owners, Control.ticketNames, List.count_append, List.count_cons] <;> omega
  | spent owner answer rest ih =>
      simp only [Control.owners, Control.ticketNames, List.count_cons]
      omega

theorem plan_ticket_names_count (plan : List CloseItem) (ticket : Nat) :
    (planControl plan).ticketNames.count ticket = (planOwners plan).count (.ticket ticket) := by
  induction plan with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | release | invoke =>
          simpa [planControl, Control.ticketNames, CloseItem.frame, planOwners,
            CloseItem.owner] using ih
      | retire owner =>
          by_cases same : ticket = owner <;>
            simp [planControl, Control.ticketNames, CloseItem.frame, planOwners,
              CloseItem.owner, List.count_cons, same] at ih ⊢ <;> omega

/-- Raw close-plan construction cannot invent clause names, even before
    resource support or interpretation admission is considered. -/
theorem raw_plan_ticket_name_bound {control : Control} (built : rawPlan control = some plan) (ticket : Nat) :
    (planControl plan).ticketNames.count ticket ≤ control.ticketNames.count ticket := by
  rw [plan_ticket_names_count, (raw_plan_accounting control built).count_eq]
  exact owned_ticket_count_le_names control ticket

/-- On an actual raw transition, this records the activation installed by
    handler entry. Other expression shapes do not allocate a handler. -/
def enteredActivations (before after : Configuration) : List Nat :=
  match before.expression, after.stack with
  | .handle _ _ _, .push (.handler handler) _ => [handler.activation]
  | _, _ => []

theorem value_enters_no_activation (closed : ClosedValue value) :
    enteredActivations ⟨value, scope, stack⟩ after = [] := by
  have valueForm := closed.1
  cases value <;> simp_all [enteredActivations, Expr.IsValue]

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
  | enterCell identity payload body scope answer tail =>
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
      output cut selected closed ready fresh =>
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
      have bound := raw_plan_ticket_name_bound erasedBuild ticket
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

/-- True spent clause markers, excluding retirement frames that still own an
    undisposed ticket. The traversal includes markers in dormant captures. -/
def _root_.Ash.OneShot.Control.spentNames : Control → List Nat
  | .nil => []
  | .push _ rest => rest.spentNames
  | .live _ _ _ saved rest => saved.spentNames ++ rest.spentNames
  | .spent owner _ rest => owner :: rest.spentNames

theorem spent_names_append (front tail : Control) :
    (front.append tail).spentNames = front.spentNames ++ tail.spentNames := by
  induction front <;> simp_all [Control.append, Control.spentNames, List.append_assoc]

/-- Each retained ticket name is either an owned live/retiring occurrence or
    a spent marker. This accounting is independent of freshness assumptions. -/
theorem ticket_name_count_accounting (control : Control) (ticket : Nat) :
    control.ticketNames.count ticket =
      control.owners.count (.ticket ticket) + control.spentNames.count ticket := by
  induction control with
  | nil => simp [Control.ticketNames, Control.owners, Control.spentNames]
  | push frame rest ih =>
      cases kind : frame.kind <;>
        simp_all [Control.ticketNames, Control.owners, Control.spentNames, Frame.owners,
          List.count_cons] <;> omega
  | live owner input answer saved rest ihSaved ihRest =>
      by_cases same : ticket = owner <;>
        simp_all [Control.ticketNames, Control.owners, Control.spentNames,
          List.count_append, List.count_cons] <;> omega
  | spent owner answer rest ih =>
      simp [Control.ticketNames, Control.owners, Control.spentNames, List.count_cons, ih]
      omega

theorem spent_binding_occurs
    (binding : TicketBinding ticket useScope (.ticket binder owner) .consumed stack) :
    owner ∈ stack.erase.spentNames := by
  cases binding with
  | spent => simp [erase_append, Stack.erase, spent_names_append, Control.spentNames]

theorem spent_name_count_le_completed (ledger : Ledger state.erase)
    (history : NameHistory state activations) (ticket : Nat) :
    state.configuration.stack.erase.spentNames.count ticket ≤ state.completed.count (.ticket ticket) := by
  have names := history.tickets ticket
  rw [ticket_name_count_accounting] at names
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

/-- Name allocation and resource-access admission refer to the same actual
    transition. Source checking still has to derive the access checks. -/
structure NamedAccessStep (ambient : List Nat) (before after : NamedState) : Prop where
  execution : NamedStep before after
  checks : AccessChecks before.execution.configuration ambient

inductive NamedAccessSteps (ambient : List Nat) : NamedState → NamedState → Prop where
  | refl (state : NamedState) : NamedAccessSteps ambient state state
  | next (first : NamedAccessStep ambient before middle)
      (rest : NamedAccessSteps ambient middle after) : NamedAccessSteps ambient before after

theorem named_access_steps_have_names (steps : NamedAccessSteps ambient before after) :
    NamedSteps before after := by
  induction steps with
  | refl => exact .refl _
  | next first rest ih => exact .next first.execution ih

theorem named_access_step_preserves (step : NamedAccessStep ambient before after)
    (ledger : Ledger before.execution.erase) (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient) :
    Ledger after.execution.erase ∧ NameHistory after.execution after.activations ∧
      AccessValid after.execution.configuration ambient := by
  obtain ⟨nextLedger, nextHistory⟩ := named_step_preserves step.execution ledger history
  exact ⟨nextLedger, nextHistory,
    access_run_step_preserves ⟨named_step_executes step.execution, step.checks⟩ access⟩

theorem named_access_steps_preserve (steps : NamedAccessSteps ambient before after)
    (ledger : Ledger before.execution.erase) (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient) :
    Ledger after.execution.erase ∧ NameHistory after.execution after.activations ∧
      AccessValid after.execution.configuration ambient := by
  induction steps with
  | refl => exact ⟨ledger, history, access⟩
  | next first rest ih =>
      obtain ⟨nextLedger, nextHistory, nextAccess⟩ := named_access_step_preserves first ledger history access
      exact ih nextLedger nextHistory nextAccess

namespace NameExamples
open Ash.OneShot.Execution.Examples

theorem cleanup_execution_has_joint_checks :
    NamedAccessSteps []
      ⟨⟨⟨.handle (.user 1 []) (.cleanup callback (.integer 42)) clauses, .none, .nil⟩, [], []⟩, []⟩
      ⟨⟨⟨.integer 42, .none, .nil⟩, [.cleanup 7, .ticket 3], [.cleanup 7, .ticket 3]⟩, [8]⟩ := by
  have select : HandlerCut (.user 1 []) captureStack captureStack .nil handler :=
    .push _ _ _ _ _ (by simp [ExecFrame.erase, Frame.target]) (.hit handler .nil rfl)
  have e0 := RawStep.enterHandler handler (.cleanup callback (.integer 42)) .nil
  have e1 := RawStep.enterCleanup action (.integer 42) handlerStack
  have e2 := RawStep.startCleanup action (.integer 42) (closed_integer 42) .none handlerStack
  have e3 := RawStep.beta 0 callbackBody .unit .none captureStack closed_unit callback_closed
    (by simp [ResourceFresh, Expr.dependencies])
  have e4 := RawStep.capture (.user 1 []) 0 1 9 3 .unit (.resume 9 .unit) .none
    captureStack captureStack .nil handler .unit select .hit closed_unit
    (by simp [ClosedExcept, Expr.dependencies]) (by simp [ResourceFresh, Expr.dependencies])
  have e5 := RawStep.resume 9 3 (.ticket 9 3) .none .unit .integer .nil captureStack .nil .unit closed_unit rfl
  have e6 := RawStep.finishCleanup action (.integer 42) (closed_integer 42) (.ticket 9 3)
    (.push (.handler handler) spentStack)
  have e7 := RawStep.leaveHandler handler (.integer 42) (closed_integer 42) .none spentStack
  have e8 := RawStep.leaveClause 3 .integer (.integer 42) (closed_integer 42) .none .none .nil
  refine .next ⟨.event _ _ _ _ e0 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e1 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e2 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e3 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e4 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e5 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e6 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e7 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  exact .next ⟨.event _ _ _ _ e8 (by decide) (by decide),
    resource_free_access_checks rfl (by intro binder same; cases same)⟩ (.refl _)

theorem cleanup_execution_has_name_history :
    NamedSteps
      ⟨⟨⟨.handle (.user 1 []) (.cleanup callback (.integer 42)) clauses, .none, .nil⟩, [], []⟩, []⟩
      ⟨⟨⟨.integer 42, .none, .nil⟩, [.cleanup 7, .ticket 3], [.cleanup 7, .ticket 3]⟩, [8]⟩ :=
  named_access_steps_have_names cleanup_execution_has_joint_checks

theorem cleanup_final_history_checked :
    NameHistory
      ⟨⟨.integer 42, .none, .nil⟩, [.cleanup 7, .ticket 3], [.cleanup 7, .ticket 3]⟩ [8] := by
  exact (named_steps_preserve cleanup_execution_has_name_history ⟨.refl [], by decide⟩
    ⟨by simp [Stack.erase, Control.ticketNames], by simp [Stack.erase, Control.activations], by decide⟩).2

theorem cleanup_final_joint_invariant :
    let final : RunState := ⟨⟨.integer 42, .none, .nil⟩,
      [.cleanup 7, .ticket 3], [.cleanup 7, .ticket 3]⟩
    Ledger final.erase ∧ NameHistory final [8] ∧ AccessValid final.configuration [] := by
  apply named_access_steps_preserve cleanup_execution_has_joint_checks ⟨.refl [], by decide⟩
    ⟨by simp [Stack.erase, Control.ticketNames], by simp [Stack.erase, Control.activations], by decide⟩
  constructor
  · exact .nil _
  · simp [Expr.dependencies, callback, callbackBody, clauses, Clauses.dependencies,
      resourceDependencies, instanceDependencies, Instance.resources, without]

/-- The old activation is no longer active, but remains unavailable for
    allocation. A raw entry alone has no such history check. -/
theorem exited_handler_activation_cannot_be_reused :
    RawStep ⟨.handle handler.effectInst .unit handler.clauses, .none, .nil⟩
      ⟨.unit, .none, .push (.handler handler) .nil⟩ [] [] ∧
    ¬ ([8] ++ enteredActivations
      ⟨.handle handler.effectInst .unit handler.clauses, .none, .nil⟩
      ⟨.unit, .none, .push (.handler handler) .nil⟩).Nodup :=
  ⟨.enterHandler handler .unit .nil, by decide⟩

theorem alias_counterexample_has_no_name_history :
    ¬ NameHistory ⟨⟨.unit, .ticket 9 3, DispatchExamples.aliasedTicketStack⟩, [.ticket 3], []⟩ [] := by
  intro history
  have names := history.tickets 3
  simp [DispatchExamples.aliasedTicketStack, Stack.erase, Control.ticketNames] at names

end NameExamples

end Ash.OneShot.Execution

#print axioms Ash.OneShot.Execution.raw_step_name_bounds
#print axioms Ash.OneShot.Execution.named_steps_preserve
#print axioms Ash.OneShot.Execution.named_execution_has_unique_ticket_state
#print axioms Ash.OneShot.Execution.completed_ticket_never_available
#print axioms Ash.OneShot.Execution.named_execution_never_reallocates
#print axioms Ash.OneShot.Execution.NameExamples.cleanup_execution_has_name_history
#print axioms Ash.OneShot.Execution.named_access_steps_preserve
#print axioms Ash.OneShot.Execution.spent_binding_was_discharged
#print axioms Ash.OneShot.Execution.consumed_binding_never_available
#print axioms Ash.OneShot.Execution.NameExamples.cleanup_execution_has_joint_checks
#print axioms Ash.OneShot.Execution.NameExamples.cleanup_final_joint_invariant
