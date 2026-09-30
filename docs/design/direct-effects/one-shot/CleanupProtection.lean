import DisposalProtection

/-!
Installation and future normal invocation of source cleanup callbacks.
Retaining callback contracts is distinct from checking their invocation context.
The future phase certificate is derived at source cleanup entry; connecting
every intervening execution to that phase remains a joint-invariant obligation.
-/

namespace Ash.OneShot.CleanupProtection
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts
open CallableProtectionFrames ProtectionResiduals DisposalProtection
open ClauseProtection (Ticket Derives phaseContext exportAt)
open Syntax (UseState)

variable {action : ActionData} {ticket : Ticket}

theorem summarized_callback
    (summary : Summarizes operations environment (.cleanup action.action body) result row) :
    Callback operations action := by
  cases summary with
  | cleanup callback body =>
      have empty := value_has_no_immediate_demands callback action.closed.1
      subst_vars
      exact ⟨environment, _, callback⟩

theorem clause_callback
    (checked : Derives operations policy ticket inside environment before
      (.cleanup action.action body) after result row) : Callback operations action := by
  cases checked with
  | stable summary _ => exact summarized_callback summary
  | cleanup callback _ _ => exact ⟨environment, _, (ClauseProtection.value_summary callback action.closed.1).1⟩

theorem cell_update_retains (update : CellUpdate identity old new before after)
    (retained : Retained operations before) : Retained operations after := by
  induction update with
  | hit => exact retained
  | push miss update ih => exact ⟨retained.1, ih retained.2⟩
  | live update ih => exact ⟨retained.1, ih retained.2⟩
  | spent update ih => exact ih retained

/-- Only cleanup entry introduces a callback not already stored in the stack.
    The premise names that exact source expression; it supplies no successor
    certificate and no claim about invocation readiness. -/
theorem raw_step_retains (step : RawStep before after created discharged)
    (retained : Retained operations before.stack)
    (install : ∀ (action : ActionData) body, before.expression = .cleanup action.action body →
      Callback operations action) : Retained operations after.stack := by
  cases step with
  | focus => exact ⟨trivial, retained⟩
  | plug => exact retained.2
  | bind | beta | ifTrue | ifFalse => exact retained
  | enterHandler | enterCell => exact ⟨trivial, retained⟩
  | leaveHandler | leaveCell => exact retained.2
  | enterCleanup action body tail => exact ⟨install action body rfl, retained⟩
  | startCleanup => exact retained
  | finishCleanup => exact retained.2
  | capture requested operation parameter binder owner operand body scope whole capture tail handler result cut clause closed ready =>
      exact capture_retains_callbacks retained cut
  | resume => exact resume_retains_callbacks retained
  | discard binder owner closeId scope callerScope input answer front capture tail plan resolve built =>
      exact discard_retains_callbacks retained built
  | leaveClause => exact retained
  | finishClose | retire => exact retained.2
  | readCell identity payload scope before after selected => exact cell_update_retains selected retained
  | writeCell identity old new scope before after selected => exact cell_update_retains selected retained

theorem summarized_step_retains (step : RawStep before after created discharged)
    (retained : Retained operations before.stack)
    (summary : Summarizes operations environment before.expression result row) :
    Retained operations after.stack := by
  apply raw_step_retains step retained
  intro action body same
  rw [same] at summary
  exact summarized_callback summary

theorem clause_step_retains (step : RawStep before after created discharged)
    (retained : Retained operations before.stack)
    (checked : Derives operations policy ticket inside environment first before.expression last result row) :
    Retained operations after.stack := by
  apply raw_step_retains step retained
  intro action body same
  rw [same] at checked
  exact clause_callback checked

/-- The callback is checked for the phase in which the cleanup body returns.
    In particular, this is not an Armed certificate at an earlier phase. -/
def Normal (operations : Operations) (ticket : Ticket) (inside outside : ProtectionContracts.Context)
    (action : ActionData) (after : UseState) : Prop :=
  ∃ environment latent,
    Summarizes operations environment action.action (.function .scalar .scalar latent) [] ∧
    checkFootprint ((.barrier true :: phaseContext ticket inside after) ++ outside) latent = true

theorem normal_retains (normal : Normal operations ticket inside outside action after) :
    Callback operations action := by
  obtain ⟨environment, latent, callback, _⟩ := normal
  exact ⟨environment, latent, callback⟩

theorem inside_congr
    (checked : Derives operations policy ticket first environment before code after result row)
    (same : ∀ demands, residualize first demands = residualize second demands) :
    Derives operations policy ticket second environment before code after result row := by
  have phaseSame : ∀ state demands, exportAt ticket first state demands = exportAt ticket second state demands := by
    intro state demands
    simp only [exportAt, phaseContext, residual_append, same]
  have runningSame : ∀ demands, residualize (.barrier true :: first) demands =
      residualize (.barrier true :: second) demands := by
    intro demands
    simp only [residualize, through_barrier, same]
  have normalSame : ∀ state demands, residualize (.barrier true :: phaseContext ticket first state) demands =
      residualize (.barrier true :: phaseContext ticket second state) demands := by
    intro state demands
    simp only [residualize, through_barrier]
    exact phaseSame state (qualify true demands)
  induction checked with
  | stable summary exported => exact .stable summary ((phaseSame _ _).symm.trans exported)
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument exported ihFunction ihArgument =>
      exact .app ihFunction ihArgument ((phaseSame _ _).symm.trans exported)
  | bind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known operand exported ih => exact .perform known ih ((phaseSame _ _).symm.trans exported)
  | resume allowed operand exported ih => exact .resume allowed ih ((same _).symm.trans exported)
  | discard allowed unprotected exported => exact .discard allowed unprotected ((runningSame _).symm.trans exported)
  | cleanup callback body exported ihCallback ihBody =>
      exact .cleanup ihCallback ihBody ((normalSame _ _).symm.trans exported)
  | resource initializer body outward exported ih =>
      exact .resource ih body outward ((phaseSame _ _).symm.trans exported)

theorem under_armed
    (checked : Derives operations policy ticket inside environment before code after result row) :
    Derives operations policy ticket (.barrier false :: inside) environment before code after result row := by
  apply inside_congr checked
  intro demands
  simp [residualize, through_barrier, qualify]

theorem cleanup_decompose
    (checked : Derives operations policy ticket inside environment before
      (.cleanup action.action body) after result row)
    (accepted : checkFootprint outside row = true) :
    ∃ bodyRow, Derives operations policy ticket inside environment before body after result bodyRow ∧
      checkFootprint outside bodyRow = true ∧ Normal operations ticket inside outside action after := by
  cases checked with
  | stable summary exported =>
      cases summary with
      | cleanup callback bodySummary =>
          have empty := value_has_no_immediate_demands callback action.closed.1
          subst_vars
          rename_i latent bodyRow
          simp only [List.nil_append] at exported
          have admitted : checkFootprint (phaseContext ticket inside before ++ outside)
              (bodyRow ++ qualify true latent) = true := by
            rw [← residual_check, ← exportAt, exported]
            exact accepted
          rw [check_footprint_append, Bool.and_eq_true_iff] at admitted
          obtain ⟨bodyRow, residual, bodyAccepted⟩ :=
            residual_admitted_iff.mp admitted.1
          exact ⟨bodyRow, .stable bodySummary residual, bodyAccepted,
            environment, _, callback, by simpa [List.cons_append, ← check_qualified] using admitted.2⟩
  | cleanup callback bodyChecked exported =>
      obtain ⟨callbackSummary, same, empty⟩ := ClauseProtection.value_summary callback action.closed.1
      subst_vars
      simp only [List.nil_append, check_footprint_append, Bool.and_eq_true_iff] at accepted
      refine ⟨_, bodyChecked, accepted.1, environment, _, callbackSummary, ?_⟩
      rw [← residual_check, exported]
      exact accepted.2

theorem cleanup_entry
    (checked : Derives operations policy ticket inside environment before
      (.cleanup action.action body) after result row)
    (accepted : checkFootprint outside row = true)
    (retained : Retained operations tail) :
    ∃ bodyRow, RawStep ⟨.cleanup action.action body, action.scope, tail⟩
      ⟨body, action.scope, .push (.armed action) tail⟩ [.cleanup action.identity] [] ∧
      Derives operations policy ticket (.barrier false :: inside) environment before body after result bodyRow ∧
      checkFootprint outside bodyRow = true ∧ Normal operations ticket inside outside action after ∧
      Retained operations (.push (.armed action) tail) := by
  obtain ⟨bodyRow, bodyChecked, bodyAccepted, normal⟩ := cleanup_decompose checked accepted
  exact ⟨bodyRow, .enterCleanup action body tail, under_armed bodyChecked,
    bodyAccepted, normal, normal_retains normal, retained⟩

theorem normal_available_armed
    (normal : Normal operations ticket (contextOf tables front) (contextOf tables tail) action .available)
    (held : ticket.held = ProtectionContexts.protectedMode capture.erase) :
    Armed operations tables action (front.append (.live owner input answer capture scope tail)) := by
  obtain ⟨environment, latent, callback, accepted⟩ := normal
  refine ⟨environment, latent, callback, ?_⟩
  have qualified : checkFootprint (phaseContext ticket (contextOf tables front) .available ++ contextOf tables tail)
      (qualify true latent) = true := by simpa only [check_qualified, List.cons_append] using accepted
  rw [ClauseProtection.available_stack_check tables front capture tail held] at qualified
  exact (check_qualified).symm.trans qualified

theorem normal_consumed_armed
    (normal : Normal operations ticket (contextOf tables front) (contextOf tables tail) action .consumed) :
    Armed operations tables action (front.append (.spent owner answer scope tail)) := by
  obtain ⟨environment, latent, callback, accepted⟩ := normal
  refine ⟨environment, latent, callback, ?_⟩
  have qualified : checkFootprint (phaseContext ticket (contextOf tables front) .consumed ++ contextOf tables tail)
      (qualify true latent) = true := by simpa only [check_qualified, List.cons_append] using accepted
  rw [ClauseProtection.consumed_stack_check tables front tail] at qualified
  exact (check_qualified).symm.trans qualified

theorem consumed_start
    (normal : Normal operations ticket (contextOf tables front) (contextOf tables tail) action .consumed)
    (returned : Derives operations policy ticket inside environment .consumed value .consumed result row)
    (closed : ClosedValue value) :
    let suffix := front.append (.spent owner answer callerScope tail)
    RawStep ⟨value, scope, .push (.armed action) suffix⟩
      ⟨.app action.action .unit, .none, .push (.running action value closed) suffix⟩ [] [] ∧
      Checked operations tables environment (.push (.running action value closed) suffix)
        (.app action.action .unit) .scalar ∧ Saved operations value result := by
  have valueSummary := (ClauseProtection.value_summary returned closed.1).1
  exact start_cleanup_step (normal_consumed_armed normal)
    ⟨[], valueSummary, rfl⟩ closed

theorem available_start
    (normal : Normal operations ticket (contextOf tables front) (contextOf tables tail) action .available)
    (held : ticket.held = ProtectionContexts.protectedMode capture.erase)
    (returned : Derives operations policy ticket inside environment .available value .available result row)
    (closed : ClosedValue value) :
    let suffix := front.append (.live owner input answer capture callerScope tail)
    RawStep ⟨value, scope, .push (.armed action) suffix⟩
      ⟨.app action.action .unit, .none, .push (.running action value closed) suffix⟩ [] [] ∧
      Checked operations tables environment (.push (.running action value closed) suffix)
        (.app action.action .unit) .scalar ∧ Saved operations value result := by
  have valueSummary := (ClauseProtection.value_summary returned closed.1).1
  exact start_cleanup_step (normal_available_armed normal held)
    ⟨[], valueSummary, rfl⟩ closed

namespace Examples
open Instantiation
open CallableProtection.Examples (effect operations function functionContract function_summary function_closed unit_closed)
def cleanupAction : ActionData := { CallableProtectionFrames.Examples.action with identity := 8, scope := .ticket 0 7 }
def capturedAction : ActionData := { CallableProtectionFrames.Examples.action with identity := 9 }

def effectF : Instance := .user 1 []
def demandF : Footprint := [⟨effectF, 0, false⟩]
def handlerE : HandlerData := ⟨11, effect,
  .cons 0 0 1 (.bind 2 (.resume 1 .unit) (.perform (freezeEffect effectF) 0 .unit)) .nil,
  .none, .unit, rfl⟩
def handlerF : HandlerData := ⟨22, effectF, .cons 0 0 2 (.discard 2) .nil, .none, .unit, rfl⟩
def tables : Tables := fun handler => if handler.activation = 11 then
  [(0, ⟨false, some demandF, some demandF⟩)] else [(0, ⟨true, some [], none⟩)]
def front : Stack := .push (.handler handlerE) .nil
def tail : Stack := .push (.handler handlerF) .nil
def capture : Stack := .push (.running capturedAction .unit unit_closed) .nil
def capturedTicket : Ticket := ⟨0, .scalar, .scalar, true, [], []⟩
def policy : Syntax.TicketPolicy := fun _ => ActionRequirements.resumeOnly
def cleanupSource : Code := .cleanup cleanupAction.action (.resume 0 .unit)

theorem cleanup_source_checked : Derives operations policy capturedTicket (contextOf tables front)
    environment .available cleanupSource .consumed .scalar demandF := by
  have callback : Derives operations policy capturedTicket (contextOf tables front) environment
      .available cleanupAction.action .available functionContract [] := .stable function_summary (by decide)
  have body : Derives operations policy capturedTicket (contextOf tables front) environment
      .available (.resume 0 .unit) .consumed .scalar [] :=
    .resume (ticket := capturedTicket) (inside := contextOf tables front)
      (operandRow := []) (resumedRow := []) rfl (.stable .unit (by decide)) (by decide)
  exact .cleanup callback body (by decide)

theorem future_normal_derived :
    Normal operations capturedTicket (contextOf tables front) (contextOf tables tail) cleanupAction .consumed := by
  obtain ⟨_, _, _, normal⟩ := cleanup_decompose
    (cleanup_source_checked (environment := .empty)) (show checkFootprint (contextOf tables tail) demandF = true by decide)
  exact normal

theorem installation_from_source :
    Retained operations (.push (.armed cleanupAction) (front.append (.live 7 .unit .unit capture .none tail))) := by
  apply clause_step_retains (RawStep.enterCleanup cleanupAction (.resume 0 .unit) _)
    (checked := cleanup_source_checked (environment := .empty))
  exact (retained_append_iff front _).mpr ⟨⟨trivial, trivial⟩,
    ⟨⟨.empty, _, function_summary⟩, trivial⟩, trivial, trivial⟩

theorem premature_arming_rejected :
    ¬ Armed operations tables cleanupAction (front.append (.live 7 .unit .unit capture .none tail)) := by
  intro armed
  have started := (start_cleanup_step armed
    (show Checked operations tables .empty
      (.push (.armed cleanupAction) (front.append (.live 7 .unit .unit capture .none tail))) .unit .scalar from
        ⟨[], .unit, rfl⟩) unit_closed (scope := .none)).2.1
  have reduced := (CallableProtectionFrames.beta_step started unit_closed function_closed (scope := .none)).2
  have admitted := actual_request_admitted reduced
  have rejected : checkRequest
      (contextOf tables (.push (.running cleanupAction .unit unit_closed)
        (front.append (.live 7 .unit .unit capture .none tail)))) ⟨effect, 0, false⟩ = false := by decide
  rw [rejected] at admitted
  cases admitted

theorem normal_start_after_consumption :
    let suffix := front.append (.spent 7 .unit .none tail)
    RawStep ⟨.unit, .none, .push (.armed cleanupAction) suffix⟩
      ⟨.app cleanupAction.action .unit, .none, .push (.running cleanupAction .unit unit_closed) suffix⟩ [] [] ∧
      Checked operations tables environment (.push (.running cleanupAction .unit unit_closed) suffix)
        (.app cleanupAction.action .unit) .scalar ∧ Saved operations .unit .scalar := by
  exact consumed_start future_normal_derived
    (show Derives operations policy capturedTicket [] environment .consumed .unit .consumed .scalar [] from
      .stable .unit rfl) unit_closed

theorem stable_cleanup_decomposition :
    ∃ bodyRow, Derives operations policy capturedTicket [] environment .available .unit .available .scalar bodyRow ∧
      checkFootprint CallableProtection.Examples.resumeContext bodyRow = true ∧
      Normal operations capturedTicket [] CallableProtection.Examples.resumeContext cleanupAction .available := by
  have checked : Derives operations policy capturedTicket [] environment .available
      (.cleanup cleanupAction.action .unit) .available .scalar [⟨effect, 0, true⟩] :=
    .stable (.cleanup function_summary .unit) (by decide)
  exact cleanup_decompose checked (by decide)

theorem cell_update_keeps_dormant_callback :
    Retained operations (.live 9 .unit .unit (.push (.armed cleanupAction) .nil) .none
      (.push (.cell 42 18 .none .unit) .nil)) := by
  have update : CellUpdate 42 17 18
      (.live 9 .unit .unit (.push (.armed cleanupAction) .nil) .none (.push (.cell 42 17 .none .unit) .nil))
      (.live 9 .unit .unit (.push (.armed cleanupAction) .nil) .none (.push (.cell 42 18 .none .unit) .nil)) := .live .hit
  exact cell_update_retains update ⟨⟨⟨.empty, _, function_summary⟩, trivial⟩, trivial, trivial⟩

end Examples

end Ash.OneShot.CleanupProtection

#print axioms Ash.OneShot.CleanupProtection.summarized_callback
#print axioms Ash.OneShot.CleanupProtection.clause_callback
#print axioms Ash.OneShot.CleanupProtection.cell_update_retains
#print axioms Ash.OneShot.CleanupProtection.raw_step_retains
#print axioms Ash.OneShot.CleanupProtection.summarized_step_retains
#print axioms Ash.OneShot.CleanupProtection.clause_step_retains
#print axioms Ash.OneShot.CleanupProtection.normal_retains
#print axioms Ash.OneShot.CleanupProtection.inside_congr
#print axioms Ash.OneShot.CleanupProtection.under_armed
#print axioms Ash.OneShot.CleanupProtection.cleanup_decompose
#print axioms Ash.OneShot.CleanupProtection.cleanup_entry
#print axioms Ash.OneShot.CleanupProtection.normal_available_armed
#print axioms Ash.OneShot.CleanupProtection.normal_consumed_armed
#print axioms Ash.OneShot.CleanupProtection.consumed_start
#print axioms Ash.OneShot.CleanupProtection.available_start
#print axioms Ash.OneShot.CleanupProtection.Examples.cleanup_source_checked
#print axioms Ash.OneShot.CleanupProtection.Examples.future_normal_derived
#print axioms Ash.OneShot.CleanupProtection.Examples.installation_from_source
#print axioms Ash.OneShot.CleanupProtection.Examples.premature_arming_rejected
#print axioms Ash.OneShot.CleanupProtection.Examples.normal_start_after_consumption
#print axioms Ash.OneShot.CleanupProtection.Examples.stable_cleanup_decomposition
#print axioms Ash.OneShot.CleanupProtection.Examples.cell_update_keeps_dormant_callback
