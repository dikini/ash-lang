import CertifiedClauseRows

/-!
Disposal requirements derived from executable close plans and retained callback
source contracts. This checks protection and effect availability at invocation;
ordinary ports, ownership/access and exact interpretation agreement stay separate.
-/

namespace Ash.OneShot.DisposalProtection
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals CallableProtectionFrames
open ScopedPorts (planProvides InvocationAt)

/-- The interpretation context of planned frames has no source handlers. -/
def planContext : List CloseEntry → ProtectionContracts.Context
  | [] => []
  | .release identity _ :: rest => .builtin identity :: planContext rest
  | .invoke _ :: rest => .barrier false :: planContext rest
  | .retire _ :: rest => .barrier true :: planContext rest

theorem plan_context_realizes (tables : Tables) (scope : Scope) (plan : List CloseEntry) :
    contextOf tables (closeControl scope plan) = planContext plan := by
  induction plan with
  | nil => rfl
  | cons entry rest ih => cases entry <;>
      simp [closeControl, CloseEntry.frame, contextOf, pushContext, ExecFrame.erase,
        ActionData.erase, CloseItem.frame, ProtectionContexts.frameProtected, planContext, ih]

def callbackResidual (rest : List CloseEntry) (latent : Footprint) : Footprint :=
  qualify true (latent.filter fun request => decide (request.effect ∉ planProvides rest))

theorem through_barrier (held : Bool) (row : Footprint) :
    throughLayer (.barrier held) row = some (qualify held row) := by
  induction row with
  | nil => rfl
  | cons request rest ih => simp [throughLayer, demandThrough, merge, qualify, ih]

theorem protected_request_residual (plan : List CloseEntry) (request : Demand) :
    residualize (planContext plan) [{ request with held := true }] =
      some (if request.effect ∈ planProvides plan then [] else [{ request with held := true }]) := by
  induction plan with
  | nil => simp [planContext, planProvides, residualize]
  | cons entry rest ih => cases entry with
      | release identity payload =>
          by_cases same : request.effect = .cell identity
          · simp [planContext, planProvides, residualize, throughLayer, demandThrough, merge, same, residual_empty]
          · simpa [planContext, planProvides, residualize, throughLayer, demandThrough, merge, same] using ih
      | invoke action =>
          change residualize (planContext rest) [{ request with held := true }] = _
          exact ih
      | retire owner =>
          change residualize (planContext rest) [{ request with held := true }] = _
          exact ih

theorem protected_row_residual (plan : List CloseEntry) (row : Footprint) :
    residualize (planContext plan) (qualify true row) = some (callbackResidual plan row) := by
  induction row with
  | nil => simp [qualify, callbackResidual, residual_empty]
  | cons request rest ih =>
      have splitRow : qualify true (request :: rest) = [{ request with held := true }] ++ qualify true rest := by
        simp [qualify]
      rw [splitRow, residual_rows_append, protected_request_residual, ih]
      by_cases provided : request.effect ∈ planProvides plan <;>
        simp [merge, callbackResidual, qualify, provided]

theorem callback_residual_exact (plan : List CloseEntry) (latent : Footprint) :
    residualize (.barrier true :: planContext plan) latent = some (callbackResidual plan latent) := by
  simp only [residualize, through_barrier]
  exact protected_row_residual plan latent

theorem callback_residual_check (plan : List CloseEntry) (latent : Footprint) (outside : ProtectionContracts.Context) :
    checkFootprint outside (callbackResidual plan latent) =
      checkFootprint ((.barrier true :: planContext plan) ++ outside) latent := by
  rw [← residual_check, callback_residual_exact]
  rfl

def Callback (operations : Operations) (action : ActionData) : Prop :=
  ∃ environment latent, Summarizes operations environment action.action (.function .scalar .scalar latent) []

inductive Contents (operations : Operations) : List CloseEntry → Prop where
  | nil : Contents operations []
  | release (rest : Contents operations plan) : Contents operations (.release identity payload :: plan)
  | retire (rest : Contents operations plan) : Contents operations (.retire owner :: plan)
  | invoke (callback : Callback operations action) (rest : Contents operations plan) :
      Contents operations (.invoke action :: plan)

inductive Rows (operations : Operations) : List CloseEntry → Footprint → Prop where
  | nil : Rows operations [] []
  | release (rest : Rows operations plan row) : Rows operations (.release identity payload :: plan) row
  | retire (rest : Rows operations plan row) : Rows operations (.retire owner :: plan) row
  | invoke (callback : Summarizes operations environment action.action (.function .scalar .scalar latent) [])
      (rest : Rows operations plan row) :
      Rows operations (.invoke action :: plan) (callbackResidual plan latent ++ row)

theorem contents_rows (contents : Contents operations plan) : ∃ row, Rows operations plan row := by
  induction contents with
  | nil => exact ⟨[], .nil⟩
  | release rest ih => obtain ⟨row, checked⟩ := ih; exact ⟨row, .release checked⟩
  | retire rest ih => obtain ⟨row, checked⟩ := ih; exact ⟨row, .retire checked⟩
  | invoke callback rest ih =>
      obtain ⟨environment, latent, checked⟩ := callback
      obtain ⟨row, tail⟩ := ih
      exact ⟨_, .invoke checked tail⟩

theorem contents_append (front : Contents operations first) (tail : Contents operations second) :
    Contents operations (first ++ second) := by
  induction front with
  | nil => exact tail
  | release rest ih => exact .release ih
  | retire rest ih => exact .retire ih
  | invoke callback rest ih => exact .invoke callback ih

def frameCallbacks (operations : Operations) : ExecFrame → Prop
  | .armed action | .running action _ _ => Callback operations action
  | _ => True

def Retained (operations : Operations) : Stack → Prop
  | .nil => True
  | .push frame rest => frameCallbacks operations frame ∧ Retained operations rest
  | .live _ _ _ saved _ rest => Retained operations saved ∧ Retained operations rest
  | .spent _ _ _ rest => Retained operations rest

theorem make_plan_contents (retained : Retained operations stack) (built : makePlan stack = some plan) :
    Contents operations plan := by
  induction stack generalizing plan with
  | nil => cases built; exact .nil
  | push frame rest ih =>
      obtain ⟨current, remaining⟩ := retained
      cases frame with
      | plain => exact ih remaining built
      | handler => exact ih remaining built
      | cell identity payload scope answer =>
          cases next : makePlan rest <;> simp [makePlan, next] at built
          case some suffix => subst plan; exact .release (ih remaining next)
      | armed action =>
          cases next : makePlan rest <;> simp [makePlan, next] at built
          case some suffix => subst plan; exact .invoke current (ih remaining next)
      | running | unwinding | closing | retiring => simp [makePlan] at built
  | live owner input answer saved scope rest ihSaved ihRest =>
      cases inner : makePlan saved <;> cases outer : makePlan rest <;> simp [makePlan, inner, outer] at built
      case some.some inside outside =>
        subst plan
        exact contents_append (ihSaved retained.1 inner) (.retire (ihRest retained.2 outer))
  | spent owner answer scope rest ih => exact ih retained built

theorem captured_disposal_row (retained : Retained operations stack) (built : makePlan stack = some plan) :
    ∃ row, Rows operations plan row := contents_rows (make_plan_contents retained built)

theorem retained_append_iff (front tail : Stack) :
    Retained operations (front.append tail) ↔ Retained operations front ∧ Retained operations tail := by
  induction front with
  | nil => simp [Stack.append, Retained]
  | push frame rest ih => simp only [Stack.append, Retained, ih, and_assoc]
  | live owner input answer saved scope rest ihSaved ihRest =>
      simp only [Stack.append, Retained, ihRest, and_assoc]
  | spent owner answer scope rest ih => exact ih

theorem contents_retained (contents : Contents operations plan) (scope : Scope) :
    Retained operations (closeControl scope plan) := by
  induction contents with
  | nil => trivial
  | release rest ih | retire rest ih => exact ⟨trivial, ih⟩
  | invoke callback rest ih => exact ⟨callback, ih⟩

theorem capture_retains_callbacks (retained : Retained operations whole)
    (cut : HandlerCut requested whole capture tail handler) :
    Retained operations (.live owner input answer capture scope tail) := by
  rw [handler_cut_reconstructs cut] at retained
  exact (retained_append_iff capture tail).mp retained

theorem resume_retains_callbacks {front capture : Stack}
    (retained : Retained operations (front.append (.live owner input answer capture scope tail))) :
    Retained operations (capture.append (front.append (.spent owner answer scope tail))) := by
  obtain ⟨before, saved, after⟩ := (retained_append_iff front _).mp retained
  exact (retained_append_iff capture _).mpr
    ⟨saved, (retained_append_iff front _).mpr ⟨before, after⟩⟩

theorem discard_retains_callbacks {front : Stack}
    (retained : Retained operations (front.append (.live owner input answer capture callerScope tail)))
    (built : makePlan capture = some plan) :
    Retained operations ((closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer callerScope tail)))) := by
  obtain ⟨before, saved, after⟩ := (retained_append_iff front _).mp retained
  exact (retained_append_iff _ _).mpr
    ⟨contents_retained (make_plan_contents saved built) scope,
      trivial, (retained_append_iff front _).mpr ⟨before, after⟩⟩

/-- Each callback is checked where it will run, after prior releases and before
    the remaining plan. These are normal invocation checks, not a run theorem. -/
inductive Ready (operations : Operations) (outside : ProtectionContracts.Context) : List CloseEntry → Prop where
  | nil : Ready operations outside []
  | release (rest : Ready operations outside plan) : Ready operations outside (.release identity payload :: plan)
  | retire (rest : Ready operations outside plan) : Ready operations outside (.retire owner :: plan)
  | invoke (callback : Summarizes operations environment action.action (.function .scalar .scalar latent) [])
      (checked : checkFootprint ((.barrier true :: planContext plan) ++ outside) latent = true)
      (rest : Ready operations outside plan) : Ready operations outside (.invoke action :: plan)

theorem rows_ready (rows : Rows operations plan row) (accepted : checkFootprint outside row = true) :
    Ready operations outside plan := by
  induction rows with
  | nil => exact .nil
  | release rest ih => exact .release (ih accepted)
  | retire rest ih => exact .retire (ih accepted)
  | invoke callback rest ih =>
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      exact .invoke callback ((callback_residual_check _ _ _).symm.trans accepted.1) (ih accepted.2)

theorem ready_rows (ready : Ready operations outside plan) :
    ∃ row, Rows operations plan row ∧ checkFootprint outside row = true := by
  induction ready with
  | nil => exact ⟨[], .nil, rfl⟩
  | release rest ih => obtain ⟨row, checked, accepted⟩ := ih; exact ⟨row, .release checked, accepted⟩
  | retire rest ih => obtain ⟨row, checked, accepted⟩ := ih; exact ⟨row, .retire checked, accepted⟩
  | invoke callback checked rest ih =>
      obtain ⟨row, retained, accepted⟩ := ih
      exact ⟨_, .invoke callback retained, by
        rw [check_footprint_append, Bool.and_eq_true_iff]
        exact ⟨(callback_residual_check _ _ _).trans checked, accepted⟩⟩

theorem ready_iff_rows : Ready operations outside plan ↔
    ∃ row, Rows operations plan row ∧ checkFootprint outside row = true :=
  ⟨ready_rows, fun ⟨_, rows, accepted⟩ => rows_ready rows accepted⟩

theorem ready_invocation (ready : Ready operations outside plan)
    (position : InvocationAt action plan rest) :
    Ready operations outside (.invoke action :: rest) := by
  induction position with
  | here => exact ready
  | later position ih => cases ready with
      | release remaining | retire remaining => exact ih remaining
      | invoke _ _ remaining => exact ih remaining

/-- The actual remaining close-control suffix realizes the callback's checking
    context. The outside stack includes any closing boundary and waiting frames. -/
theorem invocation_armed (ready : Ready operations (contextOf tables tail) plan)
    (position : InvocationAt action plan rest) (scope : Scope) :
    Armed operations tables { action with scope := scope, answer := .unit }
      ((closeControl scope rest).append tail) := by
  cases ready_invocation ready position with
  | invoke callback checked remaining =>
      refine ⟨_, _, callback, ?_⟩
      simpa only [context_append, plan_context_realizes, List.cons_append] using checked

/-- A callback reached in the materialized plan can take the actual invocation
    step with a checked source application. This does not prove the intervening
    execution from the beginning of the plan reaches this configuration. -/
theorem invocation_step (ready : Ready operations (contextOf tables tail) plan)
    (position : InvocationAt action plan rest) (scope : Scope) :
    let planned := { action with scope := scope, answer := .unit }
    let suffix := (closeControl scope rest).append tail
    RawStep ⟨.unit, scope, .push (.armed planned) suffix⟩
      ⟨.app action.action .unit, .none,
        .push (.running planned .unit ScopedExecution.Examples.unit_closed) suffix⟩ [] [] ∧
      Checked operations tables environment
        (.push (.running planned .unit ScopedExecution.Examples.unit_closed) suffix)
        (.app action.action .unit) .scalar := by
  have checked : Checked operations tables environment
      (.push (.armed { action with scope := scope, answer := .unit })
        ((closeControl scope rest).append tail)) .unit .scalar := ⟨[], .unit, rfl⟩
  have result := start_cleanup_step (invocation_armed ready position scope) checked
    ScopedExecution.Examples.unit_closed (scope := scope)
  exact ⟨result.1, result.2.1⟩

/-- Authenticating the ticket's disposal row against the actual plan lets the
    source discard rule establish readiness under the actual closing boundary. -/
theorem discard_ready {ticket : ClauseProtection.Ticket}
    (checked : ClauseProtection.Derives operations policy ticket (contextOf tables front)
      environment .available (.discard ticket.binder) .consumed .scalar outside)
    (rows : Rows operations plan ticket.disposalRow)
    (accepted : checkFootprint (contextOf tables tail) outside = true) :
    Ready operations (contextOf tables
      (.push (.closing closeId scope) (front.append (.spent owner answer callerScope tail)))) plan := by
  cases checked with
  | discard _ _ exported =>
      apply rows_ready rows
      have admitted : checkFootprint
          ((.barrier true :: contextOf tables front) ++ contextOf tables tail) ticket.disposalRow = true := by
        rw [← residual_check, exported]
        exact accepted
      simpa [contextOf, pushContext, ExecFrame.erase, closeFrame, ProtectionContexts.frameProtected,
        context_append] using admitted

/-- This bridge identifies the checked plan with the resolved live capture.
    Raw-step construction still leaves ordinary typing, freshness, ownership
    ledger validity and the independent Discardable checks to their judgments. -/
theorem discard_step {ticket : ClauseProtection.Ticket}
    (checked : ClauseProtection.Derives operations policy ticket (contextOf tables front)
      environment .available (.discard ticket.binder) .consumed .scalar outside)
    (built : makePlan capture = some plan)
    (rows : Rows operations plan ticket.disposalRow)
    (accepted : checkFootprint (contextOf tables tail) outside = true)
    (resolve : scope.resolve ticket.binder = some owner)
    (retained : Retained operations (front.append (.live owner input answer capture callerScope tail))) :
    let after := (closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer callerScope tail)))
    RawStep ⟨.discard ticket.binder, scope, front.append (.live owner input answer capture callerScope tail)⟩
      ⟨.unit, scope, after⟩ [.close closeId] [.ticket owner] ∧
      Ready operations (contextOf tables
        (.push (.closing closeId scope) (front.append (.spent owner answer callerScope tail)))) plan ∧
      Retained operations after :=
  ⟨.discard ticket.binder owner closeId scope callerScope input answer front capture tail plan resolve built,
    discard_ready checked rows accepted, discard_retains_callbacks retained built⟩

namespace Examples
open Instantiation Syntax

def cellOperations : Operations := fun requested operation =>
  if requested = .cell 42 ∧ operation = 0 then some (.scalar, .scalar) else none
def cellRow : Footprint := [⟨.cell 42, 0, false⟩]
def cellCallback : Code := .lambda 0
  (.bind 1 (.perform (freezeEffect (.cell 42)) 0 (.resourceRef (.activation 42))) .unit)

theorem cell_callback_summary : Summarizes cellOperations environment cellCallback
    (.function .scalar .scalar cellRow) [] :=
  .lambda (.bind (.perform (input := .scalar) (output := .scalar)
    (by simp [cellOperations]) .reference) .unit)

theorem cell_callback_closed : ClosedValue cellCallback := by
  refine ⟨trivial, rfl, ?_⟩
  intro dependency member
  have shape : dependency = .resource 42 := by
    simpa [cellCallback, Code.dependencies, without, Instance.resources] using member
  subst dependency
  trivial

def cellAction : ActionData := ⟨7, cellCallback, cell_callback_closed, .none, .unit, [.cell 42]⟩
def beforeRelease : List CloseEntry := [.invoke cellAction, .release 42 17]
def afterRelease : List CloseEntry := [.release 42 17, .invoke cellAction]

theorem release_order_changes_row : Rows cellOperations beforeRelease [] ∧
    Rows cellOperations afterRelease [⟨.cell 42, 0, true⟩] := by
  constructor
  · simpa [beforeRelease, callbackResidual, cellRow, qualify, planProvides] using
      (Rows.invoke (action := cellAction) (cell_callback_summary (environment := .empty))
        (Rows.release (identity := 42) (payload := 17) .nil))
  · simpa [afterRelease, callbackResidual, cellRow, qualify, planProvides] using
      (Rows.release (identity := 42) (payload := 17)
        (Rows.invoke (action := cellAction) (cell_callback_summary (environment := .empty)) .nil))

theorem release_order_changes_check : checkFootprint [] (callbackResidual [.release 42 17] cellRow) = true ∧
    checkFootprint [] (callbackResidual [] cellRow) = false := by decide

theorem resource_argument_is_not_provider :
    callbackResidual [.release 42 17] [⟨.user 8 [.resource 42], 0, false⟩] =
      [⟨.user 8 [.resource 42], 0, true⟩] := by decide

def nestedCapture : Stack := .live 9 .unit .unit (.push (.armed cellAction) .nil) .none
  (.push (.cell 42 17 .none .unit) .nil)
def nestedPlan : List CloseEntry := [.invoke cellAction, .retire 9, .release 42 17]

theorem nested_plan_derivation : Retained cellOperations nestedCapture ∧
    makePlan nestedCapture = some nestedPlan ∧ Rows cellOperations nestedPlan [] := by
  refine ⟨⟨⟨⟨.empty, cellRow, cell_callback_summary⟩, trivial⟩, trivial, trivial⟩, rfl, ?_⟩
  simpa [nestedPlan, callbackResidual, cellRow, qualify, planProvides] using
    (Rows.invoke (action := cellAction) (cell_callback_summary (environment := .empty))
      (Rows.retire (owner := 9) (Rows.release (identity := 42) (payload := 17) .nil)))

theorem assembled_suffix_reduces_inner_row :
    Rows cellOperations [.invoke cellAction] [⟨.cell 42, 0, true⟩] ∧
      Ready cellOperations [] nestedPlan := by
  refine ⟨?_, rows_ready nested_plan_derivation.2.2 rfl⟩
  simpa [callbackResidual, cellRow, qualify, planProvides] using
    (Rows.invoke (action := cellAction) (cell_callback_summary (environment := .empty)) .nil)

def disposalTicket : ClauseProtection.Ticket := ⟨3, .scalar, .scalar, false, [], []⟩

theorem cell_discard_clause : ClauseProtection.Derives cellOperations
    (fun _ => ActionRequirements.disposeOnly) disposalTicket [] environment
    .available (.discard 3) .consumed .scalar [] := .discard rfl rfl rfl

theorem actual_nested_discard :
    let outside := Stack.push (.closing 12 (.ticket 3 8)) (.spent 8 .unit .none .nil)
    let after := (closeControl (.ticket 3 8) nestedPlan).append outside
    RawStep ⟨.discard 3, .ticket 3 8, .live 8 .unit .unit nestedCapture .none .nil⟩
      ⟨.unit, .ticket 3 8, after⟩ [.close 12] [.ticket 8] ∧
      Ready cellOperations (contextOf (fun _ => []) outside) nestedPlan ∧
      Retained cellOperations after := by
  exact discard_step (tables := fun _ => []) (front := .nil) (tail := .nil)
    (environment := .empty) cell_discard_clause nested_plan_derivation.2.1
    nested_plan_derivation.2.2 rfl rfl ⟨nested_plan_derivation.1, trivial⟩

theorem invocation_after_retirement :
    let planned := { cellAction with scope := Execution.Scope.ticket 3 9, answer := Ty.unit }
    let suffix := closeControl (.ticket 3 9) [.release 42 17]
    RawStep ⟨.unit, .ticket 3 9, .push (.armed planned) suffix⟩
      ⟨.app cellCallback .unit, .none,
        .push (.running planned .unit ScopedExecution.Examples.unit_closed) suffix⟩ [] [] ∧
      Checked cellOperations (fun _ => []) environment
        (.push (.running planned .unit ScopedExecution.Examples.unit_closed) suffix)
        (.app cellCallback .unit) .scalar := by
  have ready : Ready cellOperations (contextOf (fun _ => []) .nil) (.retire 9 :: beforeRelease) :=
    .retire (rows_ready release_order_changes_row.1 rfl)
  simpa [Stack.append, closeControl, cellAction] using
    invocation_step ready (.later .here) (.ticket 3 9) (environment := environment)

open CallableProtection.Examples (effect operations latent function_summary)
open CallableProtectionFrames.Examples (action)

theorem outward_callback_row : Rows operations [.invoke action] [⟨effect, 0, true⟩] := by
  simpa [callbackResidual, latent, qualify, planProvides] using
    (Rows.invoke (action := action) (function_summary (environment := .empty)) .nil)

theorem outward_protection_checked :
    checkFootprint [.handler effect 11 [(0, ⟨false, some [], some []⟩)]] [⟨effect, 0, true⟩] = true ∧
    checkFootprint [.handler effect 11 [(0, ⟨true, some [], some []⟩)]] [⟨effect, 0, true⟩] = false := by decide

end Examples

end Ash.OneShot.DisposalProtection

#print axioms Ash.OneShot.DisposalProtection.plan_context_realizes
#print axioms Ash.OneShot.DisposalProtection.through_barrier
#print axioms Ash.OneShot.DisposalProtection.protected_request_residual
#print axioms Ash.OneShot.DisposalProtection.protected_row_residual
#print axioms Ash.OneShot.DisposalProtection.callback_residual_exact
#print axioms Ash.OneShot.DisposalProtection.callback_residual_check
#print axioms Ash.OneShot.DisposalProtection.contents_rows
#print axioms Ash.OneShot.DisposalProtection.contents_append
#print axioms Ash.OneShot.DisposalProtection.make_plan_contents
#print axioms Ash.OneShot.DisposalProtection.captured_disposal_row
#print axioms Ash.OneShot.DisposalProtection.retained_append_iff
#print axioms Ash.OneShot.DisposalProtection.contents_retained
#print axioms Ash.OneShot.DisposalProtection.capture_retains_callbacks
#print axioms Ash.OneShot.DisposalProtection.resume_retains_callbacks
#print axioms Ash.OneShot.DisposalProtection.discard_retains_callbacks
#print axioms Ash.OneShot.DisposalProtection.rows_ready
#print axioms Ash.OneShot.DisposalProtection.ready_rows
#print axioms Ash.OneShot.DisposalProtection.ready_iff_rows
#print axioms Ash.OneShot.DisposalProtection.ready_invocation
#print axioms Ash.OneShot.DisposalProtection.invocation_armed
#print axioms Ash.OneShot.DisposalProtection.invocation_step
#print axioms Ash.OneShot.DisposalProtection.discard_ready
#print axioms Ash.OneShot.DisposalProtection.discard_step
#print axioms Ash.OneShot.DisposalProtection.Examples.cell_callback_summary
#print axioms Ash.OneShot.DisposalProtection.Examples.cell_callback_closed
#print axioms Ash.OneShot.DisposalProtection.Examples.release_order_changes_row
#print axioms Ash.OneShot.DisposalProtection.Examples.release_order_changes_check
#print axioms Ash.OneShot.DisposalProtection.Examples.resource_argument_is_not_provider
#print axioms Ash.OneShot.DisposalProtection.Examples.nested_plan_derivation
#print axioms Ash.OneShot.DisposalProtection.Examples.assembled_suffix_reduces_inner_row
#print axioms Ash.OneShot.DisposalProtection.Examples.cell_discard_clause
#print axioms Ash.OneShot.DisposalProtection.Examples.actual_nested_discard
#print axioms Ash.OneShot.DisposalProtection.Examples.invocation_after_retirement
#print axioms Ash.OneShot.DisposalProtection.Examples.outward_callback_row
#print axioms Ash.OneShot.DisposalProtection.Examples.outward_protection_checked
