import CallableProtectionFrames

/-!
Finite residual requirements across ordered interpretation prefixes. This is
analysis of the existing direct-effect calculus, not a new computation syntax.
Handler rows remain supplied; whole retained-code admission remains independent.
-/

namespace Ash.OneShot.ProtectionResiduals
open ProtectionContracts CallableProtectionFrames ScopedExecution

/-- A missing result is a failure inside this prefix. Unhandled demands at its
    outside edge are retained for the eventual receiving context. -/
def merge : Option Footprint → Option Footprint → Option Footprint
  | some left, some right => some (left ++ right)
  | _, _ => none

def checkResidual (context : ProtectionContracts.Context) : Option Footprint → Bool
  | none => false
  | some row => checkFootprint context row

def demandThrough (layer : Layer) (request : Demand) : Option Footprint := match layer with
  | .barrier held => some [{ request with held := request.held || held }]
  | .builtin identity => if request.effect = .cell identity then some [] else some [request]
  | .handler effect _ clauses =>
      if request.effect = effect then
        match lookup request.operation clauses with
        | none => none
        | some contract => if modeCheck contract.dispose request.held then contract.row request.held else none
      else some [request]

def throughLayer (layer : Layer) : Footprint → Option Footprint
  | [] => some []
  | request :: rest => merge (demandThrough layer request) (throughLayer layer rest)

def residualize : ProtectionContracts.Context → Footprint → Option Footprint
  | [], row => some row
  | layer :: rest, row => match throughLayer layer row with
      | none => none
      | some next => residualize rest next

theorem through_builtin (identity : Nat) (row : Footprint) :
    throughLayer (.builtin identity) row = some (CallableProtection.outsideCell identity row) := by
  induction row with
  | nil => rfl
  | cons request rest ih =>
      by_cases same : request.effect = .cell identity <;>
        simp [throughLayer, demandThrough, CallableProtection.outsideCell, same, ih, merge]

/-- Opening a resource discharges exactly the local builtin requests before
    the remaining ordered interpretations see the outward footprint. -/
theorem residual_builtin (identity : Nat) (row : Footprint) (tail : ProtectionContracts.Context) :
    residualize (.builtin identity :: tail) row = residualize tail (CallableProtection.outsideCell identity row) := by
  simp only [residualize, through_builtin]

theorem check_merge (context : ProtectionContracts.Context) (left right : Option Footprint) :
    checkResidual context (merge left right) = (checkResidual context left && checkResidual context right) := by
  cases left <;> cases right <;> simp [merge, checkResidual, check_footprint_append]

theorem demand_through_check (layer : Layer) (context : ProtectionContracts.Context) (request : Demand) :
    checkResidual context (demandThrough layer request) = checkRequest (layer :: context) request := by
  cases layer with
  | barrier held => simp [demandThrough, checkResidual, checkFootprint, checkRequest]
  | builtin identity =>
      by_cases same : request.effect = .cell identity <;>
        simp [demandThrough, checkResidual, checkFootprint, checkRequest, same]
  | handler effect activation clauses =>
      by_cases same : request.effect = effect
      · cases known : lookup request.operation clauses with
        | none => simp [demandThrough, checkResidual, checkRequest, same, known]
        | some contract =>
            cases permitted : modeCheck contract.dispose request.held <;>
              cases row : contract.row request.held <;>
              simp [demandThrough, checkResidual, checkFootprint, checkRequest, same, known, permitted, row]
      · simp [demandThrough, checkResidual, checkFootprint, checkRequest, same]

theorem through_layer_check (layer : Layer) (context : ProtectionContracts.Context) (row : Footprint) :
    checkResidual context (throughLayer layer row) = checkFootprint (layer :: context) row := by
  induction row with
  | nil => rfl
  | cons request rest ih =>
      simp only [throughLayer, check_merge, demand_through_check, ih, checkFootprint, List.all_cons]

/-- Every outside context sees exactly the residual of the prefix. -/
theorem residual_check (front tail : ProtectionContracts.Context) (row : Footprint) :
    checkResidual tail (residualize front row) = checkFootprint (front ++ tail) row := by
  induction front generalizing row with
  | nil => rfl
  | cons layer rest ih =>
      have first := through_layer_check layer (rest ++ tail) row
      cases next : throughLayer layer row with
      | none => simpa [residualize, next, checkResidual] using first
      | some output => simpa [residualize, next, checkResidual, ← ih] using first

theorem residual_append (front middle : ProtectionContracts.Context) (row : Footprint) :
    residualize (front ++ middle) row =
      match residualize front row with
      | none => none
      | some next => residualize middle next := by
  induction front generalizing row with
  | nil => rfl
  | cons layer rest ih =>
      cases next : throughLayer layer row <;> simp [residualize, next, ih]

theorem residual_admitted_iff : checkFootprint (front ++ tail) row = true ↔
    ∃ output, residualize front row = some output ∧ checkFootprint tail output = true := by
  rw [← residual_check]
  cases next : residualize front row <;> simp [checkResidual]

theorem residual_empty (context : ProtectionContracts.Context) : residualize context [] = some [] := by
  induction context with
  | nil => rfl
  | cons layer rest ih => simpa [residualize, throughLayer] using ih

theorem merge_assoc (a b c : Option Footprint) : merge (merge a b) c = merge a (merge b c) := by
  cases a <;> cases b <;> cases c <;> simp [merge, List.append_assoc]

theorem through_layer_append (layer : Layer) (left right : Footprint) :
    throughLayer layer (left ++ right) = merge (throughLayer layer left) (throughLayer layer right) := by
  induction left with
  | nil => cases known : throughLayer layer right <;> simp [throughLayer, merge, known]
  | cons request rest ih => simp [throughLayer, ih, merge_assoc]

theorem residual_rows_append (context : ProtectionContracts.Context) (left right : Footprint) :
    residualize context (left ++ right) = merge (residualize context left) (residualize context right) := by
  induction context generalizing left right with
  | nil => rfl
  | cons layer rest ih =>
      simp only [residualize, through_layer_append]
      cases a : throughLayer layer left <;> cases b : throughLayer layer right <;> simp [merge, ih]

theorem push_context_append (tables : Tables) (frame : ExecFrame) (left right : ProtectionContracts.Context) :
    pushContext tables frame (left ++ right) = pushContext tables frame left ++ right := by
  cases frame <;> rfl

theorem context_append (tables : Tables) (front tail : Stack) :
    contextOf tables (front.append tail) = contextOf tables front ++ contextOf tables tail := by
  induction front with
  | nil => rfl
  | push frame rest ih => simp only [Stack.append, contextOf, ih, push_context_append]
  | live owner input answer saved scope rest ihSaved ihRest =>
      simp only [Stack.append, contextOf, ihRest, List.cons_append]
  | spent owner answer scope rest ih => exact ih

theorem stack_residual_check (tables : Tables) (front tail : Stack) (row : Footprint) :
    checkFootprint (contextOf tables (front.append tail)) row =
      checkResidual (contextOf tables tail) (residualize (contextOf tables front) row) := by
  rw [context_append, residual_check]

/-- This is the exact stack installed by RawStep.resume. A residual obtained
    from the captured prefix must be checked against the waiting caller frames
    followed by the surviving tail, in that order. -/
theorem resume_requirements (tables : Tables) (capture front tail : Stack) (row : Footprint) :
    checkFootprint (contextOf tables (capture.append (front.append (.spent owner answer scope tail)))) row =
      checkResidual (contextOf tables (front.append tail)) (residualize (contextOf tables capture) row) := by
  rw [stack_residual_check, context_append, context_append]
  rfl

theorem resume_admitted_iff (tables : Tables) (capture front tail : Stack) (row : Footprint) :
    checkFootprint (contextOf tables (capture.append (front.append (.spent owner answer scope tail)))) row = true ↔
      ∃ outside, residualize (contextOf tables capture) row = some outside ∧
        checkFootprint (contextOf tables (front.append tail)) outside = true := by
  rw [resume_requirements]
  cases next : residualize (contextOf tables capture) row <;> simp [checkResidual]

/-- Capture derives an outside residual from an already checked footprint.
    Restoring the same captured prefix preserves that residual, but its caller
    context must be checked again; arbitrary waiting frames need not admit it. -/
theorem capture_resume_recomposition
    (cut : HandlerCut requested whole capture tail handler)
    (checked : checkFootprint (contextOf tables whole) row = true) :
    ∃ outside, residualize (contextOf tables capture) row = some outside ∧
      checkFootprint (contextOf tables tail) outside = true ∧
      ∀ (front : Stack) (owner : Nat) (answer : Ty) (scope : Scope),
        checkFootprint (contextOf tables (capture.append (front.append (.spent owner answer scope tail)))) row =
          checkFootprint (contextOf tables (front.append tail)) outside := by
  rw [handler_cut_reconstructs cut, context_append] at checked
  obtain ⟨outside, derived, admitted⟩ := residual_admitted_iff.mp checked
  refine ⟨outside, derived, admitted, ?_⟩
  intro front owner answer scope
  rw [resume_requirements, derived]
  rfl

namespace Examples

def effectE : Instance := .user 0 []
def effectF : Instance := .user 1 []
def demandE : Footprint := [⟨effectE, 0, false⟩]
def demandF : Footprint := [⟨effectF, 0, false⟩]
def heldF : Footprint := [⟨effectF, 0, true⟩]
def disposableE : Layer := .handler effectE 11 [(0, ⟨true, some [], none⟩)]
def disposableF : Layer := .handler effectF 22 [(0, ⟨true, some [], none⟩)]
def afterCompletion : Layer := .handler effectE 11 [(0, ⟨false, some demandF, some demandF⟩)]
def beforeCompletion : Layer := .handler effectE 11 [(0, ⟨false, some demandF, some heldF⟩)]

theorem empty_prefix_exports : residualize [] demandE = some demandE ∧ checkFootprint [] demandE = false := by decide

theorem phase_specific_export : residualize [.barrier true, afterCompletion] demandE = some demandF ∧
    checkFootprint [.barrier true, afterCompletion, disposableF] demandE = true := by decide

theorem surviving_barrier_rejects :
    checkFootprint [.barrier true, afterCompletion, .barrier true, disposableF] demandE = false := by decide

theorem owned_protection_exports : residualize [.barrier true, beforeCompletion] demandE = some heldF ∧
    checkFootprint [.barrier true, beforeCompletion, disposableF] demandE = false := by decide

theorem handler_order_matters : residualize [disposableE, .barrier true] demandE = some [] ∧
    residualize [.barrier true, disposableE] demandE = none := by decide

theorem missing_operation_cannot_fall_through :
    residualize [.handler effectE 11 []] demandE = none ∧
    checkFootprint [.handler effectE 11 [], disposableE] demandE = false := by decide

theorem no_mode_weakening :
    let protectedOnly := Layer.handler effectE 11 [(0, ⟨false, none, some []⟩)]
    residualize [.barrier true, protectedOnly] demandE = some [] ∧
      residualize [protectedOnly] demandE = none := by decide

open ScopedExpressions Instantiation

def handlerE : HandlerData :=
  ⟨11, effectE, .cons 0 0 0 (.bind 1 (.perform (freezeEffect effectF) 0 .unit) (.resume 0 .unit)) .nil,
    .none, .unit, rfl⟩
def handlerF : HandlerData := ⟨22, effectF, .cons 0 0 2 (.resume 2 .unit) .nil, .none, .unit, rfl⟩
def interveningF : HandlerData := ⟨33, effectF, .cons 0 0 3 (.discard 3) .nil, .none, .unit, rfl⟩
def policy : Syntax.TicketPolicy := fun binder => if binder = 3 then ActionRequirements.disposeOnly else ActionRequirements.resumeOnly
def rows : HandlerData → ClauseRows := fun handler _ _ _ _ =>
  if handler.activation = 11 then (some demandF, some heldF) else (some [], some [])
def tables : Tables := policyTables policy rows

def capture : Stack := .push
  (.running CallableProtectionFrames.Examples.action .unit CallableProtection.Examples.unit_closed)
  (.push (.handler handlerE) .nil)
def tail : Stack := .push (.handler handlerF) .nil
def front : Stack := .push (.handler interveningF) .nil

theorem original_context_accepts : checkFootprint (contextOf tables (capture.append tail)) demandE = true := by decide

theorem resumed_context_rejects :
    checkFootprint (contextOf tables (capture.append (front.append (.spent 8 .unit .none tail)))) demandE = false := by decide

theorem waiting_handler_rejects_residual :
    residualize (contextOf tables capture) demandE = some heldF ∧
      checkFootprint (contextOf tables (front.append tail)) heldF = false := by decide

theorem dormant_handler_is_not_active :
    checkFootprint (contextOf tables (.live 8 .unit .unit capture .none tail)) demandE = false := by decide

end Examples

end Ash.OneShot.ProtectionResiduals

#print axioms Ash.OneShot.ProtectionResiduals.check_merge
#print axioms Ash.OneShot.ProtectionResiduals.demand_through_check
#print axioms Ash.OneShot.ProtectionResiduals.through_layer_check
#print axioms Ash.OneShot.ProtectionResiduals.residual_check
#print axioms Ash.OneShot.ProtectionResiduals.through_builtin
#print axioms Ash.OneShot.ProtectionResiduals.residual_builtin
#print axioms Ash.OneShot.ProtectionResiduals.residual_append
#print axioms Ash.OneShot.ProtectionResiduals.residual_admitted_iff
#print axioms Ash.OneShot.ProtectionResiduals.residual_empty
#print axioms Ash.OneShot.ProtectionResiduals.merge_assoc
#print axioms Ash.OneShot.ProtectionResiduals.through_layer_append
#print axioms Ash.OneShot.ProtectionResiduals.residual_rows_append
#print axioms Ash.OneShot.ProtectionResiduals.push_context_append
#print axioms Ash.OneShot.ProtectionResiduals.context_append
#print axioms Ash.OneShot.ProtectionResiduals.stack_residual_check
#print axioms Ash.OneShot.ProtectionResiduals.resume_requirements
#print axioms Ash.OneShot.ProtectionResiduals.resume_admitted_iff
#print axioms Ash.OneShot.ProtectionResiduals.Examples.empty_prefix_exports
#print axioms Ash.OneShot.ProtectionResiduals.Examples.phase_specific_export
#print axioms Ash.OneShot.ProtectionResiduals.Examples.surviving_barrier_rejects
#print axioms Ash.OneShot.ProtectionResiduals.Examples.owned_protection_exports
#print axioms Ash.OneShot.ProtectionResiduals.Examples.handler_order_matters
#print axioms Ash.OneShot.ProtectionResiduals.Examples.missing_operation_cannot_fall_through
#print axioms Ash.OneShot.ProtectionResiduals.Examples.no_mode_weakening
#print axioms Ash.OneShot.ProtectionResiduals.Examples.original_context_accepts
#print axioms Ash.OneShot.ProtectionResiduals.Examples.resumed_context_rejects
#print axioms Ash.OneShot.ProtectionResiduals.Examples.waiting_handler_rejects_residual
#print axioms Ash.OneShot.ProtectionResiduals.Examples.dormant_handler_is_not_active

#print axioms Ash.OneShot.ProtectionResiduals.capture_resume_recomposition
