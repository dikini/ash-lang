import ProtectionResiduals

/-!
Source clause requirements indexed by the existing one-shot usage states.
Captured execution/closing footprints are inputs; authenticating those inputs
against retained control and integrating handler/resource rules remain open.
-/

namespace Ash.OneShot.ClauseProtection
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open Syntax (TicketPolicy UseState UseScope)
open Instantiation (freezeEffect)

structure Ticket where
  binder : Nat
  input : Contract
  answer : Contract
  held : Bool
  resumeRow : Footprint
  disposalRow : Footprint
  deriving DecidableEq, Repr

variable {ticket : Ticket}

def ownedMode (ticket : Ticket) : UseState → Bool
  | .available => ticket.held
  | .consumed => false

def phaseContext (ticket : Ticket) (inside : ProtectionContracts.Context) (state : UseState) :
    ProtectionContracts.Context := inside ++ [.barrier (ownedMode ticket state)]

def exportAt (ticket : Ticket) (inside : ProtectionContracts.Context) (state : UseState) (row : Footprint) :
    Option Footprint := residualize (phaseContext ticket inside state) row

/-- The stable source component has no ticket actions, including inside lambdas. -/
theorem stable_usage (summary : Summarizes operations environment code contract row)
    (policy : TicketPolicy) (scope : UseScope) (state : UseState) :
    ScopedExpressions.Uses policy scope state code state := by
  induction summary generalizing scope state with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .resourceRef
  | «variable» => exact .variable
  | pair left right ihLeft ihRight => exact .pair (ihLeft scope state) (ihRight scope state)
  | lambda body ih => exact .lambda (ih .none .available)
  | app function argument ihFunction ihArgument => exact .app (ihFunction scope state) (ihArgument scope state)
  | bind initializer body ihInit ihBody => exact .bind (ihInit scope state) (ihBody scope state)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch (ihCondition scope state) (ihYes scope state) (ihNo scope state)
  | perform known operand ih => exact .perform (ih scope state)
  | cleanup callback body ihCallback ihBody => exact .cleanup (ihCallback scope state) (ihBody scope state)
  | resource initializer body outward ihInit ihBody =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource (ihInit scope state)
        ((instantiation_preserves_usage_iff _ _).mp (ihBody identity fresh scope state))

inductive Derives (operations : Operations) (policy : TicketPolicy) (ticket : Ticket)
    (inside : ProtectionContracts.Context) :
    CallableProtection.Environment → UseState → Code → UseState → Contract → Footprint → Prop where
  | stable (summary : Summarizes operations environment code contract row)
      (exported : exportAt ticket inside state row = some outside) :
      Derives operations policy ticket inside environment state code state contract outside
  | pair (left : Derives operations policy ticket inside environment before a middle first leftRow)
      (right : Derives operations policy ticket inside environment middle b after second rightRow) :
      Derives operations policy ticket inside environment before (.pair a b) after (.pair first second) (leftRow ++ rightRow)
  | app (function : Derives operations policy ticket inside environment before f middle (.function input output latent) functionRow)
      (argument : Derives operations policy ticket inside environment middle a after input argumentRow)
      (exported : exportAt ticket inside after latent = some invocationRow) :
      Derives operations policy ticket inside environment before (.app f a) after output (functionRow ++ argumentRow ++ invocationRow)
  | bind (initializer : Derives operations policy ticket inside environment before a middle input initializerRow)
      (body : Derives operations policy ticket inside (environment.extend parameter input) middle b after output bodyRow) :
      Derives operations policy ticket inside environment before (.bind parameter a b) after output (initializerRow ++ bodyRow)
  | branch (condition : Derives operations policy ticket inside environment before test middle .scalar conditionRow)
      (yes : Derives operations policy ticket inside environment middle a after output yesRow)
      (no : Derives operations policy ticket inside environment middle b after output noRow) :
      Derives operations policy ticket inside environment before (.branch test a b) after output (conditionRow ++ yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output))
      (operand : Derives operations policy ticket inside environment before value after input operandRow)
      (exported : exportAt ticket inside after [⟨effect, operation, false⟩] = some requestRow) :
      Derives operations policy ticket inside environment before (.perform (freezeEffect effect) operation value) after output
        (operandRow ++ requestRow)
  | resume (allowed : (policy ticket.binder).resume = true)
      (operand : Derives operations policy ticket inside environment before value .available ticket.input operandRow)
      (exported : residualize inside ticket.resumeRow = some resumedRow) :
      Derives operations policy ticket inside environment before (.resume ticket.binder value) .consumed ticket.answer
        (operandRow ++ resumedRow)
  | discard (allowed : (policy ticket.binder).dispose = true) (unprotected : ticket.held = false)
      (exported : residualize (.barrier true :: inside) ticket.disposalRow = some closingRow) :
      Derives operations policy ticket inside environment .available (.discard ticket.binder) .consumed .scalar closingRow
  | cleanup (callback : Derives operations policy ticket inside environment before action middle (.function .scalar .scalar latent) callbackRow)
      (body : Derives operations policy ticket inside environment middle code after output bodyRow)
      (exported : residualize (.barrier true :: phaseContext ticket inside after) latent = some executionRow) :
      Derives operations policy ticket inside environment before (.cleanup action code) after output
        (callbackRow ++ bodyRow ++ executionRow)
  | resource {world : List Nat} {bodyRow : Nat → Footprint}
      (initializer : Derives operations policy ticket inside environment before initial after .scalar initialRow)
      (body : ∀ identity, identity ∉ world → Summarizes operations environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (outward : ∀ identity, identity ∉ world → outsideCell identity (bodyRow identity) = raw)
      (exported : exportAt ticket inside after raw = some row) :
      Derives operations policy ticket inside environment before (.resource binder initial code) after output (initialRow ++ row)

theorem derives_usage (checked : Derives operations policy ticket inside environment before code after contract row) :
    ScopedExpressions.Uses policy (.ticket ticket.binder (policy ticket.binder)) before code after := by
  induction checked with
  | stable summary exported => exact stable_usage summary policy _ _
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument exported ihFunction ihArgument => exact .app ihFunction ihArgument
  | bind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known operand exported ih => exact .perform ih
  | resume allowed operand exported ih => exact .resume allowed ih
  | discard allowed unprotected exported => exact .discard allowed
  | cleanup callback body exported ihCallback ihBody => exact .cleanup ihCallback ihBody
  | resource initializer body outward exported ih =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource ih ((instantiation_preserves_usage_iff _ _).mp (stable_usage (body identity fresh) policy _ _))

theorem phase_monotone (checked : Derives operations policy ticket inside environment before code after contract row) :
    before = .consumed → after = .consumed := Syntax.use_state_monotone (derives_usage checked)

theorem export_check (exported : exportAt ticket inside state row = some outside) :
    checkFootprint (phaseContext ticket inside state ++ tail) row = checkFootprint tail outside := by
  unfold exportAt at exported
  rw [← residual_check, exported]
  rfl

theorem resume_export_check (exported : residualize inside ticket.resumeRow = some outside) :
    checkFootprint (inside ++ tail) ticket.resumeRow = checkFootprint tail outside := by
  rw [← residual_check, exported]
  rfl

theorem discard_export_check (exported : residualize (.barrier true :: inside) ticket.disposalRow = some outside) :
    checkFootprint ((.barrier true :: inside) ++ tail) ticket.disposalRow = checkFootprint tail outside := by
  rw [← residual_check, exported]
  rfl

theorem environment_congr (checked : Derives operations policy ticket inside source before code after contract row)
    (agree : AgreeOn source destination code.dependencies) :
    Derives operations policy ticket inside destination before code after contract row := by
  induction checked generalizing destination with
  | stable summary exported => exact .stable (CallableProtection.environment_congr summary agree) exported
  | pair left right ihLeft ihRight => exact .pair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | app function argument exported ihFunction ihArgument =>
      exact .app (ihFunction (agree_left agree)) (ihArgument (agree_right agree)) exported
  | bind initializer body ihInit ihBody => exact .bind (ihInit (agree_left agree)) (ihBody (agree_extend (agree_right agree)))
  | branch condition yes no ihCondition ihYes ihNo =>
      exact .branch (ihCondition (agree_left (agree_left agree))) (ihYes (agree_right (agree_left agree))) (ihNo (agree_right agree))
  | perform known operand exported ih => exact .perform known (ih (agree_right agree)) exported
  | resume allowed operand exported ih =>
      exact .resume allowed (ih (fun name member => agree name (List.mem_cons_of_mem _ member))) exported
  | discard allowed unprotected exported => exact .discard allowed unprotected exported
  | cleanup callback body exported ihCallback ihBody =>
      exact .cleanup (ihCallback (agree_left agree)) (ihBody (agree_right agree)) exported
  | resource initializer body outward exported ih =>
      exact .resource (ih (agree_left agree))
        (fun identity fresh => CallableProtection.environment_congr (body identity fresh)
          (agree_resource_opening (agree_right agree))) outward exported

/-- Closed parameter substitution preserves both endpoint phases and the exact
    exported footprint. The replacement retains its complete callable contract. -/
theorem substitution
    (checked : Derives operations policy ticket inside (environment.extend name input) before code after result row)
    (replacement : Summarizes operations environment value input []) (closed : ClosedValue value) :
    Derives operations policy ticket inside environment before (code.subst name value) after result row := by
  cases checked with
  | stable summary exported => exact .stable (CallableProtection.substitution summary replacement closed) exported
  | pair left right => exact .pair (substitution left replacement closed) (substitution right replacement closed)
  | app function argument exported => exact .app (substitution function replacement closed) (substitution argument replacement closed) exported
  | bind initializer body =>
      rename_i a middle domain initializerRow parameter b bodyRow
      apply Derives.bind (substitution initializer replacement closed)
      by_cases same : name = parameter
      · subst parameter
        simpa only [ite_true, CallableProtection.Environment.extend_shadow] using body
      · simp only [if_neg same]
        have rearranged := body
        rw [CallableProtection.Environment.extend_commute environment name parameter input domain same] at rearranged
        exact substitution rearranged
          (closed_value_environment replacement closed (environment.extend parameter domain)) closed
  | branch condition yes no =>
      exact .branch (substitution condition replacement closed) (substitution yes replacement closed) (substitution no replacement closed)
  | perform known operand exported => exact .perform known (substitution operand replacement closed) exported
  | resume allowed operand exported => exact .resume allowed (substitution operand replacement closed) exported
  | discard allowed unprotected exported => exact .discard allowed unprotected exported
  | cleanup callback body exported =>
      exact .cleanup (substitution callback replacement closed) (substitution body replacement closed) exported
  | resource initializer body outward exported =>
      apply Derives.resource (substitution initializer replacement closed) _ outward exported
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact CallableProtection.substitution (body identity fresh) replacement closed
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes]; all_goals omega

theorem value_summary (checked : Derives operations policy ticket inside environment before value after contract row)
    (isValue : value.IsValue) :
    Summarizes operations environment value contract [] ∧ before = after ∧ row = [] := by
  induction checked with
  | stable summary exported =>
      have empty := value_has_no_immediate_demands summary isValue
      subst_vars
      have output : [] = _ := Option.some.inj (by simpa [exportAt, residual_empty] using exported)
      exact ⟨summary, rfl, output.symm⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨leftSummary, leftState, leftRow⟩ := ihLeft isValue.1
      obtain ⟨rightSummary, rightState, rightRow⟩ := ihRight isValue.2
      subst_vars
      exact ⟨Summarizes.pair leftSummary rightSummary, rfl, rfl⟩
  | app | bind | branch | perform | resume | discard | cleanup | resource => cases isValue

theorem bind_summary
    (checked : Derives operations policy ticket inside environment before (.bind parameter value body) after result row)
    (closed : ClosedValue value) :
    Derives operations policy ticket inside environment before (body.subst parameter value) after result row := by
  cases checked with
  | stable summary exported => exact .stable (CallableProtection.bind_summary summary closed) exported
  | bind initializer body =>
      obtain ⟨replacement, same, empty⟩ := value_summary initializer closed.1
      subst_vars
      simpa using substitution body replacement closed

theorem beta_summary
    (checked : Derives operations policy ticket inside environment before (.app (.lambda parameter body) value) after result row)
    (closed : ClosedValue value) :
    Derives operations policy ticket inside environment before (body.subst parameter value) after result row := by
  cases checked with
  | stable summary exported => exact .stable (CallableProtection.beta_summary summary closed) exported
  | app function argument exported =>
      obtain ⟨functionSummary, functionState, functionRow⟩ := value_summary function trivial
      obtain ⟨argumentSummary, argumentState, argumentRow⟩ := value_summary argument closed.1
      subst_vars
      cases functionSummary with
      | lambda body =>
          simpa using Derives.stable (policy := policy)
            (CallableProtection.substitution body argumentSummary closed) exported

theorem available_stack_check (tables : CallableProtectionFrames.Tables) (front capture tail : Stack)
    (held : ticket.held = ProtectionContexts.protectedMode capture.erase) :
    checkFootprint (phaseContext ticket (CallableProtectionFrames.contextOf tables front) .available ++
      CallableProtectionFrames.contextOf tables tail) row =
      checkFootprint (CallableProtectionFrames.contextOf tables
        (front.append (.live owner input answer capture scope tail))) row := by
  simp [phaseContext, ownedMode, context_append, CallableProtectionFrames.contextOf, held, List.append_assoc]

theorem false_barrier_check (inside tail : ProtectionContracts.Context) (row : Footprint) :
    checkFootprint (inside ++ .barrier false :: tail) row = checkFootprint (inside ++ tail) row := by
  rw [← residual_check, ← residual_check]
  cases residualize inside row <;> simp [checkResidual, checkFootprint, checkRequest]

theorem consumed_stack_check (tables : CallableProtectionFrames.Tables) (front tail : Stack) :
    checkFootprint (phaseContext ticket (CallableProtectionFrames.contextOf tables front) .consumed ++
      CallableProtectionFrames.contextOf tables tail) row =
      checkFootprint (CallableProtectionFrames.contextOf tables (front.append (.spent owner answer scope tail))) row := by
  simp [phaseContext, ownedMode, context_append, CallableProtectionFrames.contextOf, List.append_assoc, false_barrier_check]

theorem protected_discard_rejected (held : ticket.held = true) :
    ¬ Derives operations policy ticket inside environment before (.discard binder) after contract row := by
  intro checked
  cases checked with
  | stable summary exported => cases summary
  | discard allowed unprotected exported => simp [held] at unprotected

theorem consumed_resume_rejected :
    ¬ Derives operations policy ticket inside environment .consumed (.resume binder operand) after contract row := by
  intro checked
  cases checked with
  | stable summary exported => cases summary
  | resume allowed operand exported => cases phase_monotone operand rfl

/-- When the supplied captured residual is realized, the resume rule's export
    is exactly the check at the stack installed by raw resumption. -/
theorem resume_stack_check (tables : CallableProtectionFrames.Tables) (capture front tail : Stack)
    (captured : residualize (CallableProtectionFrames.contextOf tables capture) row = some ticket.resumeRow)
    (exported : residualize (CallableProtectionFrames.contextOf tables front) ticket.resumeRow = some outside) :
    checkFootprint (CallableProtectionFrames.contextOf tables
      (capture.append (front.append (.spent owner answer scope tail)))) row =
      checkFootprint (CallableProtectionFrames.contextOf tables tail) outside := by
  rw [resume_requirements, captured]
  change checkFootprint (CallableProtectionFrames.contextOf tables (front.append tail)) ticket.resumeRow = _
  rw [context_append, ← residual_check, exported]
  rfl

/-- The closing barrier remains outside the planned frames and inside the
    waiting caller frames. Plan construction and row provenance are separate. -/
theorem closing_stack_check (tables : CallableProtectionFrames.Tables) (plan : List CloseEntry) (front tail : Stack)
    (planned : residualize (CallableProtectionFrames.contextOf tables (closeControl scope plan)) row = some ticket.disposalRow)
    (exported : residualize (.barrier true :: CallableProtectionFrames.contextOf tables front) ticket.disposalRow = some outside) :
    checkFootprint (CallableProtectionFrames.contextOf tables
      ((closeControl scope plan).append (.push (.closing identity scope) (front.append (.spent owner answer caller tail))))) row =
      checkFootprint (CallableProtectionFrames.contextOf tables tail) outside := by
  rw [stack_residual_check, planned]
  change checkFootprint (.barrier true :: CallableProtectionFrames.contextOf tables
    (front.append (.spent owner answer caller tail))) ticket.disposalRow = _
  rw [context_append]
  change checkFootprint ((.barrier true :: CallableProtectionFrames.contextOf tables front) ++
    CallableProtectionFrames.contextOf tables tail) ticket.disposalRow = _
  rw [← residual_check, exported]
  rfl

namespace Examples

def effectF : Instance := .user 1 []
def effectG : Instance := .user 2 []
def operations : Operations := fun _ _ => some (.scalar, .scalar)
def policy : TicketPolicy := fun _ => ActionRequirements.resumeOnly
def capturedTicket : Ticket := ⟨0, .scalar, .scalar, true, [⟨effectG, 0, true⟩], []⟩
def requestF : Code := .perform (freezeEffect effectF) 0 .unit

theorem unit_summary (phase : UseState) :
    Derives operations policy capturedTicket inside environment phase .unit phase .scalar [] :=
  .stable .unit (by simp [exportAt, residual_empty])

theorem request_summary (phase : UseState) :
    Derives operations policy capturedTicket [] environment phase requestF phase .scalar [⟨effectF, 0, ownedMode capturedTicket phase⟩] := by
  cases phase <;> exact .stable (.perform rfl .unit) rfl

theorem resume_summary : Derives operations policy capturedTicket [] environment .available
    (.resume 0 .unit) .consumed .scalar [⟨effectG, 0, true⟩] :=
  .resume rfl (unit_summary .available) rfl

def surrounding : Code := .bind 1 requestF (.bind 2 (.resume 0 .unit) requestF)

theorem before_during_after : Derives operations policy capturedTicket [] environment .available surrounding .consumed .scalar
    [⟨effectF, 0, true⟩, ⟨effectG, 0, true⟩, ⟨effectF, 0, false⟩] := by
  exact .bind (request_summary .available) (.bind resume_summary (request_summary .consumed))

theorem source_usage : ScopedExpressions.Uses policy (.ticket 0 (policy 0)) .available surrounding .consumed :=
  derives_usage (before_during_after (environment := CallableProtection.Environment.empty))

theorem double_resume_rejected :
    ¬ Derives operations policy capturedTicket [] environment .available
      (.bind 1 (.resume 0 .unit) (.resume 0 .unit)) after contract row := by
  intro checked
  have usage := derives_usage checked
  cases usage with
  | bind first second => cases first with
      | resume allowed operand => cases second with
          | resume allowed operand => cases Syntax.use_state_monotone operand rfl

theorem lambda_cannot_capture_ticket :
    ¬ Derives operations policy capturedTicket [] environment before (.lambda 1 (.resume 0 .unit)) after contract row := by
  intro checked
  have usage := derives_usage checked
  cases usage with
  | lambda body => cases body

theorem inherited_barrier_survives :
    exportAt capturedTicket [.barrier true] .consumed [⟨effectF, 0, false⟩] = some [⟨effectF, 0, true⟩] := rfl

def callback : Code := .lambda 1 requestF

theorem cleanup_after_resume : Derives operations policy capturedTicket [] environment .available
    (.cleanup callback (.resume 0 .unit)) .consumed .scalar
      [⟨effectG, 0, true⟩, ⟨effectF, 0, true⟩] := by
  exact .cleanup (.stable (.lambda (.perform rfl .unit)) rfl) resume_summary rfl

def disposable : Ticket := { capturedTicket with held := false, resumeRow := [], disposalRow := [⟨effectG, 0, false⟩] }
def disposalPolicy : TicketPolicy := fun _ => ActionRequirements.disposeOnly

theorem disposal_closing_barrier : Derives operations disposalPolicy disposable [] environment .available
    (.discard 0) .consumed .scalar [⟨effectG, 0, true⟩] := .discard rfl rfl rfl

end Examples

end Ash.OneShot.ClauseProtection

#print axioms Ash.OneShot.ClauseProtection.stable_usage
#print axioms Ash.OneShot.ClauseProtection.derives_usage
#print axioms Ash.OneShot.ClauseProtection.phase_monotone
#print axioms Ash.OneShot.ClauseProtection.export_check
#print axioms Ash.OneShot.ClauseProtection.resume_export_check
#print axioms Ash.OneShot.ClauseProtection.discard_export_check
#print axioms Ash.OneShot.ClauseProtection.environment_congr
#print axioms Ash.OneShot.ClauseProtection.substitution
#print axioms Ash.OneShot.ClauseProtection.value_summary
#print axioms Ash.OneShot.ClauseProtection.bind_summary
#print axioms Ash.OneShot.ClauseProtection.beta_summary
#print axioms Ash.OneShot.ClauseProtection.available_stack_check
#print axioms Ash.OneShot.ClauseProtection.false_barrier_check
#print axioms Ash.OneShot.ClauseProtection.consumed_stack_check
#print axioms Ash.OneShot.ClauseProtection.protected_discard_rejected
#print axioms Ash.OneShot.ClauseProtection.consumed_resume_rejected
#print axioms Ash.OneShot.ClauseProtection.Examples.unit_summary
#print axioms Ash.OneShot.ClauseProtection.Examples.request_summary
#print axioms Ash.OneShot.ClauseProtection.Examples.resume_summary
#print axioms Ash.OneShot.ClauseProtection.Examples.before_during_after
#print axioms Ash.OneShot.ClauseProtection.Examples.source_usage
#print axioms Ash.OneShot.ClauseProtection.Examples.double_resume_rejected
#print axioms Ash.OneShot.ClauseProtection.Examples.lambda_cannot_capture_ticket
#print axioms Ash.OneShot.ClauseProtection.Examples.inherited_barrier_survives
#print axioms Ash.OneShot.ClauseProtection.Examples.cleanup_after_resume
#print axioms Ash.OneShot.ClauseProtection.Examples.disposal_closing_barrier

#print axioms Ash.OneShot.ClauseProtection.resume_stack_check
#print axioms Ash.OneShot.ClauseProtection.closing_stack_check
