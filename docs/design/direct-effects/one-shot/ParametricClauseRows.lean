import CaptureInterfaces

/-!
Structural clause schemas with explicit resumption and disposal row parameters.
These are analysis expressions for the existing Code and Derives judgments,
not additional computation syntax. Specialization must still be integrated with
ordered interpretation and source admission throughout execution.
-/

namespace Ash.OneShot.ParametricClauseRows
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open ClauseProtection (Ticket Derives)
open Syntax (TicketPolicy UseState)

structure Header where
  binder : Nat
  input : Contract
  answer : Contract
  held : Bool
  deriving DecidableEq, Repr

def Header.ticket (header : Header) (resumeRow : Footprint) (closeRow : Option Footprint) : Ticket :=
  ⟨header.binder, header.input, header.answer, header.held, resumeRow, closeRow.getD []⟩

def Header.context (header : Header) (inside : ProtectionContracts.Context) (phase : UseState) : ProtectionContracts.Context :=
  ClauseProtection.phaseContext (header.ticket [] none) inside phase

inductive RowExpr where
  | literal : Footprint → RowExpr
  | resume : RowExpr
  | disposal : RowExpr
  | append : RowExpr → RowExpr → RowExpr
  | through : ProtectionContracts.Context → RowExpr → RowExpr
  deriving DecidableEq, Repr

def RowExpr.eval (resumeRow : Footprint) (closeRow : Option Footprint) : RowExpr → Option Footprint
  | .literal row => some row
  | .resume => some resumeRow
  | .disposal => closeRow
  | .append first second => merge (first.eval resumeRow closeRow) (second.eval resumeRow closeRow)
  | .through context row => match row.eval resumeRow closeRow with
      | none => none
      | some raw => residualize context raw

theorem eval_append
    (left : RowExpr.eval resumeRow closeRow first = some a)
    (right : RowExpr.eval resumeRow closeRow second = some b) :
    RowExpr.eval resumeRow closeRow (.append first second) = some (a ++ b) := by
  simp only [RowExpr.eval, left, right, merge]

theorem eval_append_parts
    (evaluated : RowExpr.eval resumeRow closeRow (.append first second) = some row) :
    ∃ a b, RowExpr.eval resumeRow closeRow first = some a ∧ RowExpr.eval resumeRow closeRow second = some b ∧ row = a ++ b := by
  cases left : RowExpr.eval resumeRow closeRow first <;> cases right : RowExpr.eval resumeRow closeRow second <;>
    simp [RowExpr.eval, left, right, merge] at evaluated
  case some.some a b => exact ⟨a, b, rfl, rfl, evaluated.symm⟩

inductive Schema (operations : Operations) (policy : TicketPolicy) (header : Header)
    (inside : ProtectionContracts.Context) :
    CallableProtection.Environment → UseState → Code → UseState → Contract → RowExpr → Prop where
  | stable (summary : Summarizes operations environment code contract raw) :
      Schema operations policy header inside environment phase code phase contract
        (.through (header.context inside phase) (.literal raw))
  | pair (left : Schema operations policy header inside environment before a middle first leftRow)
      (right : Schema operations policy header inside environment middle b after second rightRow) :
      Schema operations policy header inside environment before (.pair a b) after (.pair first second) (.append leftRow rightRow)
  | app (function : Schema operations policy header inside environment before f middle (.function input output latent) functionRow)
      (argument : Schema operations policy header inside environment middle a after input argumentRow) :
      Schema operations policy header inside environment before (.app f a) after output
        (.append (.append functionRow argumentRow) (.through (header.context inside after) (.literal latent)))
  | bind (initializer : Schema operations policy header inside environment before a middle input initializerRow)
      (body : Schema operations policy header inside (environment.extend parameter input) middle b after output bodyRow) :
      Schema operations policy header inside environment before (.bind parameter a b) after output (.append initializerRow bodyRow)
  | branch (condition : Schema operations policy header inside environment before test middle .scalar conditionRow)
      (yes : Schema operations policy header inside environment middle a after output yesRow)
      (no : Schema operations policy header inside environment middle b after output noRow) :
      Schema operations policy header inside environment before (.branch test a b) after output
        (.append (.append conditionRow yesRow) noRow)
  | perform (known : operations effect operation = some (input, output))
      (operand : Schema operations policy header inside environment before value after input operandRow) :
      Schema operations policy header inside environment before (.perform (Instantiation.freezeEffect effect) operation value) after output
        (.append operandRow (.through (header.context inside after) (.literal [⟨effect, operation, false⟩])))
  | resume (allowed : (policy header.binder).resume = true)
      (operand : Schema operations policy header inside environment before value .available header.input operandRow) :
      Schema operations policy header inside environment before (.resume header.binder value) .consumed header.answer
        (.append operandRow (.through inside .resume))
  | discard (allowed : (policy header.binder).dispose = true) (unprotected : header.held = false) :
      Schema operations policy header inside environment .available (.discard header.binder) .consumed .scalar
        (.through (.barrier true :: inside) .disposal)
  | cleanup (callback : Schema operations policy header inside environment before action middle (.function .scalar .scalar latent) callbackRow)
      (body : Schema operations policy header inside environment middle code after output bodyRow) :
      Schema operations policy header inside environment before (.cleanup action code) after output
        (.append (.append callbackRow bodyRow) (.through (.barrier true :: header.context inside after) (.literal latent)))
  | resource {world : List Nat} {bodyRow : Nat → Footprint}
      (initializer : Schema operations policy header inside environment before initial after .scalar initialRow)
      (body : ∀ identity, identity ∉ world → Summarizes operations environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (outward : ∀ identity, identity ∉ world → outsideCell identity (bodyRow identity) = raw) :
      Schema operations policy header inside environment before (.resource binder initial code) after output
        (.append initialRow (.through (header.context inside after) (.literal raw)))

theorem instantiate
    (schema : Schema operations policy header inside environment before code after contract expression)
    (evaluated : expression.eval resumeRow closeRow = some row) :
    Derives operations policy (header.ticket resumeRow closeRow) inside environment before code after contract row := by
  induction schema generalizing row with
  | stable summary => exact .stable summary evaluated
  | pair left right ihLeft ihRight =>
      obtain ⟨a, b, first, second, rfl⟩ := eval_append_parts evaluated
      exact .pair (ihLeft first) (ihRight second)
  | app function argument ihFunction ihArgument =>
      obtain ⟨both, invocation, pairEval, invoked, rfl⟩ := eval_append_parts evaluated
      obtain ⟨f, a, functionEval, argumentEval, rfl⟩ := eval_append_parts pairEval
      exact .app (ihFunction functionEval) (ihArgument argumentEval) invoked
  | bind initializer body ihInitializer ihBody =>
      obtain ⟨a, b, first, second, rfl⟩ := eval_append_parts evaluated
      exact .bind (ihInitializer first) (ihBody second)
  | branch condition yes no ihCondition ihYes ihNo =>
      obtain ⟨both, b, first, right, rfl⟩ := eval_append_parts evaluated
      obtain ⟨c, a, test, left, rfl⟩ := eval_append_parts first
      exact .branch (ihCondition test) (ihYes left) (ihNo right)
  | perform known operand ih =>
      obtain ⟨a, request, first, exported, rfl⟩ := eval_append_parts evaluated
      exact .perform known (ih first) exported
  | resume allowed operand ih =>
      obtain ⟨a, resumed, first, exported, rfl⟩ := eval_append_parts evaluated
      exact .resume allowed (ih first) exported
  | discard allowed unprotected =>
      cases closeRow with
      | none => simp [RowExpr.eval] at evaluated
      | some closing => exact .discard allowed unprotected evaluated
  | cleanup callback body ihCallback ihBody =>
      obtain ⟨both, invocation, first, exported, rfl⟩ := eval_append_parts evaluated
      obtain ⟨a, b, callbackEval, bodyEval, rfl⟩ := eval_append_parts first
      exact .cleanup (ihCallback callbackEval) (ihBody bodyEval) exported
  | resource initializer body outward ih =>
      obtain ⟨initialRow, row, initialEval, exported, rfl⟩ := eval_append_parts evaluated
      exact .resource (ih initialEval) body outward exported

/-- Continuation use is checked before any row arguments are supplied. Row
    specialization cannot grant additional resume or disposal capabilities. -/
theorem schema_usage
    (schema : Schema operations policy header inside environment before code after contract expression) :
    Uses policy (.ticket header.binder (policy header.binder)) before code after := by
  induction schema with
  | stable summary => exact ClauseProtection.stable_usage summary policy _ _
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument ihFunction ihArgument => exact .app ihFunction ihArgument
  | bind initializer body ihInitializer ihBody => exact .bind ihInitializer ihBody
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known operand ih => exact .perform ih
  | resume allowed operand ih => exact .resume allowed ih
  | discard allowed unprotected => exact .discard allowed
  | cleanup callback body ihCallback ihBody => exact .cleanup ihCallback ihBody
  | resource initializer body outward ih =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource ih ((instantiation_preserves_usage_iff _ _).mp (ClauseProtection.stable_usage (body identity fresh) policy _ _))

theorem schema_phase_monotone
    (schema : Schema operations policy header inside environment before code after contract expression) :
    before = .consumed → after = .consumed := Syntax.use_state_monotone (schema_usage schema)

/-- Coherence rules out interpreting the old total ticket field's empty
    placeholder as an available disposal plan. Actual capture interfaces supply
    this premise automatically. -/
theorem abstract_derivation
    (source : Derives operations policy (header.ticket resumeRow closeRow) inside environment before code after contract row)
    (coherent : closeRow = none → header.held = true) :
    ∃ expression, Schema operations policy header inside environment before code after contract expression ∧
      expression.eval resumeRow closeRow = some row := by
  induction source with
  | stable summary exported => exact ⟨_, .stable summary, exported⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨a, first, firstEval⟩ := ihLeft
      obtain ⟨b, second, secondEval⟩ := ihRight
      exact ⟨_, .pair first second, eval_append firstEval secondEval⟩
  | app function argument exported ihFunction ihArgument =>
      obtain ⟨f, callable, functionEval⟩ := ihFunction
      obtain ⟨a, operand, argumentEval⟩ := ihArgument
      exact ⟨_, .app callable operand, eval_append (eval_append functionEval argumentEval) exported⟩
  | bind initializer body ihInitializer ihBody =>
      obtain ⟨a, first, firstEval⟩ := ihInitializer
      obtain ⟨b, second, secondEval⟩ := ihBody
      exact ⟨_, .bind first second, eval_append firstEval secondEval⟩
  | branch condition yes no ihCondition ihYes ihNo =>
      obtain ⟨c, test, testEval⟩ := ihCondition
      obtain ⟨a, left, leftEval⟩ := ihYes
      obtain ⟨b, right, rightEval⟩ := ihNo
      exact ⟨_, .branch test left right, eval_append (eval_append testEval leftEval) rightEval⟩
  | perform known operand exported ih =>
      obtain ⟨a, value, operandEval⟩ := ih
      exact ⟨_, .perform known value, eval_append operandEval exported⟩
  | resume allowed operand exported ih =>
      obtain ⟨a, value, operandEval⟩ := ih
      exact ⟨_, .resume allowed value, eval_append operandEval exported⟩
  | discard allowed unprotected exported =>
      cases closeRow with
      | none =>
          have held := coherent rfl
          change header.held = false at unprotected
          rw [held] at unprotected
          cases unprotected
      | some closing => exact ⟨_, .discard allowed unprotected, exported⟩
  | cleanup callback body exported ihCallback ihBody =>
      obtain ⟨a, action, callbackEval⟩ := ihCallback
      obtain ⟨b, value, bodyEval⟩ := ihBody
      exact ⟨_, .cleanup action value, eval_append (eval_append callbackEval bodyEval) exported⟩
  | resource initializer body outward exported ih =>
      obtain ⟨expression, initial, initialEval⟩ := ih
      exact ⟨_, .resource initial body outward, eval_append initialEval exported⟩

theorem schema_equivalence (coherent : closeRow = none → header.held = true) :
    Derives operations policy (header.ticket resumeRow closeRow) inside environment before code after contract row ↔
      ∃ expression, Schema operations policy header inside environment before code after contract expression ∧
        expression.eval resumeRow closeRow = some row :=
  ⟨fun source => abstract_derivation source coherent, fun ⟨_, schema, evaluated⟩ => instantiate schema evaluated⟩

def captureHeader (capture : Stack) (binder : Nat) (input answer : Contract) : Header :=
  ⟨binder, input, answer, ProtectionContexts.protectedMode capture.erase⟩

theorem interface_coherent
    (interface : CaptureInterfaces.Interface operations tables capture resumeRow closeRow) :
    closeRow = none → (captureHeader capture binder input answer).held = true := by
  intro unavailable
  subst closeRow
  exact (CaptureInterfaces.closing_unavailable interface).1

theorem abstract_capture_clause
    (interface : CaptureInterfaces.Interface operations tables capture resumeRow closeRow)
    (source : Derives operations policy (CaptureInterfaces.ticketFor capture resumeRow closeRow binder input answer)
      inside environment before code after contract row) :
    ∃ expression, Schema operations policy (captureHeader capture binder input answer) inside environment before code after contract expression ∧
      expression.eval resumeRow closeRow = some row :=
  abstract_derivation source (interface_coherent interface)

structure ClauseSchema where
  dispose : Bool
  ordinary : Option RowExpr
  protectedRow : Option RowExpr
  deriving DecidableEq, Repr

def evalOffer (resumeRow : Footprint) (closeRow : Option Footprint) : Option RowExpr → Option Footprint
  | none => none
  | some expression => expression.eval resumeRow closeRow

def ClauseSchema.specialize (schema : ClauseSchema) (resumeRow : Footprint) (closeRow : Option Footprint) : ClauseContract :=
  ⟨schema.dispose, evalOffer resumeRow closeRow schema.ordinary, evalOffer resumeRow closeRow schema.protectedRow⟩

def specializeTable (schemas : List (Nat × ClauseSchema)) (resumeRow : Footprint) (closeRow : Option Footprint) :
    List (Nat × ClauseContract) := schemas.map fun (operation, schema) => (operation, schema.specialize resumeRow closeRow)

inductive Offer (operations : Operations) (policy : TicketPolicy) (environment : CallableProtection.Environment)
    (parameter binder : Nat) (argument input answer : Contract) (body : Code) (held : Bool) : Option RowExpr → Prop where
  | unavailable : Offer operations policy environment parameter binder argument input answer body held none
  | offered (supported : ProtectionContexts.SupportsMode (policy binder).dispose held)
      (schema : Schema operations policy ⟨binder, input, answer, held⟩ []
        (environment.extend parameter argument) .available body .consumed answer expression) :
      Offer operations policy environment parameter binder argument input answer body held (some expression)

inductive ClausesSchema (operations : Operations) (policy : TicketPolicy) (environment : CallableProtection.Environment)
    (requested : Instance) (answer : Contract) : Clauses → List (Nat × ClauseSchema) → Prop where
  | nil : ClausesSchema operations policy environment requested answer .nil []
  | cons (known : operations requested operation = some (argument, input))
      (ordinary : Offer operations policy environment parameter binder argument input answer body false ordinaryExpression)
      (protectedMode : Offer operations policy environment parameter binder argument input answer body true protectedExpression)
      (rest : ClausesSchema operations policy environment requested answer clauses table) :
      ClausesSchema operations policy environment requested answer (.cons operation parameter binder body clauses)
        ((operation, ⟨(policy binder).dispose, ordinaryExpression, protectedExpression⟩) :: table)

theorem specialize_offer
    (offer : Offer operations policy environment parameter binder argument input answer body held expression) :
    CertifiedClauseRows.Offers operations policy (CaptureInterfaces.localRows resumeRow closeRow) environment operation parameter binder
      argument input answer body held (evalOffer resumeRow closeRow expression) := by
  cases offer with
  | unavailable => exact .unavailable
  | offered supported schema =>
      rename_i expression
      cases evaluated : expression.eval resumeRow closeRow with
      | none => simp only [evalOffer, evaluated]; exact .unavailable
      | some row => simp only [evalOffer, evaluated]; exact .offered supported (instantiate schema evaluated)

/-- One structural clause-list proof specializes to every pair of capture
    rows. Failed row evaluation produces an unavailable offer, not a proof of
    an invalid concrete clause. Clause order is retained by specialization. -/
theorem specialize_clauses
    (schemas : ClausesSchema operations policy environment requested answer clauses table) :
    CaptureInterfaces.ClausesAt operations policy environment requested answer resumeRow closeRow clauses
      (specializeTable table resumeRow closeRow) := by
  induction schemas with
  | nil => exact .nil
  | cons known ordinary protectedMode rest ih =>
      exact .cons known (specialize_offer ordinary) (specialize_offer protectedMode) ih

/-- This supplies the occurrence-specific certificate expected by the capture
    theorem. Agreement with the interpreter table remains an explicit check. -/
theorem specialize_at_interface {handler : HandlerData} {tables : CallableProtectionFrames.Tables}
    (schemas : ClausesSchema operations policy environment requested answer handler.clauses schemaTable)
    (same : tables handler = specializeTable schemaTable resumeRow closeRow) :
    CaptureInterfaces.ClausesAt operations policy environment requested answer resumeRow closeRow handler.clauses (tables handler) := by
  rw [same]
  exact specialize_clauses schemas

namespace Examples
open CallableFrames.Examples (clauseBody clauses handler)
open CallableJoint.CaptureExample (policy)
open PhaseBoundaries.Examples (operations functionContract)
open ContinuationBounds.Examples (family)

def clauseHeader (held : Bool) : Header := ⟨10, .scalar, functionContract, held⟩
def emptyAt (held : Bool) (phase : UseState) : RowExpr := .through ((clauseHeader held).context [] phase) (.literal [])
def clauseExpression (held : Bool) : RowExpr :=
  .append (.append (emptyAt held .available) (.through [] .resume)) (emptyAt held .consumed)

theorem clause_schema (held : Bool) : Schema operations policy (clauseHeader held) [] environment
    .available clauseBody .consumed functionContract (clauseExpression held) :=
  .bind (.resume rfl (.stable .integer)) (.stable (.variable rfl))

theorem clause_expression_eval (held : Bool) (resumeRow : Footprint) (closeRow : Option Footprint) :
    (clauseExpression held).eval resumeRow closeRow = some resumeRow := by
  simp [clauseExpression, emptyAt, RowExpr.eval, Header.context, ClauseProtection.phaseContext,
    Header.ticket, residualize, DisposalProtection.through_barrier, qualify, merge]

def schemaTable : List (Nat × ClauseSchema) :=
  [(0, ⟨false, some (clauseExpression false), some (clauseExpression true)⟩)]

theorem clause_list_schema : ClausesSchema operations policy environment family functionContract clauses schemaTable :=
  .cons rfl (.offered (fun _ => rfl) (clause_schema false)) (.offered (fun _ => rfl) (clause_schema true)) .nil

/-- One schema proof covers both actual row interfaces from the same-clause
    counterexample; each occurrence gets its own evaluated concrete table. -/
theorem both_capture_rows_specialize (choice : Bool) :
    CaptureInterfaces.ClausesAt operations policy CallableProtection.Environment.empty family functionContract
      (CaptureInterfaces.Examples.actualRow choice) (some []) clauses
      (specializeTable schemaTable (CaptureInterfaces.Examples.actualRow choice) (some [])) :=
  specialize_clauses clause_list_schema

theorem specialized_tables_differ :
    specializeTable schemaTable (CaptureInterfaces.Examples.actualRow true) (some []) ≠
      specializeTable schemaTable (CaptureInterfaces.Examples.actualRow false) (some []) := by decide

theorem controls_checked_before_rows :
    Uses policy (.ticket 10 (policy 10)) .available clauseBody .consumed :=
  schema_usage (clause_schema (environment := .empty) true)

theorem duplicate_resume_schema_rejected :
    ¬ Schema operations policy (clauseHeader false) [] environment .available
      (.bind 4 (.resume 10 (.integer 17)) (.resume 10 (.integer 17))) after contract expression := by
  intro schema
  have usage := schema_usage schema
  cases usage with
  | bind first second => cases first with
      | resume allowed operand => cases second with
          | resume allowed operand => cases operand

def branchExpression (held : Bool) : RowExpr :=
  .append (.append (emptyAt held .available) (clauseExpression held)) (clauseExpression held)

theorem branch_schema (held : Bool) : Schema operations policy (clauseHeader held) [] environment .available
    (.branch (.boolean true) clauseBody clauseBody) .consumed functionContract (branchExpression held) :=
  .branch (.stable .boolean) (clause_schema held) (clause_schema held)

/-- Branch footprints combine possible effects. Repeated row parameters in
    that summary do not authorize repeated continuation use on one path. -/
theorem branch_row_union_and_single_use (held : Bool) (resumeRow : Footprint) (closeRow : Option Footprint) :
    (branchExpression held).eval resumeRow closeRow = some (resumeRow ++ resumeRow) ∧
      Uses policy (.ticket 10 (policy 10)) .available (.branch (.boolean true) clauseBody clauseBody) .consumed := by
  refine ⟨?_, schema_usage (branch_schema (environment := .empty) held)⟩
  simp [branchExpression, RowExpr.eval, clauseExpression, emptyAt, Header.context, Header.ticket,
    ClauseProtection.phaseContext, residualize, DisposalProtection.through_barrier, qualify, merge]

def disposalHeader : Header := ⟨0, .scalar, .scalar, false⟩
def disposalExpression : RowExpr := .through [.barrier true] .disposal

theorem disposal_schema : Schema operations (fun _ => ActionRequirements.disposeOnly) disposalHeader [] environment
    .available (.discard 0) .consumed .scalar disposalExpression := .discard rfl rfl

theorem unavailable_disposal_does_not_evaluate (resumeRow : Footprint) : disposalExpression.eval resumeRow none = none := rfl

theorem disposal_rows_are_protected (resumeRow closing : Footprint) :
    disposalExpression.eval resumeRow (some closing) = some (qualify true closing) := by
  simp [disposalExpression, RowExpr.eval, residualize, DisposalProtection.through_barrier]

theorem protected_discard_schema_rejected :
    ¬ Schema operations (fun _ => ActionRequirements.disposeOnly) (clauseHeader true) [] environment .available
      (.discard 10) .consumed .scalar expression := by
  intro schema
  cases schema with
  | discard allowed unprotected => cases unprotected

namespace Joint
open CallableFrames.Examples (captured outside s0 s1)
open CallableJoint.CaptureExample (initial atRequest liveState source_enters_request)
open CallableContracts.Examples (scalar)
open GenerativeFrames.Examples (declarations)

theorem specialized_empty_table : specializeTable schemaTable [] (some []) = PhaseBoundaries.Examples.tables handler := by
  simp only [schemaTable, specializeTable, List.map_cons, List.map_nil, ClauseSchema.specialize,
    evalOffer, clause_expression_eval]
  rfl

theorem admitted_schema_capture : ∃ registry row,
    NamedAccessSteps [] initial (liveState s1) ∧
      CompletionJoint.Valid declarations policy registry [] (liveState s1) .integer [] scalar ∧
      Derives operations policy (CaptureInterfaces.ticketFor captured [] (some []) 10 .scalar functionContract)
        [] CallableProtection.Environment.empty .available clauseBody .consumed functionContract row ∧
      checkFootprint (CallableProtectionFrames.contextOf PhaseBoundaries.Examples.tables outside) row = true := by
  have certified := specialize_at_interface (environment := CallableProtection.Environment.empty)
    clause_list_schema specialized_empty_table.symm
  obtain ⟨parameter, binder, code, port, record, input, row, selected, portKnown, inputKnown,
      extension, step, valid, boundary, source, accepted, interface⟩ :=
    CaptureInterfaces.capture_preserves (CompletionJoint.callable_valid_included source_enters_request.2)
      CaptureInterfaces.Examples.Joint.capture_interface certified CallableFrames.Examples.selected_cut
      (PhaseBoundaries.Examples.request_checked (environment := .empty)) trivial (owner := 5) (by decide)
  cases selected with
  | hit =>
      obtain ⟨argumentPort, portKnown⟩ := portKnown
      change some (ScopedPorts.Port.unit, ScopedPorts.Port.integer) = some (argumentPort, port) at portKnown
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj portKnown)
      obtain ⟨argument, inputKnown⟩ := inputKnown
      change some (Contract.scalar, Contract.scalar) = some (argument, input) at inputKnown
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj inputKnown)
      have captureStep : NamedAccessStep [] atRequest (liveState s1) := by
        simpa [atRequest, liveState, s0, s1, handler, clauses, clauseBody, Code.subst,
          ScopedPortJoint.advanceState, enteredActivations, ScopedPorts.embedPort] using step
      refine ⟨CallableJoint.Registry.insert (fun _ => none) 5 record, row,
        CallableJoint.execution_append source_enters_request.1 (.next captureStep (.refl _)), ?_, source, accepted⟩
      simpa [atRequest, liveState, s0, s1, handler, clauses, clauseBody, Code.subst,
        ScopedPortJoint.advanceState, enteredActivations, ScopedPorts.embedPort] using valid
  | pass different => exact False.elim (different rfl)

end Joint
end Examples

end Ash.OneShot.ParametricClauseRows

#print axioms Ash.OneShot.ParametricClauseRows.eval_append
#print axioms Ash.OneShot.ParametricClauseRows.eval_append_parts
#print axioms Ash.OneShot.ParametricClauseRows.instantiate
#print axioms Ash.OneShot.ParametricClauseRows.abstract_derivation
#print axioms Ash.OneShot.ParametricClauseRows.schema_equivalence
#print axioms Ash.OneShot.ParametricClauseRows.interface_coherent
#print axioms Ash.OneShot.ParametricClauseRows.abstract_capture_clause
#print axioms Ash.OneShot.ParametricClauseRows.specialize_offer
#print axioms Ash.OneShot.ParametricClauseRows.specialize_clauses
#print axioms Ash.OneShot.ParametricClauseRows.specialize_at_interface
#print axioms Ash.OneShot.ParametricClauseRows.schema_usage
#print axioms Ash.OneShot.ParametricClauseRows.schema_phase_monotone
#print axioms Ash.OneShot.ParametricClauseRows.Examples.clause_schema
#print axioms Ash.OneShot.ParametricClauseRows.Examples.clause_expression_eval
#print axioms Ash.OneShot.ParametricClauseRows.Examples.clause_list_schema
#print axioms Ash.OneShot.ParametricClauseRows.Examples.both_capture_rows_specialize
#print axioms Ash.OneShot.ParametricClauseRows.Examples.specialized_tables_differ
#print axioms Ash.OneShot.ParametricClauseRows.Examples.controls_checked_before_rows
#print axioms Ash.OneShot.ParametricClauseRows.Examples.duplicate_resume_schema_rejected
#print axioms Ash.OneShot.ParametricClauseRows.Examples.disposal_schema
#print axioms Ash.OneShot.ParametricClauseRows.Examples.unavailable_disposal_does_not_evaluate
#print axioms Ash.OneShot.ParametricClauseRows.Examples.disposal_rows_are_protected
#print axioms Ash.OneShot.ParametricClauseRows.Examples.protected_discard_schema_rejected
#print axioms Ash.OneShot.ParametricClauseRows.Examples.Joint.specialized_empty_table
#print axioms Ash.OneShot.ParametricClauseRows.Examples.Joint.admitted_schema_capture
#print axioms Ash.OneShot.ParametricClauseRows.Examples.branch_schema
#print axioms Ash.OneShot.ParametricClauseRows.Examples.branch_row_union_and_single_use
