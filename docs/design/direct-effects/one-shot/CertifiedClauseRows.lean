import ClauseProtection

/-!
Offered handler rows justified by their actual source clause bodies. Captured
execution and closing residuals remain explicit inputs; this does not establish
whole capture preservation or initial-program admission.
-/

namespace Ash.OneShot.CertifiedClauseRows
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts CallableProtectionFrames
open ClauseProtection (Ticket Derives)
open Syntax (TicketPolicy)
open Instantiation (freezeEffect)

abbrev CaptureRows := Nat → Nat → Nat → Code → Bool → Footprint × Footprint

def clauseTicket (captures : CaptureRows) (operation parameter binder : Nat) (body : Code)
    (input answer : Contract) (held : Bool) : Ticket :=
  ⟨binder, input, answer, held, (captures operation parameter binder body held).1,
    (captures operation parameter binder body held).2⟩

inductive Offers (operations : Operations) (policy : TicketPolicy) (captures : CaptureRows)
    (environment : CallableProtection.Environment) (operation parameter binder : Nat)
    (argument input answer : Contract) (body : Code) : Bool → Option Footprint → Prop where
  | unavailable : Offers operations policy captures environment operation parameter binder argument input answer body held none
  | offered (supported : ProtectionContexts.SupportsMode (policy binder).dispose held)
      (checked : Derives operations policy (clauseTicket captures operation parameter binder body input answer held) []
        (environment.extend parameter argument) .available body .consumed answer row) :
      Offers operations policy captures environment operation parameter binder argument input answer body held (some row)

inductive Certified (operations : Operations) (policy : TicketPolicy) (captures : CaptureRows)
    (environment : CallableProtection.Environment) (requested : Instance) (answer : Contract) :
    Clauses → List (Nat × ClauseContract) → Prop where
  | nil : Certified operations policy captures environment requested answer .nil []
  | cons (known : operations requested operation = some (argument, input))
      (ordinary : Offers operations policy captures environment operation parameter binder argument input answer body false ordinaryRow)
      (protectedMode : Offers operations policy captures environment operation parameter binder argument input answer body true protectedRow)
      (rest : Certified operations policy captures environment requested answer clauses table) :
      Certified operations policy captures environment requested answer (.cons operation parameter binder body clauses)
        ((operation, ⟨(policy binder).dispose, ordinaryRow, protectedRow⟩) :: table)

theorem offered_body
    (offered : Offers operations policy captures environment operation parameter binder argument input answer body held (some row)) :
    ProtectionContexts.SupportsMode (policy binder).dispose held ∧
      Derives operations policy (clauseTicket captures operation parameter binder body input answer held) []
        (environment.extend parameter argument) .available body .consumed answer row := by
  cases offered with
  | offered supported checked => exact ⟨supported, checked⟩

theorem selected_contract (certified : Certified operations policy captures environment requested answer clauses table)
    (selected : ClauseAt operation clauses parameter binder body) :
    ∃ argument input ordinaryRow protectedRow,
      operations requested operation = some (argument, input) ∧
      lookup operation table = some ⟨(policy binder).dispose, ordinaryRow, protectedRow⟩ ∧
      Offers operations policy captures environment operation parameter binder argument input answer body false ordinaryRow ∧
      Offers operations policy captures environment operation parameter binder argument input answer body true protectedRow := by
  induction selected generalizing table with
  | hit => cases certified with
      | cons known ordinary protectedMode rest => exact ⟨_, _, _, _, known, by simp [lookup], ordinary, protectedMode⟩
  | pass different next ih => cases certified with
      | cons known ordinary protectedMode rest =>
          obtain ⟨argument, input, ordinaryRow, protectedRow, signature, found, first, second⟩ := ih rest
          exact ⟨argument, input, ordinaryRow, protectedRow, signature,
            by simpa [lookup, different] using found, first, second⟩

theorem selected_body (certified : Certified operations policy captures environment requested answer clauses table)
    (selected : ClauseAt operation clauses parameter binder body)
    (found : lookup operation table = some contract) (row : contract.row held = some outside) :
    ∃ argument input, operations requested operation = some (argument, input) ∧
      ProtectionContexts.SupportsMode (policy binder).dispose held ∧
      Derives operations policy (clauseTicket captures operation parameter binder body input answer held) []
        (environment.extend parameter argument) .available body .consumed answer outside := by
  obtain ⟨argument, input, ordinaryRow, protectedRow, known, actual, ordinary, protectedMode⟩ := selected_contract certified selected
  cases Option.some.inj (actual.symm.trans found)
  refine ⟨argument, input, known, ?_⟩
  cases held with
  | false =>
      have same : ordinaryRow = some outside := by simpa [ClauseContract.row] using row
      exact offered_body (same ▸ ordinary)
  | true =>
      have same : protectedRow = some outside := by simpa [ClauseContract.row] using row
      exact offered_body (same ▸ protectedMode)

/-- Follow the actual cut, obtaining the selected row and its check at the
    actual surviving tail. Equal activation labels cannot redirect this proof. -/
theorem cut_offered (cut : HandlerCut requested whole capture tail handler)
    (checked : checkRequest (contextOf tables whole) ⟨requested, operation, incoming⟩ = true) :
    ∃ contract outside, lookup operation (tables handler) = some contract ∧
      modeCheck contract.dispose (incoming || ProtectionContexts.protectedMode capture.erase) = true ∧
      contract.row (incoming || ProtectionContexts.protectedMode capture.erase) = some outside ∧
      checkFootprint (contextOf tables tail) outside = true := by
  induction cut generalizing incoming with
  | hit handler tail same =>
      simp only [contextOf, pushContext, checkRequest, same, ↓reduceIte] at checked
      cases known : lookup operation (tables handler) with
      | none => simp [known] at checked
      | some contract =>
          cases permitted : modeCheck contract.dispose incoming with
          | false => simp [known, permitted] at checked
          | true =>
              cases row : contract.row incoming with
              | none => simp [known, permitted, row] at checked
              | some outside =>
                  refine ⟨contract, outside, rfl, ?_, ?_, ?_⟩
                  · simpa [Stack.erase, ExecFrame.erase, HandlerData.erase, ProtectionContexts.protectedMode,
                      ProtectionContexts.frameProtected] using permitted
                  · simpa [Stack.erase, ExecFrame.erase, HandlerData.erase, ProtectionContexts.protectedMode,
                      ProtectionContexts.frameProtected] using row
                  · simpa [known, permitted, row, checkFootprint] using checked
  | push frame rest capture tail handler miss next ih =>
      rw [contextOf, check_push_miss tables frame _ miss] at checked
      obtain ⟨contract, outside, known, permitted, row, accepted⟩ := ih checked
      exact ⟨contract, outside, known,
        by simpa [Stack.erase, ProtectionContexts.protectedMode, Bool.or_assoc] using permitted,
        by simpa [Stack.erase, ProtectionContexts.protectedMode, Bool.or_assoc] using row, accepted⟩
  | live owner input answer saved scope rest capture tail handler next ih =>
      change checkRequest (contextOf tables rest)
        ⟨requested, operation, incoming || ProtectionContexts.protectedMode saved.erase⟩ = true at checked
      obtain ⟨contract, outside, known, permitted, row, accepted⟩ := ih checked
      exact ⟨contract, outside, known,
        by simpa [Stack.erase, ProtectionContexts.protectedMode, Bool.or_assoc] using permitted,
        by simpa [Stack.erase, ProtectionContexts.protectedMode, Bool.or_assoc] using row, accepted⟩
  | spent owner answer scope rest capture tail handler next ih => exact ih checked

/-- The source request's own operation contract supplies its closed payload
    contract, independently of the clause's analysis environment. -/
theorem request_operand (summary : Summarizes operations environment
    (.perform (freezeEffect requested) operation operand) result row)
    (known : operations requested operation = some (argument, input)) (closed : ClosedValue operand) :
    Summarizes operations environment operand argument [] := by
  generalize shape : Code.perform (freezeEffect requested) operation operand = code at summary
  cases summary <;> try cases shape
  case perform payload actual =>
    obtain ⟨effectEq, operationEq, operandEq⟩ := Code.perform.inj shape
    cases freeze_effect_injective effectEq
    cases operationEq
    cases operandEq
    cases Option.some.inj (actual.symm.trans known)
    have empty := value_has_no_immediate_demands payload closed.1
    exact empty ▸ payload

/-- Selection plus a checked request derives the actual clause body's exported
    requirements after closed payload binding. Capture-row provenance remains
    an input of the source table certificate. -/
theorem capture_clause_certificate
    (certified : Certified operations policy captures clauseEnvironment requested answer handler.clauses (tables handler))
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (checked : Checked operations tables operandEnvironment whole (.perform (freezeEffect requested) operation operand) result)
    (closed : ClosedValue operand) :
    ∃ argument input outside, operations requested operation = some (argument, input) ∧
      ProtectionContexts.SupportsMode (policy binder).dispose (ProtectionContexts.protectedMode capture.erase) ∧
      Derives operations policy
        (clauseTicket captures operation parameter binder body input answer (ProtectionContexts.protectedMode capture.erase)) []
        clauseEnvironment .available (body.subst parameter operand) .consumed answer outside ∧
      checkFootprint (contextOf tables tail) outside = true := by
  obtain ⟨contract, outside, found, permitted, offered, accepted⟩ := cut_offered cut (actual_request_admitted checked)
  simp only [Bool.false_or] at offered
  obtain ⟨argument, input, known, supported, bodyChecked⟩ := selected_body certified selected found offered
  obtain ⟨requestRow, summary, _⟩ := checked
  have payload := request_operand summary known closed
  have moved := closed_value_environment payload closed clauseEnvironment
  exact ⟨argument, input, outside, known, supported, ClauseProtection.substitution bodyChecked moved closed, accepted⟩

theorem capture_step
    (certified : Certified operations policy captures clauseEnvironment requested answer handler.clauses (tables handler))
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (checked : Checked operations tables operandEnvironment whole (.perform (freezeEffect requested) operation operand) result)
    (closed : ClosedValue operand) (ready : ClosedExcept parameter body) :
    ∃ input outside,
      RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner operationResult handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
      Derives operations policy
        (clauseTicket captures operation parameter binder body input answer (ProtectionContexts.protectedMode capture.erase)) []
        clauseEnvironment .available (body.subst parameter operand) .consumed answer outside ∧
      ScopedExpressions.Uses policy (.ticket binder (policy binder)) .available (body.subst parameter operand) .consumed ∧
      checkFootprint (contextOf tables tail) outside = true := by
  obtain ⟨argument, input, outside, known, supported, bodyChecked, accepted⟩ :=
    capture_clause_certificate certified cut selected checked closed
  exact ⟨input, outside, .capture requested operation parameter binder owner operand body scope whole capture tail handler
    operationResult cut selected closed ready, bodyChecked, ClauseProtection.derives_usage bodyChecked, accepted⟩

namespace Examples
open ClauseProtection.Examples (operations policy effectF effectG surrounding)

def effectE : Instance := .user 0 []
def captures : CaptureRows := fun _ _ _ _ held => ([⟨effectG, 0, held⟩], [])
def outside : Footprint := [⟨effectF, 0, true⟩, ⟨effectG, 0, true⟩, ⟨effectF, 0, false⟩]
def clauses : Clauses := .cons 0 9 0 surrounding .nil
def table : List (Nat × ClauseContract) := [(0, ⟨false, none, some outside⟩)]

theorem protected_body : Offers operations policy captures environment 0 9 0 .scalar .scalar .scalar surrounding true (some outside) :=
  .offered (fun _ => rfl) ClauseProtection.Examples.before_during_after

theorem table_certified : Certified operations policy captures environment effectE .scalar clauses table :=
  .cons rfl .unavailable protected_body .nil

theorem mode_is_explicit : lookup 0 table = some ⟨false, none, some outside⟩ := rfl

def resumeBody : Code := .resume 0 .unit

theorem fabricated_resume_row_rejected :
    ¬ Offers operations policy captures environment 0 9 0 .scalar .scalar .scalar resumeBody true (some []) := by
  intro offered
  have checked := (offered_body offered).2
  generalize empty : ([] : Footprint) = row at checked
  cases checked with
  | resume allowed operand exported =>
      have same : ([⟨effectG, 0, true⟩] : Footprint) = _ := Option.some.inj exported
      simp_all

def disposalPolicy : TicketPolicy := fun _ => ActionRequirements.disposeOnly

theorem protected_policy_rejected :
    ¬ Offers operations disposalPolicy captures environment 0 9 0 .scalar .scalar .scalar body true (some row) := by
  intro offered
  have denied := (offered_body offered).1 rfl
  cases denied

def handler : HandlerData := ⟨11, effectE, clauses, .none, .unit, rfl⟩
def outerF : HandlerData := ⟨22, effectF, .cons 0 0 2 (.resume 2 .unit) .nil, .none, .unit, rfl⟩
def outerG : HandlerData := ⟨33, effectG, .cons 0 0 3 (.resume 3 .unit) .nil, .none, .unit, rfl⟩
def tables : Tables := fun data => if data.activation = 11 then table else [(0, ⟨false, some [], some []⟩)]
def tail : Stack := .push (.handler outerF) (.push (.handler outerG) .nil)
def capture : Stack := .push
  (.running CallableProtectionFrames.Examples.action .unit CallableProtection.Examples.unit_closed)
  (.push (.handler handler) .nil)
def whole : Stack := capture.append tail

theorem actual_cut : HandlerCut effectE whole capture tail handler :=
  .push _ _ _ _ _ (by decide) (.hit handler tail rfl)

theorem request_checked : Checked operations tables environment whole
    (.perform (freezeEffect effectE) 0 .unit) .scalar :=
  ⟨_, .perform rfl .unit, by decide⟩

theorem selected_source_body :
    ∃ argument input row, operations effectE 0 = some (argument, input) ∧
      ProtectionContexts.SupportsMode (policy 0).dispose (ProtectionContexts.protectedMode capture.erase) ∧
      Derives operations policy (clauseTicket captures 0 9 0 surrounding input .scalar (ProtectionContexts.protectedMode capture.erase)) []
        environment .available (surrounding.subst 9 .unit) .consumed .scalar row ∧
      checkFootprint (contextOf tables tail) row = true :=
  capture_clause_certificate table_certified actual_cut ClauseAt.hit (request_checked (environment := environment)) CallableProtection.Examples.unit_closed

theorem clause_closed_except_parameter : ClosedExcept 9 surrounding := by
  intro name member
  simp [ClauseProtection.Examples.surrounding, ClauseProtection.Examples.requestF, Code.dependencies,
    effectAtoms, Instantiation.freezeEffect, ClauseProtection.Examples.effectF, Syntax.without] at member

theorem actual_capture_step :
    RawStep ⟨.perform (freezeEffect effectE) 0 .unit, .none, whole⟩
      ⟨surrounding.subst 9 .unit, .ticket 0 8, .live 8 .unit handler.answer capture handler.scope tail⟩ [.ticket 8] [] :=
  .capture effectE 0 9 0 8 .unit surrounding .none whole capture tail handler .unit actual_cut ClauseAt.hit
    CallableProtection.Examples.unit_closed clause_closed_except_parameter

theorem used_parameter_offer :
    Offers operations policy captures environment 0 9 0 .scalar .scalar .scalar
      (.resume 0 (.variable 9)) true (some [⟨effectG, 0, true⟩]) := by
  apply Offers.offered (fun _ => rfl)
  apply Derives.resume (operandRow := []) (resumedRow := [⟨effectG, 0, true⟩])
  · rfl
  · exact .stable (.variable rfl) rfl
  · rfl

theorem used_parameter_binding :
    Derives operations policy (clauseTicket captures 0 9 0 (.resume 0 (.variable 9)) .scalar .scalar true) []
      environment .available (.resume 0 .unit) .consumed .scalar [⟨effectG, 0, true⟩] :=
  ClauseProtection.substitution (offered_body used_parameter_offer).2 Summarizes.unit CallableProtection.Examples.unit_closed

end Examples

end Ash.OneShot.CertifiedClauseRows

#print axioms Ash.OneShot.CertifiedClauseRows.offered_body
#print axioms Ash.OneShot.CertifiedClauseRows.selected_contract
#print axioms Ash.OneShot.CertifiedClauseRows.selected_body
#print axioms Ash.OneShot.CertifiedClauseRows.cut_offered
#print axioms Ash.OneShot.CertifiedClauseRows.request_operand
#print axioms Ash.OneShot.CertifiedClauseRows.capture_clause_certificate
#print axioms Ash.OneShot.CertifiedClauseRows.capture_step
#print axioms Ash.OneShot.CertifiedClauseRows.Examples.protected_body
#print axioms Ash.OneShot.CertifiedClauseRows.Examples.table_certified
#print axioms Ash.OneShot.CertifiedClauseRows.Examples.mode_is_explicit
#print axioms Ash.OneShot.CertifiedClauseRows.Examples.fabricated_resume_row_rejected
#print axioms Ash.OneShot.CertifiedClauseRows.Examples.protected_policy_rejected
#print axioms Ash.OneShot.CertifiedClauseRows.Examples.actual_cut
#print axioms Ash.OneShot.CertifiedClauseRows.Examples.request_checked
#print axioms Ash.OneShot.CertifiedClauseRows.Examples.selected_source_body

#print axioms Ash.OneShot.CertifiedClauseRows.Examples.clause_closed_except_parameter
#print axioms Ash.OneShot.CertifiedClauseRows.Examples.actual_capture_step

#print axioms Ash.OneShot.CertifiedClauseRows.Examples.used_parameter_offer
#print axioms Ash.OneShot.CertifiedClauseRows.Examples.used_parameter_binding
