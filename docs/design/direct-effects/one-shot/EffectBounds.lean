import ParametricClauseRows

/-!
Effect upper bounds preserve complete demand identities, including protection,
while allowing repeated requirements to share a bound. Continuation ownership
and usage remain separate judgments. This repairs a local exact-row obstruction;
complete bounded source preservation and inference still require integration.
-/

namespace Ash.OneShot.EffectBounds
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open CallableProtectionFrames (Tables contextOf)
open ClauseProtection (Ticket Derives)

/-- Coverage keeps the effect instance, operation and protection bit intact.
    It does not equate different interpreter positions or continuation uses. -/
abbrev Covers (bound actual : Footprint) : Prop := actual ⊆ bound

theorem covers_refl (row : Footprint) : Covers row row := fun _ present => present

theorem covers_trans (first : Covers bound middle) (second : Covers middle actual) : Covers bound actual :=
  fun _ present => first (second present)

theorem covers_append (first : Covers bound a) (second : Covers bound b) : Covers bound (a ++ b) := by
  intro request present
  exact (List.mem_append.mp present).elim (fun member => first member) (fun member => second member)

theorem covers_append_bounds (first : Covers a actualA) (second : Covers b actualB) : Covers (a ++ b) (actualA ++ actualB) := by
  intro request present
  rcases List.mem_append.mp present with left | right
  · exact List.mem_append_left _ (first left)
  · exact List.mem_append_right _ (second right)

theorem check_covered (accepted : checkFootprint outside bound = true) (covered : Covers bound actual) :
    checkFootprint outside actual = true := checked_footprint_subset accepted covered

theorem qualifies_coverage (covered : Covers bound actual) : Covers (qualify held bound) (qualify held actual) := by
  intro request present
  obtain ⟨original, member, same⟩ := List.mem_map.mp present
  exact List.mem_map.mpr ⟨original, covered member, same⟩

/-- Exact saved-frame derivations remain witnesses; their effects may be
    admitted by a common upper bound rather than an equal ordered list. -/
def Saved (operations : Operations) (tables : Tables) (capture : Stack) (bound : Footprint) : Prop :=
  ∃ actual, SavedFrameRequirements.Rows operations tables capture actual ∧ Covers bound actual

theorem saved_exact (rows : SavedFrameRequirements.Rows operations tables capture row) : Saved operations tables capture row :=
  ⟨row, rows, covers_refl row⟩

theorem saved_checked (saved : Saved operations tables capture bound) (accepted : checkFootprint outside bound = true) :
    SavedFrameRequirements.Checked operations tables outside capture := by
  obtain ⟨actual, rows, covered⟩ := saved
  exact SavedFrameRequirements.rows_checked rows (check_covered accepted covered)

theorem resume_recomposition {front tail : Stack}
    (saved : Saved operations tables capture bound)
    (accepted : checkFootprint (contextOf tables (front.append tail) ++ outside) bound = true)
    (caller : SavedFrameRequirements.Checked operations tables outside (front.append tail)) :
    SavedFrameRequirements.Checked operations tables outside (capture.append (front.append (.spent owner answer scope tail))) := by
  obtain ⟨actual, rows, covered⟩ := saved
  exact SavedFrameRequirements.resume_recomposition rows (check_covered accepted covered) caller

/-- A body has its existing exact source derivation. Coverage connects that
    derivation to the handler's advertised upper bound. -/
inductive Offer (operations : Operations) (policy : Syntax.TicketPolicy) (captures : CertifiedClauseRows.CaptureRows)
    (environment : CallableProtection.Environment) (operation parameter binder : Nat)
    (argument input answer : Contract) (body : Code) : Bool → Option Footprint → Prop where
  | unavailable : Offer operations policy captures environment operation parameter binder argument input answer body held none
  | offered (supported : ProtectionContexts.SupportsMode (policy binder).dispose held)
      (source : Derives operations policy (CertifiedClauseRows.clauseTicket captures operation parameter binder body input answer held) []
        (environment.extend parameter argument) .available body .consumed answer actual)
      (covered : Covers bound actual) :
      Offer operations policy captures environment operation parameter binder argument input answer body held (some bound)

inductive Certified (operations : Operations) (policy : Syntax.TicketPolicy) (captures : CertifiedClauseRows.CaptureRows)
    (environment : CallableProtection.Environment) (requested : Instance) (answer : Contract) :
    Clauses → List (Nat × ClauseContract) → Prop where
  | nil : Certified operations policy captures environment requested answer .nil []
  | cons (known : operations requested operation = some (argument, input))
      (ordinary : Offer operations policy captures environment operation parameter binder argument input answer body false ordinaryRow)
      (protectedMode : Offer operations policy captures environment operation parameter binder argument input answer body true protectedRow)
      (rest : Certified operations policy captures environment requested answer clauses table) :
      Certified operations policy captures environment requested answer (.cons operation parameter binder body clauses)
        ((operation, ⟨(policy binder).dispose, ordinaryRow, protectedRow⟩) :: table)

theorem offered_body
    (offer : Offer operations policy captures environment operation parameter binder argument input answer body held (some bound)) :
    ∃ actual, ProtectionContexts.SupportsMode (policy binder).dispose held ∧
      Derives operations policy (CertifiedClauseRows.clauseTicket captures operation parameter binder body input answer held) []
        (environment.extend parameter argument) .available body .consumed answer actual ∧ Covers bound actual := by
  cases offer with
  | offered supported source covered => exact ⟨_, supported, source, covered⟩

theorem exact_offer (offer : CertifiedClauseRows.Offers operations policy captures environment operation parameter binder argument input answer body held bound) :
    Offer operations policy captures environment operation parameter binder argument input answer body held bound := by
  cases offer with
  | unavailable => exact .unavailable
  | offered supported source => exact .offered supported source (covers_refl _)

theorem exact_certified (certified : CertifiedClauseRows.Certified operations policy captures environment requested answer clauses table) :
    Certified operations policy captures environment requested answer clauses table := by
  induction certified with
  | nil => exact .nil
  | cons known ordinary protectedMode rest ih => exact .cons known (exact_offer ordinary) (exact_offer protectedMode) ih

theorem selected_contract (certified : Certified operations policy captures environment requested answer clauses table)
    (selected : ClauseAt operation clauses parameter binder body) :
    ∃ argument input ordinaryRow protectedRow,
      operations requested operation = some (argument, input) ∧
      lookup operation table = some ⟨(policy binder).dispose, ordinaryRow, protectedRow⟩ ∧
      Offer operations policy captures environment operation parameter binder argument input answer body false ordinaryRow ∧
      Offer operations policy captures environment operation parameter binder argument input answer body true protectedRow := by
  induction selected generalizing table with
  | hit => cases certified with
      | cons known ordinary protectedMode rest => exact ⟨_, _, _, _, known, by simp [lookup], ordinary, protectedMode⟩
  | pass different next ih => cases certified with
      | cons known ordinary protectedMode rest =>
          obtain ⟨argument, input, ordinaryRow, protectedRow, known, found, first, second⟩ := ih rest
          exact ⟨argument, input, ordinaryRow, protectedRow, known, by simpa [lookup, different] using found, first, second⟩

theorem selected_body (certified : Certified operations policy captures environment requested answer clauses table)
    (selected : ClauseAt operation clauses parameter binder body)
    (found : lookup operation table = some contract) (row : contract.row held = some bound) :
    ∃ argument input actual, operations requested operation = some (argument, input) ∧
      ProtectionContexts.SupportsMode (policy binder).dispose held ∧
      Derives operations policy (CertifiedClauseRows.clauseTicket captures operation parameter binder body input answer held) []
        (environment.extend parameter argument) .available body .consumed answer actual ∧ Covers bound actual := by
  obtain ⟨argument, input, ordinaryRow, protectedRow, known, actual, ordinary, protectedMode⟩ := selected_contract certified selected
  cases Option.some.inj (actual.symm.trans found)
  have bodyChecked : ∃ actual, ProtectionContexts.SupportsMode (policy binder).dispose held ∧
      Derives operations policy (CertifiedClauseRows.clauseTicket captures operation parameter binder body input answer held) []
        (environment.extend parameter argument) .available body .consumed answer actual ∧ Covers bound actual := by
    cases held with
    | false => exact offered_body ((show ordinaryRow = some bound from row) ▸ ordinary)
    | true => exact offered_body ((show protectedRow = some bound from row) ▸ protectedMode)
  obtain ⟨actual, supported, source, covered⟩ := bodyChecked
  exact ⟨argument, input, actual, known, supported, source, covered⟩

/-- Exact selection and payload substitution are unchanged. The advertised
    bound's outside check entails the actual clause row's check. -/
theorem capture_clause_certificate
    (certified : Certified operations policy captures clauseEnvironment requested answer handler.clauses (tables handler))
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (checked : CallableProtectionFrames.Checked operations tables operandEnvironment whole
      (.perform (Instantiation.freezeEffect requested) operation operand) result)
    (closed : ClosedValue operand) :
    ∃ argument input actual, operations requested operation = some (argument, input) ∧
      Derives operations policy
        (CertifiedClauseRows.clauseTicket captures operation parameter binder body input answer (ProtectionContexts.protectedMode capture.erase)) []
        clauseEnvironment .available (body.subst parameter operand) .consumed answer actual ∧
      checkFootprint (contextOf tables tail) actual = true := by
  obtain ⟨contract, bound, found, permitted, offered, accepted⟩ :=
    CertifiedClauseRows.cut_offered cut (CallableProtection.actual_request_admitted checked)
  simp only [Bool.false_or] at offered
  obtain ⟨argument, input, actual, known, supported, source, covered⟩ := selected_body certified selected found offered
  obtain ⟨requestRow, summary, _⟩ := checked
  have payload := CertifiedClauseRows.request_operand summary known closed
  have moved := closed_value_environment payload closed clauseEnvironment
  exact ⟨argument, input, actual, known, ClauseProtection.substitution source moved closed, check_covered accepted covered⟩

/-- Disposal retains its existing exact plan certificate. Only the advertised
    resumption row is widened, with the actual row retained as a witness. -/
def Interface (operations : Operations) (tables : Tables) (capture : Stack) (resumeBound : Footprint)
    (closeRow : Option Footprint) : Prop :=
  ∃ actual, CaptureInterfaces.Interface operations tables capture actual closeRow ∧ Covers resumeBound actual

theorem interface_saved (interface : Interface operations tables capture resumeBound closeRow) :
    Saved operations tables capture resumeBound := by
  obtain ⟨actual, source, covered⟩ := interface
  exact ⟨actual, CaptureInterfaces.resume_rows source, covered⟩

theorem interface_exact (interface : CaptureInterfaces.Interface operations tables capture row closeRow) :
    Interface operations tables capture row closeRow := ⟨row, interface, covers_refl row⟩

theorem capture_preserves
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (interface : Interface operations tables capture resumeBound closeRow)
    (certified : Certified operations policy (CaptureInterfaces.localRows resumeBound closeRow) clauseEnvironment requested answer
      handler.clauses (tables handler))
    (cut : HandlerCut requested whole capture tail handler)
    (checked : CallableProtectionFrames.Checked operations tables operandEnvironment whole
      (.perform (Instantiation.freezeEffect requested) operation operand) output)
    (isValue : operand.IsValue) (fresh : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (parameter binder : Nat) (body : Code) (port : ScopedPorts.Port) (record : CallableJoint.TicketRecord)
      (input : Contract) (row : Footprint),
      ClauseAt operation handler.clauses parameter binder body ∧
      (∃ argument, DeclarationResults.signature declarations requested operation = some (argument, port)) ∧
      (∃ argument, operations requested operation = some (argument, input)) ∧
      CallableJoint.RegistryExtends registry (registry.insert owner record) ∧
      let newTicket := CaptureInterfaces.ticketFor capture resumeBound closeRow binder input answer
      let before : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let base := Stack.live owner (ScopedPorts.embedPort port) handler.answer capture handler.scope tail
      let next := ScopedPortJoint.advanceState before ⟨body.subst parameter operand, .ticket binder owner, base⟩
        [.ticket owner] []
      NamedAccessStep ambient before next ∧
      CompletionJoint.Valid declarations policy (registry.insert owner record) ambient next result outgoing bound ∧
      PhaseBoundaries.Boundary newTicket owner .available base tail handler.answer ∧
      Derives operations policy newTicket [] clauseEnvironment .available (body.subst parameter operand) .consumed answer row ∧
      checkFootprint (contextOf tables tail) row = true ∧ Interface operations tables capture resumeBound closeRow := by
  obtain ⟨parameter, binder, body, port, residual, record, _, selected, portKnown, extension, step, nextValid⟩ :=
    CompletionJoint.capture_without_payload_premise cut valid isValue fresh
  obtain ⟨argument, input, row, known, source, accepted⟩ := capture_clause_certificate certified cut selected checked
    (PhaseBoundaries.request_operand_closed valid isValue)
  exact ⟨parameter, binder, body, port, record, input, row, selected, portKnown, ⟨argument, known⟩, extension,
    step, nextValid, PhaseBoundaries.Boundary.live rfl, source, accepted, interface⟩

theorem resume_joint {ticket : Ticket}
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume ticket.binder value, scope,
        PhaseContextChains.stackOf frames (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (source : PhaseContextChains.Source operations policy ticket [] (contextOf tables tail) environment
      (.resume ticket.binder value) frames .available after output row)
    (saved : Saved operations tables capture ticket.resumeRow)
    (outside : SavedFrameRequirements.Checked operations tables [] tail)
    (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨.resume ticket.binder value, scope,
      PhaseContextChains.stackOf frames (.live owner input answer capture caller tail)⟩, issued, completed⟩, activations⟩
    let next : Configuration := ⟨value, scope, capture.append (PhaseContextChains.stackOf frames (.spent owner answer caller tail))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before next [] [.ticket owner]) ∧
      CompletionJoint.Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before next [] [.ticket owner]) result outgoing bound ∧
      SavedFrameRequirements.Checked operations tables [] next.stack := by
  obtain ⟨step, nextValid, pending⟩ := ChainOwnerAgreement.resume_joint valid source isValue
  have waiting := NeutralFrameRows.resume_waiting_checked source outside
  have accepted := NeutralFrameRows.resume_row_accepted source isValue
  have callerChecked : SavedFrameRequirements.Checked operations tables []
      ((PhaseContextChains.stackOf frames .nil).append tail) := by
    simpa only [PhaseContextChains.stack_tail_append, Stack.append] using waiting
  have captureAccepted : checkFootprint (contextOf tables ((PhaseContextChains.stackOf frames .nil).append tail) ++ [])
      ticket.resumeRow = true := by
    simpa only [PhaseContextChains.stack_tail_append, Stack.append, List.append_nil] using accepted
  have restored := resume_recomposition (owner := owner) (answer := answer) (scope := caller) saved captureAccepted callerChecked
  exact ⟨step, nextValid, by simpa only [PhaseContextChains.stack_tail_append, Stack.append] using restored⟩

namespace RepeatedHandler
open ParametricClauseRows (Header Schema RowExpr)

def pulse : Instance := .user 90 []
def audit : Instance := .user 91 []
def pulseDemand : Demand := ⟨pulse, 0, false⟩
def auditDemand : Demand := ⟨audit, 0, false⟩
def operations : Operations := fun _ _ => some (.scalar, .scalar)
def policy : Syntax.TicketPolicy := fun _ => ActionRequirements.resumeOnly

def pulseRequest : Code := .perform (Instantiation.freezeEffect pulse) 0 .unit
def auditRequest : Code := .perform (Instantiation.freezeEffect audit) 0 .unit
def body : Code := .bind 7 auditRequest (.resume 10 .unit)
def clauses : Clauses := .cons 0 5 10 body .nil
def handler : HandlerData := ⟨90, pulse, clauses, .none, .integer, rfl⟩

def pendingCode : Nat → Code
  | 0 => .integer 0
  | n + 1 => .bind 9 pulseRequest (pendingCode n)
theorem pending_dependencies (n : Nat) : (pendingCode n).dependencies = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pendingCode, Code.dependencies, pulseRequest, pulse, Instantiation.freezeEffect, Instantiation.Effect.resources, effectAtoms, Syntax.without, ih]

def pending (n : Nat) : PlainData := ⟨.bind 8 (pendingCode n), .none, .unit, .integer, [], by
  simp [Context.dependencies, Context.plug, Code.dependencies, pending_dependencies, Syntax.without, Execution.Scope.translate]⟩

def capture (n : Nat) : Stack := .push (.plain (pending n)) (.push (.handler handler) .nil)
def table (bound : Footprint) : List (Nat × ClauseContract) := [(0, ⟨false, some bound, none⟩)]
def tables (bound : Footprint) : Tables := fun data =>
  if data.effectInst = pulse then table bound else [(0, ⟨false, some [], none⟩)]
def auditHandler : HandlerData := ⟨91, audit, .cons 0 6 11 (.resume 11 .unit) .nil, .none, .integer, rfl⟩
def outside : Stack := .push (.handler auditHandler) .nil

def header : Header := ⟨10, .scalar, .scalar, false⟩
def expression : RowExpr := .append
  (.through (header.context [] .available) (.literal [auditDemand]))
  (.append (.through (header.context [] .available) (.literal [])) (.through [] .resume))

theorem body_schema : Schema operations policy header [] environment .available body .consumed .scalar expression :=
  .bind (.stable (.perform rfl .unit)) (.resume rfl (.stable .unit))

theorem body_row (resumeRow : Footprint) : expression.eval resumeRow (some []) = some (auditDemand :: resumeRow) := by
  simp [expression, RowExpr.eval, Header.context, Header.ticket, header, ClauseProtection.phaseContext,
    ClauseProtection.ownedMode, residualize, DisposalProtection.through_barrier, qualify, merge, auditDemand]

theorem body_checked (resumeRow : Footprint) : Derives operations policy (header.ticket resumeRow (some [])) [] environment
    .available body .consumed .scalar (auditDemand :: resumeRow) :=
  ParametricClauseRows.instantiate body_schema (body_row resumeRow)

theorem no_exact_self_row (row : Footprint) : row ≠ auditDemand :: row := by
  intro same
  have lengths := congrArg List.length same
  simp only [List.length_cons] at lengths
  omega

theorem perform_value_row
    (source : Summarizes operations environment (.perform (Instantiation.freezeEffect requested) operation value) contract row)
    (isValue : value.IsValue) : row = [⟨requested, operation, false⟩] := by
  generalize shape : Code.perform (Instantiation.freezeEffect requested) operation value = code at source
  cases source <;> try cases shape
  case perform payload known =>
    obtain ⟨effectEq, operationEq, operandEq⟩ := Code.perform.inj shape
    cases freeze_effect_injective effectEq
    cases operationEq
    cases operandEq
    have empty := value_has_no_immediate_demands payload isValue
    simp only [empty, List.nil_append]

theorem pending_one_source_row (source : SavedFrameRequirements.FrameSource operations (.plain (pending 1)) row) :
    row = [pulseDemand] := by
  cases source with
  | plain context => cases context with
      | bind summary => cases summary with
          | bind first second =>
              have firstRow := perform_value_row first trivial
              have secondRow := value_has_no_immediate_demands second trivial
              simp only [firstRow, secondRow, List.append_nil, pulseDemand]

theorem handler_row_empty (source : SavedFrameRequirements.Rows operations arbitraryTables (.push (.handler handler) .nil) row) : row = [] := by
  cases source with
  | push frame exported rest =>
      cases frame
      cases rest
      have empty := Option.some.inj exported
      rw [← empty]
      rfl

theorem capture_one_row (source : SavedFrameRequirements.Rows operations (tables advertised) (capture 1) row) : row = advertised := by
  cases source with
  | push frame exported rest =>
      have empty := handler_row_empty rest
      have raw := pending_one_source_row frame
      rw [raw] at exported
      change some (advertised ++ []) = some _ at exported
      simp only [List.append_nil] at exported
      have same := Option.some.inj exported
      rw [← same, empty, List.append_nil]

/-- Reusing the enclosing occurrence's exact total clause row for the next
    same-handler request forces an impossible finite-list equation. -/
theorem exact_specialization_rejects_repetition (row : Footprint) :
    ¬ SavedFrameRequirements.Rows operations (tables (auditDemand :: row)) (capture 1) row := by
  intro source
  exact no_exact_self_row row (capture_one_row source)

theorem shared_bound_condition : Covers bound (auditDemand :: bound) ↔ auditDemand ∈ bound := by
  constructor
  · intro covered; exact covered (by simp)
  · intro included request present
    rcases List.mem_cons.mp present with same | member
    · exact same ▸ included
    · exact member

theorem least_shared_bound : Covers bound (auditDemand :: bound) → Covers bound [auditDemand] := by
  intro covered request present
  have required := shared_bound_condition.mp covered
  exact List.mem_singleton.mp present ▸ required

theorem shared_table_certified : Certified operations policy (CaptureInterfaces.localRows [auditDemand] (some []))
    environment pulse .scalar clauses (table [auditDemand]) :=
  .cons rfl (.offered (fun _ => rfl) (body_checked [auditDemand]) (by decide)) .unavailable .nil

theorem pending_summary (n : Nat) : Summarizes operations environment (pendingCode n) .scalar (List.replicate n pulseDemand) := by
  induction n generalizing environment with
  | zero => exact .integer
  | succ n ih => exact .bind (.perform rfl .unit) ih

theorem pending_frame_source (n : Nat) : SavedFrameRequirements.FrameSource operations (.plain (pending n)) (List.replicate n pulseDemand) :=
  SavedFrameRequirements.FrameSource.plain (environment := .empty) (input := .scalar) (output := .scalar) (.bind (pending_summary n))

theorem interpreted_repetitions (n : Nat) :
    residualize (contextOf (tables [auditDemand]) (.push (.handler handler) .nil)) (List.replicate n pulseDemand) =
      some (List.replicate n auditDemand) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change residualize _ ([pulseDemand] ++ List.replicate n pulseDemand) = _
      rw [residual_rows_append, ih]
      rfl

theorem actual_capture_rows (n : Nat) : SavedFrameRequirements.Rows operations (tables [auditDemand]) (capture n)
    (List.replicate n auditDemand) := by
  have suffix : SavedFrameRequirements.Rows operations (tables [auditDemand]) (.push (.handler handler) .nil) [] :=
    .push .handler rfl .nil
  simpa only [List.append_nil, capture] using SavedFrameRequirements.Rows.push (pending_frame_source n) (interpreted_repetitions n) suffix

theorem arbitrary_capture_bound (n : Nat) : Saved operations (tables [auditDemand]) (capture n) [auditDemand] := by
  refine ⟨_, actual_capture_rows n, ?_⟩
  intro request present
  simp only [List.mem_replicate, List.mem_singleton] at present ⊢
  exact present.2

theorem arbitrary_capture_interface (n : Nat) : Interface operations (tables [auditDemand]) (capture n) [auditDemand] (some []) := by
  obtain ⟨actual, rows, covered⟩ := arbitrary_capture_bound n
  exact ⟨actual, .closable rows rfl .nil, covered⟩

theorem clause_use_remains_one_shot : Uses policy (.ticket 10 (policy 10)) .available body .consumed :=
  ParametricClauseRows.schema_usage (body_schema (environment := .empty))

theorem exact_cut (n : Nat) : HandlerCut pulse ((capture n).append outside) (capture n) outside handler :=
  .push (.plain (pending n)) _ _ _ _ (by simp [ExecFrame.erase, PlainData.erase, Frame.target]) (.hit handler outside rfl)

theorem request_accepted (n : Nat) : CallableProtectionFrames.Checked operations (tables [auditDemand]) CallableProtection.Environment.empty
    ((capture n).append outside) pulseRequest .scalar := by
  refine ⟨_, .perform rfl .unit, ?_⟩
  change checkFootprint (contextOf (tables [auditDemand]) (.push (.plain (pending n)) (.push (.handler handler) outside))) [pulseDemand] = true
  rw [CallableProtectionFrames.check_plain_context]
  rfl

theorem shared_source_inputs (n : Nat) :
    Interface operations (tables [auditDemand]) (capture n) [auditDemand] (some []) ∧
      Certified operations policy (CaptureInterfaces.localRows [auditDemand] (some [])) CallableProtection.Environment.empty
        pulse .scalar clauses ((tables [auditDemand]) handler) ∧
      CallableProtectionFrames.Checked operations (tables [auditDemand]) CallableProtection.Environment.empty
        ((capture n).append outside) pulseRequest .scalar :=
  ⟨arbitrary_capture_interface n, shared_table_certified, request_accepted n⟩

theorem protection_is_not_weakened : ¬ Covers [auditDemand] [⟨audit, 0, true⟩] := by decide

end RepeatedHandler

end Ash.OneShot.EffectBounds

#print axioms Ash.OneShot.EffectBounds.covers_refl
#print axioms Ash.OneShot.EffectBounds.covers_trans
#print axioms Ash.OneShot.EffectBounds.covers_append
#print axioms Ash.OneShot.EffectBounds.covers_append_bounds
#print axioms Ash.OneShot.EffectBounds.check_covered
#print axioms Ash.OneShot.EffectBounds.qualifies_coverage
#print axioms Ash.OneShot.EffectBounds.saved_exact
#print axioms Ash.OneShot.EffectBounds.saved_checked
#print axioms Ash.OneShot.EffectBounds.resume_recomposition
#print axioms Ash.OneShot.EffectBounds.offered_body
#print axioms Ash.OneShot.EffectBounds.exact_offer
#print axioms Ash.OneShot.EffectBounds.exact_certified
#print axioms Ash.OneShot.EffectBounds.selected_contract
#print axioms Ash.OneShot.EffectBounds.selected_body
#print axioms Ash.OneShot.EffectBounds.capture_clause_certificate
#print axioms Ash.OneShot.EffectBounds.interface_saved
#print axioms Ash.OneShot.EffectBounds.interface_exact
#print axioms Ash.OneShot.EffectBounds.capture_preserves
#print axioms Ash.OneShot.EffectBounds.resume_joint
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.body_schema
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.body_row
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.body_checked
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.no_exact_self_row
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.shared_bound_condition
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.least_shared_bound
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.shared_table_certified
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.pending_summary
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.pending_frame_source
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.interpreted_repetitions
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.actual_capture_rows
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.arbitrary_capture_bound
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.arbitrary_capture_interface
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.clause_use_remains_one_shot
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.protection_is_not_weakened
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.pending_dependencies
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.perform_value_row
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.pending_one_source_row
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.handler_row_empty
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.capture_one_row
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.exact_specialization_rejects_repetition
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.exact_cut
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.request_accepted
#print axioms Ash.OneShot.EffectBounds.RepeatedHandler.shared_source_inputs
