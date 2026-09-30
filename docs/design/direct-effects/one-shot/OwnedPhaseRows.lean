import UniformClauseBounds

/-!
Saved requirements with phase-changing plain segments whose live owner boundary
is retained in the same stack. The source chain retains actual scope resolution,
full contracts and one-shot phases. Open segments and intervening non-plain
frames inside such a chain still require integration.
-/

namespace Ash.OneShot.OwnedPhaseRows
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open CallableProtectionFrames (Tables contextOf)
open ClauseProtection (Ticket)
open ClauseProtectionFrames (ContextDerives)
open PhaseContextChains (stackOf)
open Syntax (UseState)

inductive Chain (operations : Operations) (policy : Syntax.TicketPolicy) (ticket : Ticket)
    (owner : Nat) (environment : CallableProtection.Environment) :
    List PlainData → UseState → Contract → UseState → Contract → Footprint → Prop where
  | nil : Chain operations policy ticket owner environment [] phase contract phase contract []
  | cons (source : ContextDerives operations policy ticket [] environment frame.context before input middle intermediate headRow)
      (resolved : before = .available → middle = .consumed → frame.scope.resolve ticket.binder = some owner)
      (rest : Chain operations policy ticket owner environment frames middle intermediate after output restRow) :
      Chain operations policy ticket owner environment (frame :: frames) before input after output (headRow ++ restRow)

theorem chain_source (chain : Chain operations policy ticket owner environment frames before input after output row) :
    PhaseContextChains.Chain operations policy ticket [] environment frames before input after output row := by
  induction chain with
  | nil => exact .nil
  | cons source resolved rest ih => exact .cons source ih

theorem chain_authenticate
    (chain : PhaseContextChains.Chain operations policy ticket [] environment frames before input after output row)
    (owners : ∀ frame ∈ frames, ∀ a b effects,
      ContextDerives operations policy ticket [] environment frame.context .available a .consumed b effects →
        frame.scope.resolve ticket.binder = some owner) :
    Chain operations policy ticket owner environment frames before input after output row := by
  induction chain with
  | nil => exact .nil
  | cons source rest ih =>
      refine .cons source ?_ (ih (fun frame member => owners frame (List.mem_cons_of_mem _ member)))
      intro first second
      cases first
      cases second
      exact owners _ List.mem_cons_self _ _ _ source

inductive Protocol (owner : Nat) : UseState → UseState → List Nat → Prop where
  | idle : Protocol owner phase phase []
  | consume : Protocol owner .available .consumed [owner]

theorem protocol_compose (first : Protocol owner before middle left) (second : Protocol owner middle after right) :
    Protocol owner before after (left ++ right) := by
  cases first <;> cases second <;> first | exact .idle | exact .consume

theorem frame_protocol
    (source : ContextDerives operations policy ticket [] environment frame.context before input after output row)
    (resolved : before = .available → after = .consumed → frame.scope.resolve ticket.binder = some owner)
    (runtime : FrameDemand policy tickets (.plain frame) names) : Protocol owner before after names := by
  have monotone := ClauseProtectionFrames.context_phase_monotone source
  cases before <;> cases after
  · rw [PhaseFrameUsage.unchanged_frame_demand_empty source runtime]; exact .idle
  · rw [PhaseFrameUsage.consuming_frame_demand source runtime (resolved rfl rfl)]; exact .consume
  · cases monotone rfl
  · rw [PhaseFrameUsage.unchanged_frame_demand_empty source runtime]; exact .idle

theorem chain_protocol
    (source : Chain operations policy ticket owner environment frames before input after output row)
    (runtime : StackUsage policy tickets (stackOf frames .nil) outside names) : Protocol owner before after names := by
  induction source generalizing names with
  | nil => cases runtime; exact .idle
  | cons source resolved rest ih => cases runtime with
      | push frame accessible remaining => exact protocol_compose (frame_protocol source resolved frame) (ih remaining)

theorem chain_consumes_actual_owner
    (source : Chain operations policy ticket owner environment frames .available input .consumed output row)
    (runtime : StackUsage policy tickets (stackOf frames .nil) outside names) : names = [owner] := by
  cases chain_protocol source runtime
  rfl

inductive Closing (operations : Operations) (capture : Stack) : Option Footprint → Prop where
  | protectedCapture (held : ProtectionContexts.protectedMode capture.erase = true) : Closing operations capture none
  | closable (built : makePlan capture = some plan) (source : DisposalProtection.Rows operations plan row) :
      Closing operations capture (some row)

theorem exact_closing (interface : CaptureInterfaces.Interface operations tables capture row closeRow) :
    Closing operations capture closeRow := by
  cases interface with
  | protectedCapture resume held => exact .protectedCapture held
  | closable resume built source => exact .closable built source

inductive Rows (operations : Operations) (policy : Syntax.TicketPolicy) (tables : Tables) : Stack → Footprint → Prop where
  | nil : Rows operations policy tables .nil []
  | push (source : SavedFrameRequirements.FrameSource operations frame raw)
      (exported : residualize (contextOf tables tail) raw = some outward)
      (rest : Rows operations policy tables tail remaining) :
      Rows operations policy tables (.push frame tail) (outward ++ remaining)
  | live (saved : SavedFrameRequirements.Sources operations capture) (rest : Rows operations policy tables tail row) :
      Rows operations policy tables (.live owner input answer capture scope tail) row
  | spent (rest : Rows operations policy tables tail row) : Rows operations policy tables (.spent owner answer scope tail) row
  | owned (saved : Rows operations policy tables capture resumeRow) (closing : Closing operations capture closeRow)
      (pending : Chain operations policy (CaptureInterfaces.ticketFor capture resumeRow closeRow binder input answer)
        owner environment frames .available hole .consumed answer raw)
      (exported : residualize (contextOf tables tail) raw = some outward)
      (rest : Rows operations policy tables tail remaining) :
      Rows operations policy tables (stackOf frames (.live owner inputType answerType capture scope tail)) (outward ++ remaining)

inductive Checked (operations : Operations) (policy : Syntax.TicketPolicy) (tables : Tables)
    (outside : ProtectionContracts.Context) : Stack → Prop where
  | nil : Checked operations policy tables outside .nil
  | push (source : SavedFrameRequirements.FrameSource operations frame raw)
      (accepted : checkFootprint (contextOf tables tail ++ outside) raw = true)
      (rest : Checked operations policy tables outside tail) : Checked operations policy tables outside (.push frame tail)
  | live (saved : SavedFrameRequirements.Sources operations capture) (rest : Checked operations policy tables outside tail) :
      Checked operations policy tables outside (.live owner input answer capture scope tail)
  | spent (rest : Checked operations policy tables outside tail) : Checked operations policy tables outside (.spent owner answer scope tail)
  | owned (saved : Rows operations policy tables capture resumeRow) (closing : Closing operations capture closeRow)
      (pending : Chain operations policy (CaptureInterfaces.ticketFor capture resumeRow closeRow binder input answer)
        owner environment frames .available hole .consumed answer raw)
      (accepted : checkFootprint (contextOf tables tail ++ outside) raw = true)
      (rest : Checked operations policy tables outside tail) :
      Checked operations policy tables outside (stackOf frames (.live owner inputType answerType capture scope tail))

theorem exact_rows (rows : SavedFrameRequirements.Rows operations tables stack row) : Rows operations policy tables stack row := by
  induction rows with
  | nil => exact .nil
  | push source exported rest ih => exact .push source exported ih
  | live saved rest ih => exact .live saved ih
  | spent rest ih => exact .spent ih

theorem rows_checked (rows : Rows operations policy tables stack row) (accepted : checkFootprint outside row = true) :
    Checked operations policy tables outside stack := by
  induction rows with
  | nil => exact .nil
  | push source exported rest ih =>
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      exact .push source (by rw [← residual_check, exported]; exact accepted.1) (ih accepted.2)
  | live saved rest ih => exact .live saved (ih accepted)
  | spent rest ih => exact .spent (ih accepted)
  | owned saved closing pending exported rest ihSaved ihRest =>
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      exact .owned saved closing pending (by rw [← residual_check, exported]; exact accepted.1) (ihRest accepted.2)

theorem checked_rows (checked : Checked operations policy tables outside stack) :
    ∃ row, Rows operations policy tables stack row ∧ checkFootprint outside row = true := by
  induction checked with
  | nil => exact ⟨[], .nil, rfl⟩
  | push source accepted rest ih =>
      obtain ⟨outward, exported, admitted⟩ := residual_admitted_iff.mp accepted
      obtain ⟨remaining, rows, acceptedRest⟩ := ih
      exact ⟨outward ++ remaining, .push source exported rows, by simp only [check_footprint_append, admitted, acceptedRest, Bool.and_self]⟩
  | live saved rest ih => obtain ⟨row, rows, accepted⟩ := ih; exact ⟨row, .live saved rows, accepted⟩
  | spent rest ih => obtain ⟨row, rows, accepted⟩ := ih; exact ⟨row, .spent rows, accepted⟩
  | owned saved closing pending accepted rest ih =>
      obtain ⟨outward, exported, admitted⟩ := residual_admitted_iff.mp accepted
      obtain ⟨remaining, rows, acceptedRest⟩ := ih
      exact ⟨outward ++ remaining, .owned saved closing pending exported rows,
        by simp only [check_footprint_append, admitted, acceptedRest, Bool.and_self]⟩

theorem checked_iff_rows : Checked operations policy tables outside stack ↔
    ∃ row, Rows operations policy tables stack row ∧ checkFootprint outside row = true :=
  ⟨checked_rows, fun ⟨_, rows, accepted⟩ => rows_checked rows accepted⟩

theorem checked_append {front tail : Stack}
    (first : Checked operations policy tables (contextOf tables tail ++ outside) front)
    (second : Checked operations policy tables outside tail) : Checked operations policy tables outside (front.append tail) := by
  induction first with
  | nil => exact second
  | push source accepted rest ih =>
      exact .push source (by simpa only [context_append, List.append_assoc] using accepted) ih
  | live saved rest ih => exact .live saved ih
  | spent rest ih => exact .spent ih
  | owned saved closing pending accepted rest ih =>
      rw [PhaseContextChains.stack_tail_append]
      exact .owned saved closing pending (by simpa only [context_append, List.append_assoc] using accepted) ih

theorem recompose {capture waiting : Stack}
    (saved : Rows operations policy tables capture row)
    (accepted : checkFootprint (contextOf tables waiting ++ outside) row = true)
    (caller : Checked operations policy tables outside waiting) :
    Checked operations policy tables outside (capture.append waiting) :=
  checked_append (rows_checked saved accepted) caller

theorem request_neutral
    (source : ClauseProtection.Derives operations policy ticket inside environment before
      (.perform effect operation operand) after output row) (isValue : operand.IsValue) : before = after := by
  cases source with
  | stable summary exported => rfl
  | perform known argument exported => exact (ClauseProtection.value_summary argument isValue).2.1

/-- The existing runtime ownership invariant supplies the scope equations in
    the saved source chain. They are not a second ownership assumption. -/
theorem request_pending_checked
    (source : PhaseContextChains.Source operations policy
      (CaptureInterfaces.ticketFor capture resumeRow closeRow binder input answer) [] (contextOf tables tail) environment
      (.perform effect operation operand) frames .available after answer row)
    (runtime : ConfigurationUsage policy tickets
      ⟨.perform effect operation operand, scope, stackOf frames (.live owner inputType answerType capture caller tail)⟩)
    (saved : Rows operations policy tables capture resumeRow) (closing : Closing operations capture closeRow)
    (outside : Checked operations policy tables [] tail) (isValue : operand.IsValue) :
    Checked operations policy tables [] (stackOf frames (.live owner inputType answerType capture caller tail)) := by
  have ends := (ChainOwnerAgreement.live_source_consumes_owner source runtime).1
  cases ends
  have owners := fun frame member a b effects checked =>
    ChainOwnerAgreement.live_source_pending_owner source runtime (plain := frame) member
      (otherInside := []) (otherEnvironment := environment)
      (frameInput := a) (frameOutput := b) (frameRow := effects) checked
  cases source with
  | checked current pending accepted =>
      cases request_neutral current isValue
      have chain := chain_authenticate pending owners
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      exact .owned saved closing chain (by simpa only [List.append_nil] using accepted.2) outside

theorem cut_plain_prefix (frames : List PlainData)
    (cut : HandlerCut requested (stackOf frames base) capture tail handler) :
    ∃ suffix, capture = stackOf frames suffix ∧ HandlerCut requested base suffix tail handler := by
  induction frames generalizing capture with
  | nil => exact ⟨capture, rfl, cut⟩
  | cons plain rest ih => cases cut with
      | push frame remaining captured outside handler miss next =>
          obtain ⟨suffix, same, cut⟩ := ih next
          exact ⟨suffix, by rw [same]; rfl, cut⟩

theorem export_captured {whole capture tail : Stack}
    (cut : HandlerCut requested whole capture tail handler)
    (accepted : checkFootprint (contextOf tables whole ++ outside) raw = true) :
    ∃ row, residualize (contextOf tables capture) raw = some row ∧
      checkFootprint (contextOf tables tail ++ outside) row = true := by
  rw [handler_cut_reconstructs cut, context_append, List.append_assoc] at accepted
  exact residual_admitted_iff.mp accepted

/-- Every actual cut of a checked closed-owner segment retains its pending
    plain chain and live boundary together. Capture may cross arbitrarily many
    such segments; their dormant saved rows remain recursive source evidence. -/
theorem capture_rows
    (checked : Checked operations policy tables outside whole)
    (cut : HandlerCut requested whole capture tail handler) :
    ∃ row, Rows operations policy tables capture row ∧
      checkFootprint (contextOf tables tail ++ outside) row = true ∧ Checked operations policy tables outside tail := by
  induction checked generalizing capture tail handler with
  | nil => cases cut
  | push source accepted rest ih => cases cut with
      | hit => cases source; exact ⟨[], .push .handler rfl .nil, rfl, rest⟩
      | push frame remaining captured outside handler miss next =>
          obtain ⟨frameRow, exported, admitted⟩ := export_captured next accepted
          obtain ⟨restRow, rows, acceptedRest, tailChecked⟩ := ih next
          exact ⟨frameRow ++ restRow, .push source exported rows,
            by simp only [check_footprint_append, admitted, acceptedRest, Bool.and_self], tailChecked⟩
  | live saved rest ih => cases cut with
      | live owner input answer capture caller remaining captured outside handler next =>
          obtain ⟨row, rows, accepted, tailChecked⟩ := ih next
          exact ⟨row, .live saved rows, accepted, tailChecked⟩
  | spent rest ih => cases cut with
      | spent owner answer caller remaining captured outside handler next =>
          obtain ⟨row, rows, accepted, tailChecked⟩ := ih next
          exact ⟨row, .spent rows, accepted, tailChecked⟩
  | owned saved closing pending accepted rest ih =>
      obtain ⟨suffix, shape, innerCut⟩ := cut_plain_prefix _ cut
      cases innerCut with
      | live owner input answer capture caller remaining captured outside handler next =>
          obtain ⟨frameRow, exported, admitted⟩ := export_captured next accepted
          obtain ⟨restRow, rows, acceptedRest, tailChecked⟩ := ih next
          rw [shape]
          exact ⟨frameRow ++ restRow, .owned saved closing pending exported rows,
            by simp only [check_footprint_append, admitted, acceptedRest, Bool.and_self], tailChecked⟩

theorem capture_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (pending : Checked operations policy tables [] whole)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (parameter binder : Nat) (body : Code) (port : ScopedPorts.Port) (record : CallableJoint.TicketRecord) (row : Footprint),
      ClauseAt operation handler.clauses parameter binder body ∧
      CallableJoint.RegistryExtends registry (registry.insert owner record) ∧
      let before : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let base := Stack.live owner (ScopedPorts.embedPort port) handler.answer capture handler.scope tail
      let next := ScopedPortJoint.advanceState before ⟨body.subst parameter operand, .ticket binder owner, base⟩ [.ticket owner] []
      NamedAccessStep ambient before next ∧
      CompletionJoint.Valid declarations policy (registry.insert owner record) ambient next result outgoing bound ∧
      Rows operations policy tables capture row ∧ checkFootprint (contextOf tables tail) row = true ∧
      Checked operations policy tables [] tail := by
  obtain ⟨row, rows, accepted, rest⟩ := capture_rows pending cut
  obtain ⟨parameter, binder, body, port, residual, record, _, selected, known, extension, step, nextValid⟩ :=
    CompletionJoint.capture_without_payload_premise cut valid isValue fresh
  exact ⟨parameter, binder, body, port, record, row, selected, extension, step, nextValid,
    rows, by simpa only [List.append_nil] using accepted, rest⟩

def Interface (operations : Operations) (policy : Syntax.TicketPolicy) (tables : Tables)
    (capture : Stack) (resumeRow : Footprint) (closeRow : Option Footprint) : Prop :=
  Rows operations policy tables capture resumeRow ∧ Closing operations capture closeRow

/-- Shared clause checking also accepts the new phase-bearing capture rows.
    Their construction and bound coverage remain explicit structural premises. -/
theorem capture_source_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (interface : Interface operations policy tables capture resumeRow closeRow)
    (schemas : ParametricClauseRows.ClausesSchema operations policy clauseEnvironment requested answer handler.clauses schemaTable)
    (same : tables handler = ParametricClauseRows.specializeTable schemaTable resumeBound closeBound)
    (resume : EffectBounds.Covers resumeBound resumeRow) (closing : UniformClauseBounds.SuccessBelow closeRow closeBound)
    (cut : HandlerCut requested whole capture tail handler)
    (checked : CallableProtectionFrames.Checked operations tables operandEnvironment whole
      (.perform (Instantiation.freezeEffect requested) operation operand) output)
    (isValue : operand.IsValue) (fresh : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (parameter binder : Nat) (body : Code) (port : ScopedPorts.Port) (record : CallableJoint.TicketRecord)
      (input : Contract) (row : Footprint),
      ClauseAt operation handler.clauses parameter binder body ∧
      CallableJoint.RegistryExtends registry (registry.insert owner record) ∧
      let newTicket := CaptureInterfaces.ticketFor capture resumeRow closeRow binder input answer
      let before : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let base := Stack.live owner (ScopedPorts.embedPort port) handler.answer capture handler.scope tail
      let next := ScopedPortJoint.advanceState before ⟨body.subst parameter operand, .ticket binder owner, base⟩ [.ticket owner] []
      NamedAccessStep ambient before next ∧
      CompletionJoint.Valid declarations policy (registry.insert owner record) ambient next result outgoing bound ∧
      PhaseBoundaries.Boundary newTicket owner .available base tail handler.answer ∧
      ClauseProtection.Derives operations policy newTicket [] clauseEnvironment .available (body.subst parameter operand) .consumed answer row ∧
      checkFootprint (contextOf tables tail) row = true ∧ Interface operations policy tables capture resumeRow closeRow := by
  have certified := UniformClauseBounds.uniform_at_interface schemas same resume closing
  obtain ⟨parameter, binder, body, port, residual, record, _, selected, known, extension, step, nextValid⟩ :=
    CompletionJoint.capture_without_payload_premise cut valid isValue fresh
  obtain ⟨argument, input, row, known, source, accepted⟩ := EffectBounds.capture_clause_certificate certified cut selected checked
    (PhaseBoundaries.request_operand_closed valid isValue)
  exact ⟨parameter, binder, body, port, record, input, row, selected, extension, step, nextValid,
    PhaseBoundaries.Boundary.live rfl, source, accepted, interface⟩

theorem resume_joint {ticket : Ticket}
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume ticket.binder value, scope, stackOf frames (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (source : PhaseContextChains.Source operations policy ticket [] (contextOf tables tail) environment
      (.resume ticket.binder value) frames .available after output row)
    (saved : Rows operations policy tables capture ticket.resumeRow)
    (outside : Checked operations policy tables [] tail) (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨.resume ticket.binder value, scope, stackOf frames (.live owner input answer capture caller tail)⟩,
      issued, completed⟩, activations⟩
    let next : Configuration := ⟨value, scope, capture.append (stackOf frames (.spent owner answer caller tail))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before next [] [.ticket owner]) ∧
      CompletionJoint.Valid declarations policy registry ambient (ScopedPortJoint.advanceState before next [] [.ticket owner]) result outgoing bound ∧
      Checked operations policy tables [] next.stack := by
  obtain ⟨step, nextValid, pending⟩ := ChainOwnerAgreement.resume_joint valid source isValue
  obtain ⟨remaining, chain, oldRows, accepted⟩ := NeutralFrameRows.resume_waiting_rows source
  have waiting : Checked operations policy tables [] (stackOf frames (.spent owner answer caller tail)) := by
    have waitingFrames : Checked operations policy tables (contextOf tables (.spent owner answer caller tail) ++ []) (stackOf frames .nil) :=
      rows_checked (exact_rows oldRows) (by simpa only [contextOf, List.append_nil] using accepted)
    simpa only [PhaseContextChains.stack_tail_append, Stack.append] using checked_append waitingFrames (Checked.spent outside)
  have acceptedCapture : checkFootprint (contextOf tables (stackOf frames (.spent owner answer caller tail)) ++ []) ticket.resumeRow = true := by
    simpa only [contextOf, List.append_nil, NeutralFrameRows.plain_prefix_check] using NeutralFrameRows.resume_row_accepted source isValue
  exact ⟨step, nextValid, recompose saved acceptedCapture waiting⟩

namespace Examples

def inner : Instance := .user 71 []
def outer : Instance := .user 72 []
def operations : Operations := fun _ _ => some (.scalar, .scalar)
def policy : Syntax.TicketPolicy := fun _ => ActionRequirements.resumeOnly
def tickets : Syntax.UsageTickets := fun _ => some ActionRequirements.resumeOnly
def request : Code := .perform (Instantiation.freezeEffect outer) 0 .unit
def innerHandler : HandlerData := ⟨71, inner, .cons 0 1 10 (.resume 10 request) .nil, .none, .integer, rfl⟩
def outerHandler : HandlerData := ⟨72, outer, .cons 0 2 20 (.resume 20 .unit) .nil, .none, .integer, rfl⟩
def tables : Tables := fun _ => [(0, ⟨false, some [], some []⟩)]
def return17 : PlainData := ⟨.bind 3 (.integer 17), .none, .unit, .integer, [], rfl⟩
def saved : Stack := .push (.plain return17) (.push (.handler innerHandler) .nil)
def waiting : PlainData := ⟨.resume 10, .ticket 10 9, .unit, .integer, [9], rfl⟩
def tail : Stack := .push (.handler outerHandler) .nil
def whole : Stack := stackOf [waiting] (.live 9 .unit .integer saved .none tail)
def capture : Stack := whole
def callTicket : Ticket := CaptureInterfaces.ticketFor saved [] (some []) 10 .scalar .scalar

theorem old_plain_source_rejected : ¬ SavedFrameRequirements.FrameSource operations (.plain waiting) row := by
  intro checked
  cases checked with
  | plain context => cases context

theorem old_saved_rows_rejected : ¬ SavedFrameRequirements.Rows operations tables capture row := by
  intro rows
  cases rows with
  | push source exported rest => exact old_plain_source_rejected source

theorem saved_rows : Rows operations policy tables saved [] := by
  have frame : SavedFrameRequirements.FrameSource operations (.plain return17) [] :=
    .plain (environment := .empty) (input := .scalar) (output := .scalar) (.bind .integer)
  exact .push frame rfl (.push .handler rfl .nil)

theorem saved_closing : Closing operations saved (some []) := .closable rfl .nil

theorem pending_chain : Chain operations policy callTicket 9 CallableProtection.Environment.empty
    [waiting] .available .scalar .consumed .scalar [] := by
  have frame : ContextDerives operations policy callTicket [] CallableProtection.Environment.empty
      waiting.context .available .scalar .consumed .scalar [] := .resume rfl rfl
  exact Chain.cons (frame := waiting) frame (fun _ _ => rfl) .nil

theorem pending_frame_uses_owner : FrameDemand policy tickets (.plain waiting) [9] :=
  .plain (.consume rfl (.resume rfl .unit))

theorem saved_usage (outside : List Nat) : StackUsage policy tickets saved outside [] :=
  .push (.plain (.idle .none (.bind .unit .integer))) (by simp [frameActiveDemand])
    (.push (.handler ⟨_, .none⟩ (.cons (.resume rfl (.perform .unit)) .nil)) (by simp [frameActiveDemand]) .nil)

theorem tail_usage : StackUsage policy tickets tail [] [] :=
  .push (.handler ⟨_, .none⟩ (.cons (.resume rfl .unit) .nil)) (by simp [frameActiveDemand]) .nil

theorem request_ownership : ConfigurationUsage policy tickets ⟨request, .ticket 10 9, whole⟩ := by
  have control : StackUsage policy tickets whole [] [9] :=
    .push pending_frame_uses_owner (by decide) (.live rfl ⟨_, .none⟩ (saved_usage _) tail_usage)
  exact ⟨[], [9], .idle (.bound rfl) (.perform .unit), control, by simp,
    List.Perm.refl _, by decide⟩

theorem source_at_request : PhaseContextChains.Source operations policy callTicket [] (contextOf tables tail)
    CallableProtection.Environment.empty request [waiting] .available .consumed .scalar [⟨outer, 0, false⟩] := by
  have current : ClauseProtection.Derives operations policy callTicket [] CallableProtection.Environment.empty
      .available request .available .scalar [⟨outer, 0, false⟩] := .stable (.perform rfl .unit) rfl
  exact .checked current (chain_source pending_chain) rfl

theorem pending_checked : Checked operations policy tables [] whole :=
  request_pending_checked source_at_request request_ownership saved_rows saved_closing
    (.push .handler rfl .nil) trivial

theorem outer_cut : HandlerCut outer whole capture .nil outerHandler :=
  .push (.plain waiting) _ _ _ _ (by decide)
    (.live 9 .unit .integer saved .none _ _ _ _ (.hit outerHandler .nil rfl))

theorem captured_pending_resume : ∃ row, Rows operations policy tables capture row ∧ checkFootprint [] row = true := by
  obtain ⟨row, rows, accepted, rest⟩ := capture_rows pending_checked outer_cut
  exact ⟨row, rows, accepted⟩

theorem captured_interface : Interface operations policy tables capture [] (some []) := by
  have rest : Rows operations policy tables tail [] := .push .handler rfl .nil
  have rows : Rows operations policy tables capture [] :=
    Rows.owned (binder := 10) (input := .scalar) (answer := .scalar)
      (inputType := .unit) (answerType := .integer) (scope := .none) (outward := [])
      saved_rows saved_closing pending_chain rfl rest
  exact ⟨rows, Closing.closable rfl (.retire .nil)⟩

theorem captured_owner_demand :
    ∀ demand, StackUsage policy tickets (stackOf [waiting] .nil) [9] demand → demand = [9] :=
  fun _ runtime => chain_consumes_actual_owner pending_chain runtime

end Examples

end Ash.OneShot.OwnedPhaseRows

#print axioms Ash.OneShot.OwnedPhaseRows.chain_source
#print axioms Ash.OneShot.OwnedPhaseRows.chain_authenticate
#print axioms Ash.OneShot.OwnedPhaseRows.protocol_compose
#print axioms Ash.OneShot.OwnedPhaseRows.frame_protocol
#print axioms Ash.OneShot.OwnedPhaseRows.chain_protocol
#print axioms Ash.OneShot.OwnedPhaseRows.chain_consumes_actual_owner
#print axioms Ash.OneShot.OwnedPhaseRows.exact_closing
#print axioms Ash.OneShot.OwnedPhaseRows.exact_rows
#print axioms Ash.OneShot.OwnedPhaseRows.rows_checked
#print axioms Ash.OneShot.OwnedPhaseRows.checked_rows
#print axioms Ash.OneShot.OwnedPhaseRows.checked_iff_rows
#print axioms Ash.OneShot.OwnedPhaseRows.checked_append
#print axioms Ash.OneShot.OwnedPhaseRows.recompose
#print axioms Ash.OneShot.OwnedPhaseRows.request_neutral
#print axioms Ash.OneShot.OwnedPhaseRows.request_pending_checked
#print axioms Ash.OneShot.OwnedPhaseRows.cut_plain_prefix
#print axioms Ash.OneShot.OwnedPhaseRows.export_captured
#print axioms Ash.OneShot.OwnedPhaseRows.capture_rows
#print axioms Ash.OneShot.OwnedPhaseRows.capture_joint
#print axioms Ash.OneShot.OwnedPhaseRows.capture_source_joint
#print axioms Ash.OneShot.OwnedPhaseRows.resume_joint
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.old_plain_source_rejected
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.old_saved_rows_rejected
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.saved_rows
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.saved_closing
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.pending_chain
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.pending_frame_uses_owner
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.saved_usage
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.tail_usage
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.request_ownership
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.source_at_request
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.pending_checked
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.outer_cut
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.captured_pending_resume
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.captured_interface
#print axioms Ash.OneShot.OwnedPhaseRows.Examples.captured_owner_demand
