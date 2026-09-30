import ClauseProtectionFrames
import CompletionJoint

/-!
Realize a source continuation phase at an actual live or spent owner boundary.
The prefix and outside context come from the runtime stack. Focus and return
join source certificates to the existing historical ownership/type invariant.
Source contract/port agreement and capture-row provenance remain separate.
-/

namespace Ash.OneShot.PhaseBoundaries
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts
open CallableProtectionFrames (Tables contextOf)
open ClauseProtection (Ticket Derives exportAt phaseContext)
open Syntax (UseState)

variable {ticket : Ticket}
variable {front otherFront nextFront stack : Stack} {state : RunState}

/-- The boundary stores an actual outside tail and answer type. A live
    boundary also realizes the source ticket's protection bit. -/
inductive Boundary (ticket : Ticket) (owner : Nat) : UseState → Stack → Stack → Ty → Prop where
  | live (held : ticket.held = ProtectionContexts.protectedMode capture.erase) :
      Boundary ticket owner .available (.live owner input answer capture caller tail) tail answer
  | spent : Boundary ticket owner .consumed (.spent owner answer caller tail) tail answer

theorem boundary_check (boundary : Boundary ticket owner phase base tail answer) :
    checkFootprint (phaseContext ticket (contextOf tables front) phase ++ contextOf tables tail) row =
      checkFootprint (contextOf tables (front.append base)) row := by
  cases boundary with
  | live held => exact ClauseProtection.available_stack_check tables front _ tail held
  | spent => exact ClauseProtection.consumed_stack_check tables front tail

theorem exported_check (boundary : Boundary ticket owner phase base tail answer)
    (exported : exportAt ticket (contextOf tables front) phase demands = some row) :
    checkFootprint (contextOf tables (front.append base)) demands =
      checkFootprint (contextOf tables tail) row := by
  rw [← boundary_check boundary, ← ProtectionResiduals.residual_check]
  change ProtectionResiduals.checkResidual (contextOf tables tail)
    (exportAt ticket (contextOf tables front) phase demands) = _
  rw [exported]
  rfl

theorem boundary_occurs (boundary : Boundary ticket owner phase base tail answer) :
    (owner, phase) ∈ (front.append base).erase.ticketStates := by
  cases boundary <;>
    simp [erase_append, Stack.erase, Typing.ticket_states_append, Control.ticketStates]

theorem available_owns (boundary : Boundary ticket owner .available base tail answer) :
    Owner.ticket owner ∈ (front.append base).erase.owners := by
  cases boundary
  simp [erase_append, Stack.erase, Control.owners]

theorem consumed_occurs (boundary : Boundary ticket owner .consumed base tail answer) :
    owner ∈ (front.append base).erase.spentNames := by
  cases boundary
  simp [erase_append, Stack.erase, Execution.spent_names_append, Control.spentNames]

theorem phase_unique (names : stack.erase.ticketNames.Nodup)
    (left : Boundary ticket owner phase base tail answer) (leftShape : stack = front.append base)
    (right : Boundary otherTicket owner otherPhase otherBase otherTail otherAnswer)
    (rightShape : stack = otherFront.append otherBase) : phase = otherPhase := by
  have leftOccurs : (owner, phase) ∈ stack.erase.ticketStates := by
    rw [leftShape]
    exact boundary_occurs left
  have rightOccurs : (owner, otherPhase) ∈ stack.erase.ticketStates := by
    rw [rightShape]
    exact boundary_occurs right
  exact Typing.unique_ticket_state_in_list
    (by simpa only [Typing.ticket_states_names] using names) leftOccurs rightOccurs

theorem available_not_completed (ledger : Ledger state.erase)
    (shape : state.configuration.stack = front.append base)
    (boundary : Boundary ticket owner .available base tail answer) : Owner.ticket owner ∉ state.completed := by
  apply ledger_no_live_completed_alias ledger
  change Owner.ticket owner ∈ state.configuration.stack.erase.owners
  rw [shape]
  exact available_owns boundary

theorem consumed_completed (ledger : Ledger state.erase) (history : NameHistory state activations)
    (shape : state.configuration.stack = front.append base)
    (boundary : Boundary ticket owner .consumed base tail answer) : Owner.ticket owner ∈ state.completed := by
  have present : owner ∈ state.configuration.stack.erase.spentNames := by
    rw [shape]
    exact consumed_occurs boundary
  have positive := List.count_pos_iff.mpr present
  have bound := spent_name_count_le_completed ledger history owner
  exact List.count_pos_iff.mp (by omega)

/-- This reuses the execution induction for ledger preservation and monotone
    completion history; no bound on nesting or execution length is needed. -/
theorem consumed_never_available (steps : RunSteps before after)
    (ledger : Ledger before.erase) (history : NameHistory before activations)
    (beforeShape : before.configuration.stack = front.append base)
    (spent : Boundary ticket owner .consumed base tail answer)
    (afterShape : after.configuration.stack = nextFront.append nextBase) :
    ¬ Boundary nextTicket owner .available nextBase nextTail nextAnswer := by
  intro live
  exact available_not_completed (run_steps_preserve_ledger steps ledger) afterShape live
    (run_steps_completed_mono steps (consumed_completed ledger history beforeShape spent))

/-- The ordinary port/effect invariant authenticates the actual boundary's
    answer against its existing registry. This does not identify CP.scalar
    with Unit or otherwise equate the two contract languages. -/
theorem recorded_answer (boundary : Boundary ticket owner phase base tail answer)
    (typed : ScopedPorts.EffectConfigurationTyped signature tickets world
      ⟨expression, scope, front.append base⟩ result outgoing) :
    ∃ contract, tickets owner = some contract ∧ contract.answer = ScopedPorts.eraseType answer := by
  cases boundary with
  | live held =>
      obtain ⟨contract, known, _, answerEq⟩ := ScopedPortJoint.active_live_contract typed
      exact ⟨contract, known, answerEq⟩
  | spent =>
      obtain ⟨type, effects, expression, ports, control⟩ := typed
      obtain ⟨middle, inside, outside⟩ := ScopedPorts.effect_stack_decompose front control
      cases outside with
      | spent known scope rest bound =>
          obtain ⟨middlePort, frontPorts, outsidePorts⟩ := ScopedPorts.stack_typed_decompose front ports
          cases outsidePorts with
          | spent recorded caller rest =>
              simp only [ScopedPorts.EffectTickets.types, known, Option.map_some] at recorded
              exact ⟨_, known, (Prod.mk.inj (Option.some.inj recorded)).2⟩

/-- Once a request's operand is a value, its phase certificate supplies an
    ordinary source summary checked at the actual dispatch stack. -/
theorem request_checked (boundary : Boundary ticket owner before base tail answer)
    (checked : Derives operations policy ticket (contextOf tables front) environment before
      (.perform effect operation operand) after output row)
    (accepted : checkFootprint (contextOf tables tail) row = true) (isValue : operand.IsValue) :
    before = after ∧ CallableProtectionFrames.Checked operations tables environment (front.append base)
      (.perform effect operation operand) output := by
  cases checked with
  | stable summary exported =>
      exact ⟨rfl, _, summary, (exported_check boundary exported).trans accepted⟩
  | perform known operand exported =>
      obtain ⟨summary, same, empty⟩ := ClauseProtection.value_summary operand isValue
      cases same
      rw [empty, List.nil_append] at accepted
      exact ⟨rfl, _, Summarizes.perform known summary, (exported_check boundary exported).trans accepted⟩

theorem request_operand_closed
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ result outgoing bound) (isValue : operand.IsValue) :
    ClosedValue operand := by
  obtain ⟨type, effects, expression, ports, control⟩ := valid.joint.effects
  cases expression with
  | checked scopeTyped typed =>
      obtain ⟨input, output, available, operandTyped⟩ := ScopedPorts.typed_perform_inversion typed
      exact ScopedPorts.typed_value_closed operandTyped isValue

/-- Capture chooses the same clause, raw ports, registry record and successor
    for the source certificate and the existing joint machine invariant.
    The supplied capture rows are still not inferred from the saved prefix. -/
theorem capture_preserves
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (certified : CertifiedClauseRows.Certified operations policy captures clauseEnvironment requested answer
      handler.clauses (tables handler))
    (cut : HandlerCut requested whole capture tail handler)
    (checked : CallableProtectionFrames.Checked operations tables operandEnvironment whole
      (.perform (Instantiation.freezeEffect requested) operation operand) output)
    (isValue : operand.IsValue) (fresh : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (parameter binder : Nat) (body : Code) (port : ScopedPorts.Port) (record : CallableJoint.TicketRecord)
      (input : CallableProtection.Contract) (row : Footprint),
      ClauseAt operation handler.clauses parameter binder body ∧
      (∃ argument, DeclarationResults.signature declarations requested operation = some (argument, port)) ∧
      (∃ argument, operations requested operation = some (argument, input)) ∧
      CallableJoint.RegistryExtends registry (registry.insert owner record) ∧
      let newTicket := CertifiedClauseRows.clauseTicket captures operation parameter binder body input answer
        (ProtectionContexts.protectedMode capture.erase)
      let before : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let base := Stack.live owner (ScopedPorts.embedPort port) handler.answer capture handler.scope tail
      let next := ScopedPortJoint.advanceState before ⟨body.subst parameter operand, .ticket binder owner, base⟩
        [.ticket owner] []
      NamedAccessStep ambient before next ∧
      CompletionJoint.Valid declarations policy (registry.insert owner record) ambient next result outgoing bound ∧
      Boundary newTicket owner .available base tail handler.answer ∧
      Derives operations policy newTicket [] clauseEnvironment .available
        (body.subst parameter operand) .consumed answer row ∧
      checkFootprint (contextOf tables tail) row = true := by
  obtain ⟨parameter, binder, body, port, residual, record, _, selected, portKnown, extension, step, nextValid⟩ :=
    CompletionJoint.capture_without_payload_premise cut valid isValue fresh
  obtain ⟨argument, input, row, known, _, bodyChecked, accepted⟩ :=
    CertifiedClauseRows.capture_clause_certificate certified cut selected checked (request_operand_closed valid isValue)
  exact ⟨parameter, binder, body, port, record, input, row, selected, portKnown, ⟨argument, known⟩, extension, step, nextValid,
    Boundary.live rfl, bodyChecked, accepted⟩

/-- Focus chooses its actual frame annotations from ordinary typing, and
    preserves that same named machine's ownership and full result invariant.
    Both source contexts are projections of its actual prefix and tail. -/
theorem focus_preserves
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨whole, scope, front.append base⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (boundary : Boundary ticket owner before base tail answer)
    (checked : Derives operations policy ticket (contextOf tables front) environment before whole after output row)
    (accepted : checkFootprint (contextOf tables tail) row = true)
    (focus : Focus whole child position) :
    ∃ plain : PlainData, plain.context = position ∧ plain.scope = scope ∧
      ∃ middle input childRow remainder,
        NamedAccessStep ambient
          ⟨⟨⟨whole, scope, front.append base⟩, issued, completed⟩, activations⟩
          (ScopedPortJoint.advanceState
            ⟨⟨⟨whole, scope, front.append base⟩, issued, completed⟩, activations⟩
            ⟨child, scope, (Stack.push (.plain plain) front).append base⟩ [] []) ∧
        CompletionJoint.Valid declarations policy registry ambient
          (ScopedPortJoint.advanceState
            ⟨⟨⟨whole, scope, front.append base⟩, issued, completed⟩, activations⟩
            ⟨child, scope, (Stack.push (.plain plain) front).append base⟩ [] []) result outgoing bound ∧
        Boundary ticket owner before base tail answer ∧
        Derives operations policy ticket (contextOf tables (.push (.plain plain) front)) environment
          before child middle input childRow ∧
        checkFootprint (contextOf tables tail) childRow = true ∧
        ClauseProtectionFrames.Pending operations policy ticket (contextOf tables front) (contextOf tables tail)
          environment plain middle input after output remainder := by
  obtain ⟨plain, sameContext, sameScope, step, nextValid⟩ := CompletionJoint.focus_preserves valid focus
  have actualFocus : Focus whole child plain.context := sameContext ▸ focus
  obtain ⟨middle, input, childRow, remainder, _, childChecked, childAccepted, pending⟩ :=
    ClauseProtectionFrames.focus_step (tail := front.append base) checked accepted actualFocus
  exact ⟨plain, sameContext, sameScope, middle, input, childRow, remainder,
    step, nextValid, boundary, childChecked, childAccepted, pending⟩

/-- A returned value uses the current boundary phase, never the phase at
    which its frame was first pushed. Closure comes from the joint invariant. -/
theorem plug_preserves
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, .push (.plain plain) (front.append base)⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (boundary : Boundary ticket owner current base tail answer)
    (pending : ClauseProtectionFrames.Pending operations policy ticket (contextOf tables front) (contextOf tables tail)
      savedEnvironment plain middle input after output remainder)
    (returned : Derives operations policy ticket (contextOf tables (.push (.plain plain) front)) currentEnvironment
      current value middle input row) (isValue : value.IsValue) :
    current = middle ∧
      NamedAccessStep ambient
        ⟨⟨⟨value, scope, .push (.plain plain) (front.append base)⟩, issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨value, scope, .push (.plain plain) (front.append base)⟩, issued, completed⟩, activations⟩
          ⟨plain.context.plug value, plain.scope, front.append base⟩ [] []) ∧
      CompletionJoint.Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState
          ⟨⟨⟨value, scope, .push (.plain plain) (front.append base)⟩, issued, completed⟩, activations⟩
          ⟨plain.context.plug value, plain.scope, front.append base⟩ [] []) result outgoing bound ∧
      Boundary ticket owner middle base tail answer ∧
      Derives operations policy ticket (contextOf tables front) savedEnvironment middle
        (plain.context.plug value) after output remainder ∧
      checkFootprint (contextOf tables tail) remainder = true := by
  obtain ⟨same, _, suffix, accepted⟩ := ClauseProtectionFrames.plug_step
    (scope := scope) (tail := front.append base) pending returned (CompletionJoint.current_closed_value valid isValue)
  obtain ⟨step, nextValid⟩ := CompletionJoint.plug_preserves valid isValue
  exact ⟨same, step, nextValid, same ▸ boundary, suffix, accepted⟩

namespace Examples
open CallableFrames.Examples (functionType clauseBody clauses handler captured outside spent s0 s1 pendingFunction)
open CallableJoint.CaptureExample (policy initial atRequest liveState spentState source_enters_request)
open CallableContracts.Examples (identity scalar)
open GenerativeFrames.Examples (declarations)
open ContinuationBounds.Examples (family)

def operations : Operations := fun _ _ => some (.scalar, .scalar)
def captures : CertifiedClauseRows.CaptureRows := fun _ _ _ _ _ => ([], [])
def functionContract : CallableProtection.Contract := .function .scalar .scalar []
def phaseTicket (held : Bool) : Ticket := ⟨10, .scalar, functionContract, held, [], []⟩
def tables : Tables := fun _ => [(0, ⟨false, some [], some []⟩)]

theorem clause_checked : Derives operations policy (phaseTicket held) [] environment
    .available clauseBody .consumed functionContract [] := by
  have argument : Derives operations policy (phaseTicket held) [] environment .available
      (.integer 17) .available .scalar [] := .stable .integer rfl
  have resumed : Derives operations policy (phaseTicket held) [] environment .available
      (.resume 10 (.integer 17)) .consumed functionContract [] := .resume rfl argument rfl
  exact .bind resumed (.stable (.variable rfl) rfl)

theorem clauses_certified : CertifiedClauseRows.Certified operations policy captures environment family
    functionContract clauses (tables handler) :=
  .cons rfl (.offered (fun _ => rfl) clause_checked) (.offered (fun _ => rfl) clause_checked) .nil

theorem request_checked : CallableProtectionFrames.Checked operations tables environment (captured.append outside)
    (.perform (Instantiation.freezeEffect family) 0 .unit) .scalar :=
  ⟨_, .perform rfl .unit, by decide⟩

theorem capture_joined : ∃ registry row,
    NamedAccessStep [] atRequest (liveState s1) ∧
    CompletionJoint.Valid declarations policy registry [] (liveState s1) .integer [] scalar ∧
    Boundary (phaseTicket false) 5 .available s1.stack outside functionType ∧
    Derives operations policy (phaseTicket false) [] CallableProtection.Environment.empty
      .available clauseBody .consumed functionContract row ∧
    checkFootprint (contextOf tables outside) row = true := by
  obtain ⟨parameter, binder, body, port, record, input, row, selected, portKnown, inputKnown,
      extension, step, valid, boundary, source, accepted⟩ :=
    capture_preserves (CompletionJoint.callable_valid_included source_enters_request.2)
      (clauses_certified (environment := CallableProtection.Environment.empty)) CallableFrames.Examples.selected_cut
      (request_checked (environment := CallableProtection.Environment.empty)) trivial (owner := 5) (by decide)
  cases selected with
  | hit =>
      obtain ⟨argumentPort, portKnown⟩ := portKnown
      change some (ScopedPorts.Port.unit, ScopedPorts.Port.integer) = some (argumentPort, port) at portKnown
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj portKnown)
      obtain ⟨argument, inputKnown⟩ := inputKnown
      change some (CallableProtection.Contract.scalar, CallableProtection.Contract.scalar) = some (argument, input) at inputKnown
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj inputKnown)
      refine ⟨CallableJoint.Registry.insert (fun _ => none) 5 record, row, ?_, ?_, ?_, ?_, accepted⟩
      · simpa [atRequest, liveState, s0, s1, handler, clauses, clauseBody, Code.subst,
          ScopedPortJoint.advanceState, enteredActivations, ScopedPorts.embedPort] using step
      · simpa [atRequest, liveState, s0, s1, handler, clauses, clauseBody, Code.subst,
          ScopedPortJoint.advanceState, enteredActivations, ScopedPorts.embedPort] using valid
      · exact Boundary.live rfl
      · exact source
  | pass different => exact False.elim (different rfl)

def afterClausePlug : NamedState :=
  spentState ⟨.bind 4 identity (.variable 4), .ticket 10 5, spent⟩

/-- The saved callable returns through its original handler, then fills the
    clause's pending bind at the consumed boundary. Every event preserves the
    same historical joint invariant. -/
theorem resume_and_return
    (valid : CompletionJoint.Valid declarations policy registry [] (liveState s1) .integer [] scalar) :
    NamedAccessSteps [] (liveState s1) afterClausePlug ∧
    CompletionJoint.Valid declarations policy registry [] afterClausePlug .integer [] scalar ∧
    Derives operations policy (phaseTicket false) [] CallableProtection.Environment.empty .consumed
      (.bind 4 identity (.variable 4)) .consumed functionContract [] ∧
    Owner.ticket 5 ∈ afterClausePlug.execution.completed := by
  have position : Focus clauseBody (.resume 10 (.integer 17)) (.bind 4 (.variable 4)) :=
    .bind (by intro impossible; cases impossible)
  obtain ⟨plain, shape, savedScope, middle, input, childRow, remainder, e1, c2, _, _, _, _⟩ :=
    focus_preserves (front := .nil) (tables := tables) valid (Boundary.live rfl)
      (clause_checked (held := false) (environment := CallableProtection.Environment.empty)) (by decide) position
  obtain ⟨e2, c3⟩ := CompletionJoint.resume_preserves (front := .push (.plain plain) .nil) c2 rfl trivial
  obtain ⟨e3, c4⟩ := CompletionJoint.plug_preserves c3 trivial
  obtain ⟨e4, c5⟩ := CompletionJoint.bind_preserves c4 trivial
  obtain ⟨e5, c6⟩ := CompletionJoint.handler_return_preserves c5 trivial
  have pending : ClauseProtectionFrames.Pending operations policy (phaseTicket false) [] (contextOf tables outside)
      CallableProtection.Environment.empty plain .consumed functionContract .consumed functionContract [] := by
    constructor
    · rw [shape]
      exact .bind (.stable (.variable rfl) rfl)
    · decide
  have returned : Derives operations policy (phaseTicket false) [.barrier false]
      CallableProtection.Environment.empty .consumed identity .consumed functionContract [] :=
    .stable (.lambda (.variable rfl)) rfl
  obtain ⟨_, e6, c7, _, suffix, _⟩ := plug_preserves (front := .nil) (tables := tables) c6
    Boundary.spent pending returned trivial
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [ScopedPortJoint.advanceState, liveState, s1, afterClausePlug, spentState, captured, handler,
      pendingFunction, spent, shape, savedScope, ScopedExecution.Context.plug, Code.subst, enteredActivations,
      clauseBody, identity, Stack.append] using
      (NamedAccessSteps.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.refl _)))))))
  · simpa [ScopedPortJoint.advanceState, liveState, s1, afterClausePlug, spentState, captured, handler,
      pendingFunction, spent, shape, savedScope, ScopedExecution.Context.plug, Code.subst, enteredActivations,
      clauseBody, identity, Stack.append] using c7
  · simpa [shape, ScopedExecution.Context.plug, identity, Code.subst, contextOf] using suffix
  · decide

theorem admitted_prefix_through_consumed_return : ∃ registry,
    NamedAccessSteps [] initial afterClausePlug ∧
    CompletionJoint.Valid declarations policy registry [] afterClausePlug .integer [] scalar := by
  obtain ⟨registry, row, captureStep, capturedValid, _, _, _⟩ := capture_joined
  obtain ⟨continuation, returned, _, _⟩ := resume_and_return capturedValid
  exact ⟨registry, CallableJoint.execution_append source_enters_request.1 (.next captureStep continuation), returned⟩

theorem wrong_protection_rejected :
    ¬ Boundary (phaseTicket true) 5 .available s1.stack outside functionType := by
  intro boundary
  cases boundary with
  | live held =>
      change true = false at held
      cases held

theorem completed_owner_cannot_be_available
    (shape : afterClausePlug.execution.configuration.stack = front.append base) :
    ¬ Boundary ticket 5 .available base tail answer := by
  obtain ⟨registry, _, valid⟩ := admitted_prefix_through_consumed_return
  intro boundary
  exact available_not_completed valid.joint.ledger shape boundary (by decide)

end Examples

end Ash.OneShot.PhaseBoundaries

#print axioms Ash.OneShot.PhaseBoundaries.boundary_check
#print axioms Ash.OneShot.PhaseBoundaries.exported_check
#print axioms Ash.OneShot.PhaseBoundaries.boundary_occurs
#print axioms Ash.OneShot.PhaseBoundaries.available_owns
#print axioms Ash.OneShot.PhaseBoundaries.consumed_occurs
#print axioms Ash.OneShot.PhaseBoundaries.phase_unique
#print axioms Ash.OneShot.PhaseBoundaries.available_not_completed
#print axioms Ash.OneShot.PhaseBoundaries.consumed_completed
#print axioms Ash.OneShot.PhaseBoundaries.consumed_never_available
#print axioms Ash.OneShot.PhaseBoundaries.recorded_answer
#print axioms Ash.OneShot.PhaseBoundaries.request_checked
#print axioms Ash.OneShot.PhaseBoundaries.request_operand_closed
#print axioms Ash.OneShot.PhaseBoundaries.capture_preserves
#print axioms Ash.OneShot.PhaseBoundaries.focus_preserves
#print axioms Ash.OneShot.PhaseBoundaries.plug_preserves
#print axioms Ash.OneShot.PhaseBoundaries.Examples.clause_checked
#print axioms Ash.OneShot.PhaseBoundaries.Examples.clauses_certified
#print axioms Ash.OneShot.PhaseBoundaries.Examples.request_checked
#print axioms Ash.OneShot.PhaseBoundaries.Examples.capture_joined
#print axioms Ash.OneShot.PhaseBoundaries.Examples.resume_and_return
#print axioms Ash.OneShot.PhaseBoundaries.Examples.admitted_prefix_through_consumed_return
#print axioms Ash.OneShot.PhaseBoundaries.Examples.wrong_protection_rejected
#print axioms Ash.OneShot.PhaseBoundaries.Examples.completed_owner_cannot_be_available
