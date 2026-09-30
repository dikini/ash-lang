import NeutralFrameRows

/-!
Occurrence-specific continuation interfaces derived from actual saved frames
and executable disposal plans. Local clause specialization replaces the opaque
CaptureRows lookup at this capture boundary. Uniform source handler contracts
and full source preservation still require integration.
-/

namespace Ash.OneShot.CaptureInterfaces
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts
open CallableProtectionFrames (Tables contextOf)
open ClauseProtection (Ticket Derives)

/-- Plan availability follows from the actual protected frames, including
    protection recursively owned by dormant captures. -/
theorem plan_available (capture : Stack) :
    (makePlan capture).isSome = !ProtectionContexts.protectedMode capture.erase := by
  induction capture with
  | nil => rfl
  | push frame rest ih =>
      cases frame <;> cases built : makePlan rest <;>
        simp_all [makePlan, Stack.erase, ExecFrame.erase, PlainData.erase, HandlerData.erase,
          ActionData.erase, closeFrame, CloseItem.frame, ProtectionContexts.protectedMode, ProtectionContexts.frameProtected]
  | live owner input answer saved caller rest ihSaved ihRest =>
      cases inner : makePlan saved <;> cases outer : makePlan rest <;>
        simp_all [makePlan, Stack.erase, ProtectionContexts.protectedMode]
  | spent owner answer caller rest ih => exact ih

/-- None denotes unavailable disposal, rather than a fabricated empty close
    plan. A present row is justified by the actual executable plan. -/
inductive Interface (operations : Operations) (tables : Tables) : Stack → Footprint → Option Footprint → Prop where
  | protectedCapture (resume : SavedFrameRequirements.Rows operations tables capture resumeRow)
      (held : ProtectionContexts.protectedMode capture.erase = true) :
      Interface operations tables capture resumeRow none
  | closable (resume : SavedFrameRequirements.Rows operations tables capture resumeRow)
      (built : makePlan capture = some plan) (closing : DisposalProtection.Rows operations plan closeRow) :
      Interface operations tables capture resumeRow (some closeRow)

theorem resume_rows (interface : Interface operations tables capture resumeRow closeRow) :
    SavedFrameRequirements.Rows operations tables capture resumeRow := by
  cases interface <;> assumption

theorem closing_available (interface : Interface operations tables capture resumeRow (some closeRow)) :
    ∃ plan, makePlan capture = some plan ∧ DisposalProtection.Rows operations plan closeRow := by
  cases interface with
  | closable resume built closing => exact ⟨_, built, closing⟩

theorem closing_unavailable (interface : Interface operations tables capture resumeRow none) :
    ProtectionContexts.protectedMode capture.erase = true ∧ makePlan capture = none := by
  cases interface with
  | protectedCapture resume held =>
      refine ⟨held, ?_⟩
      have absent := plan_available capture
      rw [held] at absent
      cases built : makePlan capture <;> simp_all

theorem closing_unprotected (interface : Interface operations tables capture resumeRow (some closeRow)) :
    ProtectionContexts.protectedMode capture.erase = false := by
  obtain ⟨plan, built, _⟩ := closing_available interface
  have available := plan_available capture
  rw [built] at available
  simpa using available.symm

theorem interface_from_sources
    (resume : SavedFrameRequirements.Rows operations tables capture resumeRow)
    (callbacks : DisposalProtection.Retained operations capture) :
    ∃ closeRow, Interface operations tables capture resumeRow closeRow := by
  cases built : makePlan capture with
  | none =>
      have held := plan_available capture
      rw [built] at held
      exact ⟨none, .protectedCapture resume (by simpa using held.symm)⟩
  | some plan =>
      obtain ⟨row, closing⟩ := DisposalProtection.captured_disposal_row callbacks built
      exact ⟨some row, .closable resume built closing⟩

/-- The old ticket representation has a total disposal-row field. Its value
    is unobservable by discard when this interface says disposal is unavailable. -/
def ticketFor (capture : Stack) (resumeRow : Footprint) (closeRow : Option Footprint)
    (binder : Nat) (input answer : Contract) : Ticket :=
  ⟨binder, input, answer, ProtectionContexts.protectedMode capture.erase, resumeRow, closeRow.getD []⟩

theorem unavailable_discard_rejected
    (interface : Interface operations tables capture resumeRow none) :
    ¬ Derives operations policy (ticketFor capture resumeRow none binder input answer) inside environment before
      (.discard binder) after output row := by
  intro source
  exact ClauseProtection.protected_discard_rejected (closing_unavailable interface).1 source

/-- This is a compatibility adapter for the existing structural clause rules;
    callers provide an occurrence's derived rows, not a key-based row oracle. -/
def localRows (resumeRow : Footprint) (closeRow : Option Footprint) : CertifiedClauseRows.CaptureRows :=
  fun _ _ _ _ _ => (resumeRow, closeRow.getD [])

def ClausesAt (operations : Operations) (policy : Syntax.TicketPolicy) (environment : CallableProtection.Environment)
    (requested : Instance) (answer : Contract) (resumeRow : Footprint) (closeRow : Option Footprint)
    (clauses : Clauses) (table : List (Nat × ClauseContract)) : Prop :=
  CertifiedClauseRows.Certified operations policy (localRows resumeRow closeRow) environment requested answer clauses table

theorem local_ticket (capture : Stack) (resumeRow : Footprint) (closeRow : Option Footprint)
    (operation parameter binder : Nat) (body : Code) (input answer : Contract) :
    CertifiedClauseRows.clauseTicket (localRows resumeRow closeRow) operation parameter binder body input answer
      (ProtectionContexts.protectedMode capture.erase) = ticketFor capture resumeRow closeRow binder input answer := rfl

/-- The same selected clause, owner, port, record and successor carry the
    occurrence's actual resumption and disposal evidence. -/
theorem capture_preserves
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (interface : Interface operations tables capture resumeRow closeRow)
    (clauses : ClausesAt operations policy clauseEnvironment requested answer resumeRow closeRow
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
      let newTicket := ticketFor capture resumeRow closeRow binder input answer
      let before : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let base := Stack.live owner (ScopedPorts.embedPort port) handler.answer capture handler.scope tail
      let next := ScopedPortJoint.advanceState before ⟨body.subst parameter operand, .ticket binder owner, base⟩
        [.ticket owner] []
      NamedAccessStep ambient before next ∧
      CompletionJoint.Valid declarations policy (registry.insert owner record) ambient next result outgoing bound ∧
      PhaseBoundaries.Boundary newTicket owner .available base tail handler.answer ∧
      Derives operations policy newTicket [] clauseEnvironment .available (body.subst parameter operand) .consumed answer row ∧
      checkFootprint (contextOf tables tail) row = true ∧
      Interface operations tables capture newTicket.resumeRow closeRow := by
  obtain ⟨parameter, binder, body, port, record, input, row, selected, portKnown, sourceKnown, extension,
    step, nextValid, boundary, source, accepted⟩ :=
    PhaseBoundaries.capture_preserves valid clauses cut checked isValue fresh
  exact ⟨parameter, binder, body, port, record, input, row, selected, portKnown, sourceKnown, extension,
    step, nextValid, boundary, source, accepted, interface⟩

theorem discard_plan
    (interface : Interface operations tables capture resumeRow closeRow)
    (source : Derives operations policy (ticketFor capture resumeRow closeRow binder input answer) inside environment before
      (.discard binder) after output row) :
    ∃ plan, makePlan capture = some plan ∧ DisposalProtection.Rows operations plan (closeRow.getD []) := by
  cases interface with
  | protectedCapture resume held =>
      exact False.elim (unavailable_discard_rejected (.protectedCapture resume held) source)
  | closable resume built closing => exact ⟨_, built, closing⟩

theorem discard_ready
    (interface : Interface operations tables capture resumeRow closeRow)
    (source : Derives operations policy (ticketFor capture resumeRow closeRow binder input answer)
      (contextOf tables front) environment .available (.discard binder) .consumed .scalar row)
    (accepted : checkFootprint (contextOf tables tail) row = true) :
    ∃ plan, makePlan capture = some plan ∧
      DisposalProtection.Ready operations (contextOf tables
        (.push (.closing closeId scope) (front.append (.spent owner answerType callerScope tail)))) plan := by
  obtain ⟨plan, built, rows⟩ := discard_plan interface source
  exact ⟨plan, built, DisposalProtection.discard_ready source rows accepted⟩

namespace Examples
open CallableFrames.Examples (handler)

def operations : Operations := fun _ _ => some (.scalar, .scalar)
def tables : Tables := fun _ => []
def effect (choice : Bool) : Instance := .user (if choice then 1 else 2) []
def body : Code := CallableFrames.Examples.clauseBody

def pending (choice : Bool) : PlainData :=
  ⟨.bind 9 (.bind 8 (.perform (Instantiation.freezeEffect (effect choice)) 0 .unit) CallableContracts.Examples.identity),
    .none, .integer, CallableFrames.Examples.functionType, [], rfl⟩
def capturedChoice (choice : Bool) : Stack := .push (.plain (pending choice)) (.push (.handler handler) .nil)
def actualRow (choice : Bool) : Footprint := [⟨effect choice, 0, false⟩]

theorem actual_saved_rows (choice : Bool) : SavedFrameRequirements.Rows operations tables (capturedChoice choice) (actualRow choice) := by
  have frame : SavedFrameRequirements.FrameSource operations (.plain (pending choice)) (actualRow choice) :=
    SavedFrameRequirements.FrameSource.plain (environment := .empty) (input := .scalar) (output := PhaseBoundaries.Examples.functionContract)
      (.bind (.bind (.perform rfl .unit) (.lambda (.variable rfl))))
  have tailRows : SavedFrameRequirements.Rows operations tables (.push (.handler handler) .nil) [] := .push .handler rfl .nil
  have through : ProtectionResiduals.residualize (contextOf tables (.push (.handler handler) .nil))
      (actualRow choice) = some (actualRow choice) := by cases choice <;> rfl
  exact .push frame through tailRows

theorem actual_interfaces (choice : Bool) : Interface operations tables (capturedChoice choice) (actualRow choice) (some []) :=
  .closable (actual_saved_rows choice) rfl .nil

theorem same_clause_at_both_captures : ClauseAt 0 handler.clauses 5 10 body := .hit

theorem same_handler_selected (choice : Bool) : HandlerCut handler.effectInst
    ((capturedChoice choice).append CallableFrames.Examples.outside) (capturedChoice choice) CallableFrames.Examples.outside handler :=
  .push (.plain (pending choice)) _ _ _ _ (by simp [ExecFrame.erase, PlainData.erase, Frame.target])
    (.hit handler CallableFrames.Examples.outside rfl)

theorem occurrence_rows_differ :
    (ticketFor (capturedChoice true) (actualRow true) (some []) 10 .scalar .scalar).resumeRow ≠
      (ticketFor (capturedChoice false) (actualRow false) (some []) 10 .scalar .scalar).resumeRow := by decide

theorem old_key_cannot_represent_both_exact_rows (captures : CertifiedClauseRows.CaptureRows) :
    ¬ ((captures 0 5 10 body false).1 = actualRow true ∧ (captures 0 5 10 body false).1 = actualRow false) := by
  intro both
  have different : actualRow true ≠ actualRow false := by decide
  exact different (both.1.symm.trans both.2)

open DisposalProtection.Examples (cellOperations cellAction nestedCapture nestedPlan nested_plan_derivation)

theorem nested_disposal_interface : Interface cellOperations tables nestedCapture [] (some []) := by
  have rows : SavedFrameRequirements.Rows cellOperations tables nestedCapture [] :=
    .live (.push (.armed (DisposalProtection.Examples.cell_callback_summary (environment := .empty))) .nil)
      (.push .cell rfl .nil)
  exact .closable rows nested_plan_derivation.2.1 nested_plan_derivation.2.2

theorem nested_disposal_is_ready : ∃ plan, makePlan nestedCapture = some plan ∧
    DisposalProtection.Ready cellOperations (contextOf tables
      (.push (.closing 21 .none) (.spent 5 .unit .none .nil))) plan := by
  have source : Derives cellOperations (fun _ => ActionRequirements.disposeOnly)
      (ticketFor nestedCapture [] (some []) 0 .scalar .scalar) [] CallableProtection.Environment.empty
      .available (.discard 0) .consumed .scalar [] := .discard rfl rfl rfl
  exact discard_ready (front := .nil) nested_disposal_interface source (tail := .nil) rfl

def protectedCapture : Stack := .live 9 .unit .unit
  (.push (.running cellAction .unit CallableProtection.Examples.unit_closed) .nil) .none .nil

theorem dormant_protection_blocks_disposal : Interface cellOperations tables protectedCapture [] none :=
  .protectedCapture (.live (.push (.running (environment := .empty) (contract := .scalar) .unit) .nil) .nil) rfl

theorem unavailable_is_not_an_empty_plan : makePlan protectedCapture = none ∧
    ¬ Derives cellOperations (fun _ => ActionRequirements.disposeOnly)
      (ticketFor protectedCapture [] none 0 .scalar .scalar) [] CallableProtection.Environment.empty
      .available (.discard 0) .consumed .scalar [] :=
  ⟨(closing_unavailable dormant_protection_blocks_disposal).2,
    unavailable_discard_rejected dormant_protection_blocks_disposal⟩

namespace Joint
open CallableFrames.Examples (functionType clauseBody clauses captured outside s0 s1 pendingFunction)
open CallableJoint.CaptureExample (policy initial atRequest liveState source_enters_request)
open CallableContracts.Examples (scalar)
open GenerativeFrames.Examples (declarations)
open ContinuationBounds.Examples (family)
open PhaseBoundaries.Examples (functionContract)

theorem capture_interface : Interface PhaseBoundaries.Examples.operations PhaseBoundaries.Examples.tables captured [] (some []) := by
  have context : ClauseProtectionFrames.ContextDerives PhaseBoundaries.Examples.operations policy
      (PhaseBoundaries.Examples.phaseTicket false)
      (contextOf PhaseBoundaries.Examples.tables (.push (.handler handler) .nil)) CallableProtection.Environment.empty
      pendingFunction.context .consumed .scalar .consumed functionContract [] :=
    .bind (.stable (.lambda (.variable rfl)) (ProtectionResiduals.residual_empty _))
  have suffix : SavedFrameRequirements.Rows PhaseBoundaries.Examples.operations PhaseBoundaries.Examples.tables
      (.push (.handler handler) .nil) [] := .push .handler rfl .nil
  have rows := NeutralFrameRows.consumed_chain_rows_append
    (PhaseContextChains.Chain.cons (frame := pendingFunction) context .nil) rfl suffix
  exact .closable rows rfl .nil

theorem admitted_capture_has_actual_interface : ∃ registry row,
    NamedAccessSteps [] initial (liveState s1) ∧
      CompletionJoint.Valid declarations policy registry [] (liveState s1) .integer [] scalar ∧
      Derives PhaseBoundaries.Examples.operations policy (ticketFor captured [] (some []) 10 .scalar functionContract)
        [] CallableProtection.Environment.empty .available clauseBody .consumed functionContract row ∧
      checkFootprint (contextOf PhaseBoundaries.Examples.tables outside) row = true ∧
      Interface PhaseBoundaries.Examples.operations PhaseBoundaries.Examples.tables captured [] (some []) := by
  have certified : ClausesAt PhaseBoundaries.Examples.operations policy CallableProtection.Environment.empty family functionContract
      [] (some []) clauses (PhaseBoundaries.Examples.tables handler) := PhaseBoundaries.Examples.clauses_certified
  obtain ⟨parameter, binder, code, port, record, input, row, selected, portKnown, inputKnown,
      extension, step, valid, boundary, source, accepted, interface⟩ :=
    capture_preserves (CompletionJoint.callable_valid_included source_enters_request.2) capture_interface certified
      CallableFrames.Examples.selected_cut (PhaseBoundaries.Examples.request_checked (environment := .empty))
      trivial (owner := 5) (by decide)
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
        CallableJoint.execution_append source_enters_request.1 (.next captureStep (.refl _)), ?_, source, accepted, interface⟩
      simpa [atRequest, liveState, s0, s1, handler, clauses, clauseBody, Code.subst,
        ScopedPortJoint.advanceState, enteredActivations, ScopedPorts.embedPort] using valid
  | pass different => exact False.elim (different rfl)

end Joint
end Examples

end Ash.OneShot.CaptureInterfaces

#print axioms Ash.OneShot.CaptureInterfaces.plan_available
#print axioms Ash.OneShot.CaptureInterfaces.resume_rows
#print axioms Ash.OneShot.CaptureInterfaces.closing_available
#print axioms Ash.OneShot.CaptureInterfaces.closing_unavailable
#print axioms Ash.OneShot.CaptureInterfaces.closing_unprotected
#print axioms Ash.OneShot.CaptureInterfaces.interface_from_sources
#print axioms Ash.OneShot.CaptureInterfaces.unavailable_discard_rejected
#print axioms Ash.OneShot.CaptureInterfaces.local_ticket
#print axioms Ash.OneShot.CaptureInterfaces.capture_preserves
#print axioms Ash.OneShot.CaptureInterfaces.discard_plan
#print axioms Ash.OneShot.CaptureInterfaces.discard_ready
#print axioms Ash.OneShot.CaptureInterfaces.Examples.actual_saved_rows
#print axioms Ash.OneShot.CaptureInterfaces.Examples.actual_interfaces
#print axioms Ash.OneShot.CaptureInterfaces.Examples.occurrence_rows_differ
#print axioms Ash.OneShot.CaptureInterfaces.Examples.old_key_cannot_represent_both_exact_rows
#print axioms Ash.OneShot.CaptureInterfaces.Examples.nested_disposal_interface
#print axioms Ash.OneShot.CaptureInterfaces.Examples.nested_disposal_is_ready
#print axioms Ash.OneShot.CaptureInterfaces.Examples.dormant_protection_blocks_disposal
#print axioms Ash.OneShot.CaptureInterfaces.Examples.unavailable_is_not_an_empty_plan
#print axioms Ash.OneShot.CaptureInterfaces.Examples.Joint.capture_interface
#print axioms Ash.OneShot.CaptureInterfaces.Examples.Joint.admitted_capture_has_actual_interface
#print axioms Ash.OneShot.CaptureInterfaces.Examples.same_clause_at_both_captures
#print axioms Ash.OneShot.CaptureInterfaces.Examples.same_handler_selected
