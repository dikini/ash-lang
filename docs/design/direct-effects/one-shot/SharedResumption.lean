import PhaseRechecking

/-!
One-shot restoration from the selected shared capture, rechecked at the caller's
current phases. The invocation row is local to the current expression; historical
capture records are retained. Successful future admission is still an obligation.
-/

namespace Ash.OneShot.SharedResumption
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open OwnerPhaseTransitions (Phases Trace spend spendAll)
open Owners (Contracts)

section Restoration
variable {front capture tail fixed : Stack}

theorem selected_capture
    (pending : SharedSourceSegments.Segment operations policy contracts tables world fixed
      (front.append (.live owner inputType answerType capture caller tail)) before input after output demand row)
    (known : contracts owner = some contract) :
    ∃ receiver savedBefore savedAfter savedRow,
      SharedSourceSegments.Segment operations policy contracts tables world receiver capture
        savedBefore contract.input savedAfter contract.answer contract.resumeDemand savedRow ∧
      EffectBounds.Covers contract.resumeRow savedRow ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      contract.input.port = ScopedPorts.eraseType inputType ∧ contract.answer.port = ScopedPorts.eraseType answerType := by
  obtain ⟨phases, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, rows⟩ :=
    SharedSourceSegments.segment_decompose (front := front) pending
  cases second with
  | live actual inputAnnotation answerAnnotation scopeKnown held consumed saved covered rest =>
      have same := Option.some.inj (actual.symm.trans known)
      subst_vars
      exact ⟨_, _, _, _, saved, covered, held, inputAnnotation, answerAnnotation⟩

theorem resume_parts
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope
      (.resume binder value) stack before after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (isValue : value.IsValue) :
    ∃ allowed ticket middle remaining restRow,
      Summary operations world Environment.empty allowed value contract.input [] ∧
      ScopedPorts.EffectScope contracts.ports scope ticket ∧ (policy binder).resume = true ∧
      contract.resumeEffects ⊆ allowed ∧ ScopedPorts.InWorld world contract.answer.port ∧
      Trace before (owner :: contract.resumeDemand) middle ∧
      SharedSourceSegments.Segment operations policy contracts tables world fixed stack
        middle contract.answer after output remaining restRow ∧
      demand = owner :: (contract.resumeDemand ++ remaining) ∧ row = contract.resumeRow ++ restRow := by
  cases source with
  | checked current scopeTyped pending accepted => cases current with
      | stable summary exported => cases summary
      | resume actual target permission operand transition admitted formed =>
          have ownerSame := Option.some.inj (target.symm.trans resolved)
          subst_vars
          have contractSame := Option.some.inj (actual.symm.trans known)
          subst_vars
          obtain ⟨summary, phases, noDemand, noRow⟩ := Owners.value_summary operand isValue
          subst_vars
          exact ⟨_, _, _, _, _, summary, scopeTyped, permission, admitted, formed, transition, pending, rfl, rfl⟩

/-- The specialized row belongs to this invocation. The waiting stack and every
    historical capture continue to use their existing shared registry. -/
theorem resume_from_rechecked
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (permission : (policy binder).resume = true)
    (operand : Summary operations world Environment.empty allowed value contract.input []) (closed : ClosedValue value)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port)
    (transition : Trace before (owner :: contract.resumeDemand) middle)
    (pending : SharedSourceSegments.Segment operations policy contracts tables world fixed
      (front.append (.live owner inputType answerType capture caller tail)) middle contract.answer after output remaining restRow)
    (received : SharedSourceSegments.Segment operations policy contracts tables world
      ((front.append (.spent owner answerType caller tail)).append fixed) capture
      (spend before owner) contract.input middle contract.answer contract.resumeDemand actual)
    (accepted : checkFootprint outside (actual ++ restRow) = true) :
    RawStep ⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩
      ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩ [] [.ticket owner] ∧
    Owners.Derives operations policy (ResumeSpecialization.sharedView contracts owner actual)
      (OwnerPhases.ofStack tables ((front.append (.live owner inputType answerType capture caller tail)).append fixed))
      world Environment.empty allowed scope before (.resume binder value) middle contract.answer
      (owner :: contract.resumeDemand) actual ∧
    SharedSourceSegments.Source operations policy contracts tables world fixed outside scope value
      (capture.append (front.append (.spent owner answerType caller tail)))
      (spend before owner) after output (contract.resumeDemand ++ remaining) (actual ++ restRow) := by
  have consumed := OwnerPhaseTransitions.trace_consumed transition List.mem_cons_self
  have waiting := SharedClosingSource.pending_live_to_spent pending consumed
  have restored := SharedSourceSegments.segment_append received waiting
  have current : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables ((capture.append (front.append (.spent owner answerType caller tail))).append fixed))
      world Environment.empty allowed scope (spend before owner) value (spend before owner) contract.input [] [] :=
    .stable operand (by simp [OwnerSource.exportAt, residual_empty])
  have invoked := (ResumeSpecialization.shared_resume_source (actual := actual)
    (inside := OwnerPhases.ofStack tables ((front.append (.live owner inputType answerType capture caller tail)).append fixed)) known resolved permission
    operand transition admitted formed scopeTyped).1
  have afterSource := SharedSourceSegments.Source.checked current scopeTyped restored accepted
  exact ⟨.resume binder owner scope caller inputType answerType front capture tail value closed resolved,
    invoked, by simpa only [List.nil_append] using afterSource⟩

/-- The actual selected boundary supplies the historical derivation. Rechecking
    computes its current endpoint, so no equality with its historical phases is
    assumed and no independently supplied after-source is needed. -/
theorem resume_requirements
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (permission : (policy binder).resume = true)
    (operand : Summary operations world Environment.empty allowed value contract.input []) (closed : ClosedValue value)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port)
    (transition : Trace before (owner :: contract.resumeDemand) middle)
    (pending : SharedSourceSegments.Segment operations policy contracts tables world fixed
      (front.append (.live owner inputType answerType capture caller tail)) middle contract.answer after output remaining restRow) :
    ∃ requirements : PhaseRechecking.Requirements contract.resumeDemand, ∃ receiver savedBefore savedRow,
      requirements.evaluate (OwnerPhases.ofStack tables receiver) savedBefore = some savedRow ∧
      EffectBounds.Covers contract.resumeRow savedRow ∧
      ∀ actual, requirements.evaluate
          (OwnerPhases.ofStack tables ((front.append (.spent owner answerType caller tail)).append fixed))
          (spend before owner) = some actual →
        checkFootprint outside (actual ++ restRow) = true →
        RawStep ⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩
          ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩ [] [.ticket owner] ∧
        Owners.Derives operations policy (ResumeSpecialization.sharedView contracts owner actual)
          (OwnerPhases.ofStack tables ((front.append (.live owner inputType answerType capture caller tail)).append fixed))
          world Environment.empty allowed scope before (.resume binder value) middle contract.answer
          (owner :: contract.resumeDemand) actual ∧
        SharedSourceSegments.Source operations policy contracts tables world fixed outside scope value
          (capture.append (front.append (.spent owner answerType caller tail)))
          (spend before owner) after output (contract.resumeDemand ++ remaining) (actual ++ restRow) := by
  obtain ⟨receiver, savedBefore, savedAfter, savedRow, saved, covered, held, inputAnnotation, answerAnnotation⟩ :=
    selected_capture pending known
  obtain ⟨requirements, original, recheck⟩ := PhaseRechecking.segment_rechecks saved
  refine ⟨requirements, receiver, savedBefore, savedRow, original, covered, ?_⟩
  intro actual checked accepted
  have received := recheck _ _ _ checked
  have endpoint := OwnerPhaseTransitions.trace_result transition
  change middle = spendAll (spend before owner) contract.resumeDemand at endpoint
  rw [← endpoint] at received
  exact resume_from_rechecked known resolved permission operand closed scopeTyped admitted formed transition pending received accepted

theorem resume_source
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail)) before after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ requirements : PhaseRechecking.Requirements contract.resumeDemand, ∃ receiver savedBefore savedRow remaining restRow,
      requirements.evaluate (OwnerPhases.ofStack tables receiver) savedBefore = some savedRow ∧
      EffectBounds.Covers contract.resumeRow savedRow ∧
      demand = owner :: (contract.resumeDemand ++ remaining) ∧ row = contract.resumeRow ++ restRow ∧
      ∀ actual, requirements.evaluate
          (OwnerPhases.ofStack tables ((front.append (.spent owner answerType caller tail)).append fixed))
          (spend before owner) = some actual →
        checkFootprint outside (actual ++ restRow) = true →
        RawStep ⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩
          ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩ [] [.ticket owner] ∧
        SharedSourceSegments.Source operations policy contracts tables world fixed outside scope value
          (capture.append (front.append (.spent owner answerType caller tail)))
          (spend before owner) after output (contract.resumeDemand ++ remaining) (actual ++ restRow) := by
  obtain ⟨allowed, ticket, middle, remaining, restRow, operand, scopeTyped, permission, admitted, formed, transition, pending, names, rows⟩ :=
    resume_parts source known resolved closed.1
  obtain ⟨requirements, receiver, savedBefore, savedRow, original, covered, recheck⟩ :=
    resume_requirements known resolved permission operand closed scopeTyped admitted formed transition pending
  refine ⟨requirements, receiver, savedBefore, savedRow, remaining, restRow, original, covered, names, rows, ?_⟩
  intro actual checked accepted
  obtain ⟨step, invoked, restored⟩ := recheck actual checked accepted
  exact ⟨step, restored⟩

theorem resume_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (source : SharedSourceSegments.Source operations policy contracts tables world .nil outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail))
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      afterPhase output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ requirements : PhaseRechecking.Requirements contract.resumeDemand, ∃ receiver savedBefore savedRow remaining restRow,
      requirements.evaluate (OwnerPhases.ofStack tables receiver) savedBefore = some savedRow ∧
      EffectBounds.Covers contract.resumeRow savedRow ∧
      demand = owner :: (contract.resumeDemand ++ remaining) ∧ row = contract.resumeRow ++ restRow ∧
      ∀ actual, requirements.evaluate
          (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))
          (spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner) = some actual →
        checkFootprint outside (actual ++ restRow) = true →
        let before : NamedState := ⟨⟨⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
          issued, completed⟩, activations⟩
        let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
        NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.ticket owner]) ∧
        CompletionJoint.Valid declarations policy registry ambient
          (ScopedPortJoint.advanceState before after [] [.ticket owner]) result outgoing bound ∧
        Trace (OwnerPhaseTransitions.available (ownedTickets before.execution.configuration.stack)) [owner]
          (OwnerPhaseTransitions.available (ownedTickets after.stack)) ∧
        SharedSourceSegments.Source operations policy contracts tables world .nil outside scope value after.stack
          (OwnerPhaseTransitions.available (ownedTickets after.stack)) afterPhase output
          (contract.resumeDemand ++ remaining) (actual ++ restRow) := by
  obtain ⟨requirements, receiver, savedBefore, savedRow, remaining, restRow, original, covered, names, rows, recheck⟩ :=
    resume_source source known resolved closed
  refine ⟨requirements, receiver, savedBefore, savedRow, remaining, restRow, original, covered, names, rows, ?_⟩
  intro actual checked accepted
  obtain ⟨raw, restored⟩ := recheck actual (by simpa only [OwnerSourceResumption.stack_append_empty] using checked) accepted
  obtain ⟨step, preserved, transition, projection⟩ := OwnerPhaseTransitions.resume_joint valid resolved closed.1 tables
  have phases := OwnerPhaseTransitions.trace_result transition
  change OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) =
    spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner at phases
  exact ⟨step, preserved, transition, phases.symm ▸ restored⟩

end Restoration

theorem invocation_ports
    (current : Owners.Derives operations policy (ResumeSpecialization.sharedView contracts owner actual)
      inside world Environment.empty allowed scope before code middle input currentDemand currentRow)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (pending : SharedSourceSegments.Segment operations policy contracts tables world fixed stack
      middle input after output remaining restRow) :
    ScopedPorts.ConfigurationTyped operations.ports contracts.ports.types world ⟨code, scope, stack⟩ output.port := by
  have typed := Owners.port_typing current (by simpa only [ResumeSpecialization.shared_view_ports] using scopeTyped)
  exact ⟨_, .checked (ScopedPorts.effect_scope_has_types scopeTyped) typed, SharedSourceSegments.segment_ports pending⟩

namespace Examples
open OwnerPhaseTransitions (empty introduce)

def effect : Instance := .user 81 []
def raw : Footprint := [⟨effect, 0, false⟩]
def operations : Operations := fun requested operation =>
  if requested = effect ∧ operation = 0 then some (.unit, .unit) else none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, true⟩
def contract : Owners.Contract := ⟨.unit, .unit, false, [], [], [], none, [effect], []⟩
def contracts : Contracts := fun owner => if owner = 19 then some contract else none
def tables : CallableProtectionFrames.Tables := fun _ => [(0, ⟨false, some [], some []⟩)]
def originalHandler : HandlerData := ⟨1, effect, .cons 0 0 7 (.resume 7 .unit) .nil, .none, .unit, rfl⟩
def originalReceiver : Stack := .push (.handler originalHandler) .nil
def plain : PlainData := ⟨.perform (Instantiation.freezeEffect effect) 0, .none, .unit, .unit, [], rfl⟩
def capture : Stack := .push (.plain plain) .nil
def stack : Stack := .live 19 .unit .unit capture .none .nil
def waiting : Stack := .spent 19 .unit .none .nil
def outside : ProtectionContracts.Context := [.handler effect 2 [(0, ⟨false, some [], some []⟩)]]

theorem operation_known : operations effect 0 = some (.unit, .unit) := by decide
theorem owner_known : contracts 19 = some contract := by decide

theorem captured_at_receiver {records : Contracts}
    (checked : OwnerSource.exportAt (OwnerPhases.ofStack tables receiver) phases raw = some row) :
    SharedSourceSegments.Segment operations policy records tables [] receiver capture
      phases .unit phases .unit [] row := by
  have context : SharedSourceSegments.Context operations policy records (OwnerPhases.ofStack tables receiver)
      [] Environment.empty [effect] .none (.perform (Instantiation.freezeEffect effect) 0)
      phases .unit phases .unit [] row :=
    .perform operation_known List.mem_cons_self
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]) checked
  have frame : SharedSourceSegments.Frame operations policy records (OwnerPhases.ofStack tables receiver)
      [] (.plain plain) phases .unit phases .unit [] row := .plain context .none rfl rfl
  have result := SharedSourceSegments.Segment.push (fixed := receiver) frame SharedSourceSegments.Segment.nil
  simpa only [Stack.append, capture, List.append_nil] using result

theorem captured_historical :
    SharedSourceSegments.Segment operations policy contracts tables [] originalReceiver capture empty .unit empty .unit [] [] :=
  captured_at_receiver (by decide)

theorem captured_current :
    SharedSourceSegments.Segment operations policy contracts tables [] waiting capture empty .unit empty .unit [] raw :=
  captured_at_receiver (by decide)

theorem pending_shared :
    SharedSourceSegments.Segment operations policy contracts tables [] .nil stack empty .unit empty .unit [] [] :=
  .live owner_known rfl rfl ⟨.none, .none⟩ rfl rfl captured_historical (EffectBounds.covers_refl []) .nil

theorem transition : Trace (introduce empty 19) [19] empty := by
  apply Trace.cons (by simp [introduce])
  rw [OwnerCaptureContracts.spend_introduced (by rfl)]
  exact .nil

theorem old_row_does_not_cover : ¬ EffectBounds.Covers contract.resumeRow raw := by
  intro covered
  exact List.not_mem_nil (covered List.mem_cons_self)

theorem new_outside_admits : checkFootprint outside raw = true := by decide
theorem empty_outside_rejects : checkFootprint [] raw = false := by decide

def requirements : PhaseRechecking.Requirements [] := .request [] raw

theorem requirement_reinterpreted :
    requirements.evaluate (OwnerPhases.ofStack tables originalReceiver) empty = some [] ∧
    requirements.evaluate (OwnerPhases.ofStack tables waiting) empty = some raw := by decide

theorem before_source :
    SharedSourceSegments.Source operations policy contracts tables [] .nil outside (.ticket 7 19) (.resume 7 .unit)
      stack (introduce empty 19) empty .unit [19] [] := by
  have operand : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables (stack.append .nil))
      [] Environment.empty [effect] (.ticket 7 19) (introduce empty 19) .unit (introduce empty 19) .unit [] [] :=
    .stable .unit (by simp [OwnerSource.exportAt, residual_empty])
  have current : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables (stack.append .nil))
      [] Environment.empty [effect] (.ticket 7 19) (introduce empty 19) (.resume 7 .unit) empty .unit [19] [] :=
    .resume owner_known rfl rfl operand transition (fun _ member => member)
      (by simp [contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .checked current (.bound (Owners.ports_lookup owner_known)) pending_shared (by decide)

theorem specialized_resume :
    RawStep ⟨.resume 7 .unit, .ticket 7 19, stack⟩ ⟨.unit, .ticket 7 19, capture.append waiting⟩ [] [.ticket 19] ∧
    Owners.Derives operations policy (ResumeSpecialization.sharedView contracts 19 raw)
      (OwnerPhases.ofStack tables (stack.append .nil)) [] Environment.empty [effect] (.ticket 7 19)
      (introduce empty 19) (.resume 7 .unit) empty .unit [19] raw ∧
    SharedSourceSegments.Source operations policy contracts tables [] .nil outside (.ticket 7 19) .unit
      (capture.append waiting) empty empty .unit [] raw := by
  have received : SharedSourceSegments.Segment operations policy contracts tables [] (waiting.append .nil) capture
      (spend (introduce empty 19) 19) .unit empty .unit [] raw := by
    simpa only [OwnerSourceResumption.stack_append_empty, OwnerCaptureContracts.spend_introduced (before := empty) (owner := 19) rfl]
      using captured_current
  have result := resume_from_rechecked (front := Stack.nil) (binder := 7) owner_known (scope := Execution.Scope.ticket 7 19) rfl rfl
    (allowed := [effect]) Summary.unit CallableProtection.Examples.unit_closed
    (.bound (Owners.ports_lookup owner_known)) (fun _ member => member)
    (by simp [contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]) transition pending_shared received
    (by simpa only [List.append_nil] using new_outside_admits)
  simpa only [contract, Stack.append, stack, waiting, List.append_nil,
    OwnerCaptureContracts.spend_introduced (before := empty) (owner := 19) rfl] using result

theorem before_ports : ScopedPorts.ConfigurationTyped operations.ports contracts.ports.types []
    ⟨.resume 7 .unit, .ticket 7 19, stack⟩ .unit :=
  invocation_ports specialized_resume.2.1 (.bound (Owners.ports_lookup owner_known)) pending_shared

theorem after_ports : ScopedPorts.ConfigurationTyped operations.ports contracts.ports.types []
    ⟨.unit, .ticket 7 19, capture.append waiting⟩ .unit :=
  SharedSourceSegments.source_ports specialized_resume.2.2

theorem original_record_retained : contracts 19 = some contract := owner_known

theorem after_history : CaptureAuthentication.Retained operations.protection policy contracts.source tables (capture.append waiting) :=
  SharedSourceSegments.source_authenticated specialized_resume.2.2

end Examples

namespace NestedExamples
open OwnerPhaseTransitions (available empty)
open Ash.OneShot.SharedResumption.Examples (effect raw operations policy tables originalReceiver)

def inner : Owners.Contract := Examples.contract
def outer : Owners.Contract := ⟨.unit, .unit, false, [29], [], [], none, [effect], []⟩
def contracts : Contracts := fun owner => if owner = 19 then some outer else if owner = 29 then some inner else none
def innerCapture : Stack := Examples.capture
def innerBoundary : Stack := .live 29 .unit .unit innerCapture .none .nil
def resumePlain : PlainData := ⟨.resume 8, .ticket 8 29, .unit, .unit, [29], rfl⟩
def outerCapture : Stack := .push (.plain resumePlain) innerBoundary
def outerBoundary : Stack := .live 19 .unit .unit outerCapture .none .nil
def outerWaiting : Stack := .spent 19 .unit .none .nil
def innerWaiting : Stack := .spent 29 .unit .none outerWaiting

theorem inner_known : contracts 29 = some inner := by decide
theorem outer_known : contracts 19 = some outer := by decide

theorem inner_historical : SharedSourceSegments.Segment operations policy contracts tables [] originalReceiver
    innerCapture empty .unit empty .unit [] [] := Examples.captured_at_receiver (by decide)

theorem inner_pending : SharedSourceSegments.Segment operations policy contracts tables [] fixed
    innerBoundary empty .unit empty .unit [] [] :=
  .live inner_known rfl rfl ⟨.none, .none⟩ rfl rfl inner_historical (EffectBounds.covers_refl []) .nil

theorem inner_transition : Trace (available [29]) [29] empty :=
  OwnerPhaseTransitions.trace_all_owned (.refl _) (by decide)

theorem outer_saved : SharedSourceSegments.Segment operations policy contracts tables [] fixed
    outerCapture (available [29]) .unit empty .unit [29] [] := by
  have context : SharedSourceSegments.Context operations policy contracts
      (OwnerPhases.ofStack tables (innerBoundary.append fixed)) [] Environment.empty [effect] (.ticket 8 29) (.resume 8)
      (available [29]) .unit empty .unit [29] [] :=
    .resume inner_known rfl rfl inner_transition (fun _ member => member)
      (by simp [inner, Examples.contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .push (.plain (plain := resumePlain) context (.bound (Owners.ports_lookup inner_known)) rfl rfl) inner_pending

theorem outer_pending : SharedSourceSegments.Segment operations policy contracts tables [] .nil
    outerBoundary empty .unit empty .unit [] [] :=
  .live outer_known rfl rfl ⟨.none, .none⟩ rfl rfl (receiver := originalReceiver) outer_saved (EffectBounds.covers_refl []) .nil

theorem outer_transition : Trace (available [19, 29]) [19, 29] empty :=
  OwnerPhaseTransitions.trace_all_owned (.refl _) (by decide)

theorem after_outer_phase : spend (available [19, 29]) 19 = available [29] := by
  funext owner
  simp only [spend, available, List.mem_cons, List.not_mem_nil, or_false]
  by_cases same : owner = 19
  · subst owner; decide
  · simp [same]

theorem initial_source : SharedSourceSegments.Source operations policy contracts tables [] .nil [] (.ticket 7 19)
    (.resume 7 .unit) outerBoundary (available [19, 29]) empty .unit [19, 29] [] := by
  have operand : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables (outerBoundary.append .nil))
      [] Environment.empty [effect] (.ticket 7 19) (available [19, 29]) .unit (available [19, 29]) .unit [] [] :=
    .stable .unit (by simp [OwnerSource.exportAt, residual_empty])
  have current : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables (outerBoundary.append .nil))
      [] Environment.empty [effect] (.ticket 7 19) (available [19, 29]) (.resume 7 .unit) empty .unit [19, 29] [] :=
    .resume outer_known rfl rfl operand outer_transition (fun _ member => member)
      (by simp [outer, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .checked current (.bound (Owners.ports_lookup outer_known)) outer_pending (by decide)

theorem outer_restoration :
    RawStep ⟨.resume 7 .unit, .ticket 7 19, outerBoundary⟩
      ⟨.unit, .ticket 7 19, outerCapture.append outerWaiting⟩ [] [.ticket 19] ∧
    SharedSourceSegments.Source operations policy contracts tables [] .nil [] (.ticket 7 19) .unit
      (outerCapture.append outerWaiting) (available [29]) empty .unit [29] [] := by
  have received : SharedSourceSegments.Segment operations policy contracts tables [] (outerWaiting.append .nil)
      outerCapture (spend (available [19, 29]) 19) .unit empty .unit [29] [] := after_outer_phase.symm ▸ outer_saved
  obtain ⟨step, invoked, restored⟩ := resume_from_rechecked (front := Stack.nil) (binder := 7) outer_known
    (scope := Execution.Scope.ticket 7 19) rfl rfl (allowed := [effect]) Summary.unit CallableProtection.Examples.unit_closed
    (.bound (Owners.ports_lookup outer_known)) (fun _ member => member)
    (by simp [outer, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]) outer_transition outer_pending received
    (outside := []) (by decide)
  exact ⟨step, after_outer_phase ▸ restored⟩

theorem plug_inner_call :
    RawStep ⟨.unit, .ticket 7 19, outerCapture.append outerWaiting⟩
      ⟨.resume 8 .unit, .ticket 8 29, innerBoundary.append outerWaiting⟩ [] [] :=
  .plug resumePlain .unit CallableProtection.Examples.unit_closed (.ticket 7 19) (innerBoundary.append outerWaiting)

theorem inner_source : SharedSourceSegments.Source operations policy contracts tables [] .nil [] (.ticket 8 29)
    (.resume 8 .unit) (innerBoundary.append outerWaiting) (available [29]) empty .unit [29] [] := by
  have pending : SharedSourceSegments.Segment operations policy contracts tables [] .nil
      (innerBoundary.append outerWaiting) empty .unit empty .unit [] [] :=
    SharedSourceSegments.segment_append inner_pending (.spent outer_known rfl ⟨.none, .none⟩ rfl .nil)
  have operand : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables ((innerBoundary.append outerWaiting).append .nil))
      [] Environment.empty [effect] (.ticket 8 29) (available [29]) .unit (available [29]) .unit [] [] :=
    .stable .unit (by simp [OwnerSource.exportAt, residual_empty])
  have current : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables ((innerBoundary.append outerWaiting).append .nil))
      [] Environment.empty [effect] (.ticket 8 29) (available [29]) (.resume 8 .unit) empty .unit [29] [] :=
    .resume inner_known rfl rfl operand inner_transition (fun _ member => member)
      (by simp [inner, Examples.contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .checked current (.bound (Owners.ports_lookup inner_known)) pending (by decide)

theorem inner_rechecking_exposes_request :
    Examples.requirements.evaluate (OwnerPhases.ofStack tables innerWaiting) empty = some raw ∧
    checkFootprint [] raw = false := by decide

theorem inner_reconstructed : SharedSourceSegments.Segment operations policy contracts tables [] innerWaiting
    innerCapture empty .unit empty .unit [] raw := Examples.captured_at_receiver (by decide)

def outerRequirements : PhaseRechecking.Requirements [29] :=
  .sequence (.consume [29] []) (.spent 29)

theorem outer_check_passes :
    outerRequirements.evaluate (OwnerPhases.ofStack tables outerWaiting) (available [29]) = some [] := by decide

theorem outer_check_reconstructs
    (checked : outerRequirements.evaluate (OwnerPhases.ofStack tables receiver) start = some row) :
    SharedSourceSegments.Segment operations policy contracts tables [] receiver outerCapture
      start .unit (spendAll start [29]) .unit [29] row := by
  obtain ⟨a, b, checkedA, checkedB, rfl⟩ := PhaseRechecking.sequence_split checked
  obtain ⟨transition, rfl⟩ := PhaseRechecking.consume_split checkedA
  obtain ⟨done, rfl⟩ := PhaseRechecking.spent_split checkedB
  have context : SharedSourceSegments.Context operations policy contracts
      (OwnerPhases.ofStack tables (innerBoundary.append receiver)) [] Environment.empty [effect] (.ticket 8 29) (.resume 8)
      start .unit (spendAll start [29]) .unit [29] [] :=
    .resume inner_known rfl rfl transition (fun _ member => member)
      (by simp [inner, Examples.contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  have pending : SharedSourceSegments.Segment operations policy contracts tables [] receiver innerBoundary
      (spendAll start [29]) .unit (spendAll start [29]) .unit [] [] :=
    .live inner_known rfl rfl ⟨.none, .none⟩ rfl done inner_historical (EffectBounds.covers_refl []) .nil
  exact .push (.plain (plain := resumePlain) context (.bound (Owners.ports_lookup inner_known)) rfl rfl) pending

theorem phases_match_runtime :
    OwnerPhaseTransitions.available (ownedTickets outerBoundary) = available [19, 29] ∧
    OwnerPhaseTransitions.available (ownedTickets (outerCapture.append outerWaiting)) = available [29] := by
  constructor <;> rfl

theorem nested_history_does_not_guarantee_future_check :
    CaptureAuthentication.Retained operations.protection policy contracts.source tables outerBoundary ∧
    SharedSourceSegments.Source operations policy contracts tables [] .nil [] (.ticket 7 19)
      (.resume 7 .unit) outerBoundary (available [19, 29]) empty .unit [19, 29] [] ∧
    outerRequirements.evaluate (OwnerPhases.ofStack tables outerWaiting) (available [29]) = some [] ∧
    Examples.requirements.evaluate (OwnerPhases.ofStack tables innerWaiting) empty = some raw ∧
    checkFootprint [] raw = false :=
  ⟨SharedSourceSegments.source_authenticated initial_source, initial_source, outer_check_passes, inner_rechecking_exposes_request⟩

end NestedExamples

end Ash.OneShot.SharedResumption

#print axioms Ash.OneShot.SharedResumption.selected_capture
#print axioms Ash.OneShot.SharedResumption.resume_parts
#print axioms Ash.OneShot.SharedResumption.resume_from_rechecked
#print axioms Ash.OneShot.SharedResumption.resume_requirements
#print axioms Ash.OneShot.SharedResumption.resume_source
#print axioms Ash.OneShot.SharedResumption.resume_joint
#print axioms Ash.OneShot.SharedResumption.invocation_ports
#print axioms Ash.OneShot.SharedResumption.Examples.operation_known
#print axioms Ash.OneShot.SharedResumption.Examples.owner_known
#print axioms Ash.OneShot.SharedResumption.Examples.captured_at_receiver
#print axioms Ash.OneShot.SharedResumption.Examples.captured_historical
#print axioms Ash.OneShot.SharedResumption.Examples.captured_current
#print axioms Ash.OneShot.SharedResumption.Examples.pending_shared
#print axioms Ash.OneShot.SharedResumption.Examples.transition
#print axioms Ash.OneShot.SharedResumption.Examples.old_row_does_not_cover
#print axioms Ash.OneShot.SharedResumption.Examples.new_outside_admits
#print axioms Ash.OneShot.SharedResumption.Examples.empty_outside_rejects
#print axioms Ash.OneShot.SharedResumption.Examples.requirement_reinterpreted
#print axioms Ash.OneShot.SharedResumption.Examples.before_source
#print axioms Ash.OneShot.SharedResumption.Examples.specialized_resume
#print axioms Ash.OneShot.SharedResumption.Examples.before_ports
#print axioms Ash.OneShot.SharedResumption.Examples.after_ports
#print axioms Ash.OneShot.SharedResumption.Examples.original_record_retained
#print axioms Ash.OneShot.SharedResumption.Examples.after_history
#print axioms Ash.OneShot.SharedResumption.NestedExamples.inner_known
#print axioms Ash.OneShot.SharedResumption.NestedExamples.outer_known
#print axioms Ash.OneShot.SharedResumption.NestedExamples.inner_historical
#print axioms Ash.OneShot.SharedResumption.NestedExamples.inner_pending
#print axioms Ash.OneShot.SharedResumption.NestedExamples.inner_transition
#print axioms Ash.OneShot.SharedResumption.NestedExamples.outer_saved
#print axioms Ash.OneShot.SharedResumption.NestedExamples.outer_pending
#print axioms Ash.OneShot.SharedResumption.NestedExamples.outer_transition
#print axioms Ash.OneShot.SharedResumption.NestedExamples.after_outer_phase
#print axioms Ash.OneShot.SharedResumption.NestedExamples.initial_source
#print axioms Ash.OneShot.SharedResumption.NestedExamples.outer_restoration
#print axioms Ash.OneShot.SharedResumption.NestedExamples.plug_inner_call
#print axioms Ash.OneShot.SharedResumption.NestedExamples.inner_source
#print axioms Ash.OneShot.SharedResumption.NestedExamples.inner_rechecking_exposes_request
#print axioms Ash.OneShot.SharedResumption.NestedExamples.inner_reconstructed
#print axioms Ash.OneShot.SharedResumption.NestedExamples.outer_check_passes
#print axioms Ash.OneShot.SharedResumption.NestedExamples.outer_check_reconstructs
#print axioms Ash.OneShot.SharedResumption.NestedExamples.phases_match_runtime
#print axioms Ash.OneShot.SharedResumption.NestedExamples.nested_history_does_not_guarantee_future_check
