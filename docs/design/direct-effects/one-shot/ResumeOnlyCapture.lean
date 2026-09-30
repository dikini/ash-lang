import DeclaredSourceRequests
import ClosingBudgetGap

/-! A selected clause that denies disposal does not require a successful
closing check. A raw plan may exist without being safe to execute. Existing
allocation retains its source records, while the new contract offers no
disposal row. No operational rule or continuation mode is added. -/
namespace Ash.OneShot.ResumeOnlyCapture
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSourceFrames (Segment)
open DeclaredSourceStates (CheckedState)
open RecursiveRequirements (Requirements Checked Store)

/-- Reuse plan-bearing allocation with an absent disposal offer, then use
the selected declaration's existing row certificate and completion proof.
There is deliberately no closing compatibility, export or budget premise. -/
theorem capture_with_raw_plan_input
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (closing : DeclaredSourceClosing.Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (capabilities : ClausesUse policy handler.clauses)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (found : lookup operation (tables handler) = some offered)
    (availableRow : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (offeredAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) offeredRow = true)
    (pendingAccepted : checkFootprint outside row = true)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (noDispose : offered.dispose = false) :
    ∃ (contract : Owners.Contract) (requestRow : Footprint) (after : Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
      residualize (CallableProtectionFrames.contextOf tables tail) offeredRow = some requestRow ∧
      contract.input = input ∧ contract.closeRow = none ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ requestRow ++ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨requestRow, requestExport, requestAccepted⟩ := residual_admitted_iff.mp offeredAccepted
  have accepted : checkFootprint outside (requestRow ++ row) = true := by
    rw [check_footprint_append, requestAccepted, pendingAccepted]; rfl
  obtain ⟨contract, allowed, clauseDemand, clauseRequirements, capReq, tailDemand, tailReq, tailRow,
    inputSame, closeDemandSame, closeRowSame, balance, heldSame, clauseSource, clauseRows, boundary, closingAfter,
    demandSame, rowSame, capCheck, tailCheck, afterUnique⟩ :=
    DeclaredSourceAllocation.allocate_selected_clause cut source closing checked unique fresh clause operationKnown
      found availableRow built internal template none
  let store : Store := (⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) ::
    (records ++ ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals))
  let initial := OwnerPhaseTransitions.available (ownedTickets
    (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
  have phases := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.port)
    cut (RecursiveCapture.fresh_unowned source.erase fresh)
  have resumeCheck := RecursiveClauses.fresh_resume_check capCheck phases
  have interface : ClauseRowAdmission.Interface owner contract offered.dispose store (OwnerPhases.ofStack tables tail) initial requestRow := by
    apply ClauseRowAdmission.Interface.of_resume _ noDispose (OwnerPhaseTransitions.capture_tail_fresh cut (RecursiveCapture.fresh_unowned source.erase fresh))
    simpa only [OwnerPhases.ofStack, heldSame] using resumeCheck
  have exported : OwnerSource.exportAt (OwnerPhases.ofStack tables tail) initial offeredRow = some requestRow := by
    rw [OwnerSource.exportAt, OwnerPhaseTransitions.project_agrees, OwnerPhases.project_stack]
    · exact requestExport
    · intro nested member
      rw [OwnerPhaseTransitions.liveNames_stack] at member
      simp [initial, OwnerPhaseTransitions.available, ownedTickets, active_tickets_owned tail member]
  obtain ⟨clauseRow, clauseChecked, covered⟩ := ClauseRowAdmission.Rows.instantiate clauseRows interface exported
      (ClauseRowAdmission.SourceStore.of_source boundary.erase (DeclaredSourceClosing.records_erase closingAfter) (by simp [Owners.Contracts.insert]))
  have clauseCheck : Checked store
      (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
      initial clauseRequirements clauseRow := by
    simpa only [OwnerPhases.ofStack, heldSame] using clauseChecked
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have payloadAfter := DeclaredSourceValues.extension (DeclaredSourceValues.change_allowed payload closed.1 allowed)
    (Owners.insert_extends (contract := contract) contracts fresh)
  have current := DeclaredSourceSubstitution.substitution clauseSource payloadAfter closed
  have completed := RecursiveClauseUsage.declared_clause_completed clause capabilities
    (DeclaredSources.expression_erase clauseSource) clauseCheck
  have included : (clauseRow ++ tailRow) ⊆ (requestRow ++ row) := by
    rw [rowSame, ← List.append_assoc]
    exact ScopedExpressions.append_subset covered (List.Subset.refl _)
  have result := DeclaredSourceCapture.fresh_clause_configuration known boundary closingAfter capCheck tailCheck
    phases afterUnique current clauseCheck balance completed (checked_footprint_subset accepted included)
  have ready : ClosedExcept parameter body := by
    obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut (SourceTemplates.segment_ports source.erase)
    cases handlerTyped with
    | handler scopeKnown clauses coverage unique =>
        obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed clause clauses
        exact ScopedPorts.typed_suffix_ready bodyTyped
  exact ⟨contract, requestRow, _, _, _, requestExport, inputSame, closeRowSame,
    RawStep.capture requested operation parameter binder owner operand body scope whole capture tail handler
      (ScopedPorts.embedPort input.port) cut clause closed ready, result.1,
    by simpa only [demandSame, List.cons_append] using result.2,
    included, RecursiveCapture.capture_owned cut⟩

theorem capture_with_raw_plan
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (closing : DeclaredSourceClosing.Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (capabilities : ClausesUse policy handler.clauses)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (found : lookup operation (tables handler) = some offered)
    (availableRow : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (offeredAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) offeredRow = true)
    (pendingAccepted : checkFootprint outside row = true)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (noDispose : offered.dispose = false) :
    ∃ (contract : Owners.Contract) (requestRow : Footprint) (after : Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
      residualize (CallableProtectionFrames.contextOf tables tail) offeredRow = some requestRow ∧
      contract.closeRow = none ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ requestRow ++ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨contract, requestRow, after, nextDemand, nextRow, exported, inputSame, rest⟩ :=
    capture_with_raw_plan_input cut source closing checked unique fresh clause capabilities operationKnown
      payload closed found availableRow offeredAccepted pendingAccepted built internal template noDispose
  exact ⟨contract, requestRow, after, nextDemand, nextRow, exported, rest⟩

/-- Cover every selected non-disposing capture: no plan, outside ownership,
or a raw plan whose closing admission may fail. All branch constructions reuse
existing allocation, source substitution and ownership accounting. -/
theorem capture_from_checked_request_with_input
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (noDispose : (lookup operation (tables handler)).map ClauseContract.dispose = some false) :
    ∃ (contract : Owners.Contract) (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      (∃ argument, operations requested operation = some (argument, contract.input)) ∧
      contract.closeRow = none ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  classical
  cases built : makePlan capture with
  | none =>
      exact DeclaredSourceRequests.capture_without_disposal_from_checked_request_with_input
        source cut isValue fresh (Or.inl built) noDispose
  | some plan =>
      by_cases internal : InternalUses capture.erase.liveTickets capture.erase.pending
      · obtain ⟨input, argument, payloadAllowed, requirements, records, disposals, parameter, binder, body,
          offered, offeredRow, requestRow, pendingRow, operationKnown, payload, closed, pending, closing,
          pendingCheck, unique, clause, capabilities, found, mode, availableRow, exported, offeredAccepted,
          pendingAccepted, sameRow⟩ := DeclaredSourceRequests.request_parts source cut isValue
        have denied : offered.dispose = false := by simpa only [found, Option.map_some, Option.some.injEq] using noDispose
        obtain ⟨answer, capDemand, tailDemand, capRequirements, tailRequirements, capRecords, tailRecords,
          annotation, selected, saved, surviving, sameDemand, sameRecords, evaluation⟩ :=
          RecursiveCapture.capture_segments_with_frames cut pending
        obtain ⟨raw, closingRequirements, template⟩ :=
          DeclaredSourceClosing.contents_template (tables := tables) (scope := .none)
            (DeclaredSourceClosing.plan_contents saved built)
        obtain ⟨contract, actualRequestRow, after, nextDemand, nextRow, actualExport, inputSame, closeNone, step, next,
          balanced, bounded, owners⟩ := capture_with_raw_plan_input cut pending closing pendingCheck unique fresh clause capabilities
            operationKnown payload closed found availableRow offeredAccepted pendingAccepted built internal template denied
        have same := Option.some.inj (actualExport.symm.trans exported)
        subst actualRequestRow
        exact ⟨contract, after, nextDemand, nextRow, ⟨argument, by simpa only [inputSame] using operationKnown⟩, closeNone, step, next, balanced, sameRow ▸ bounded, owners⟩
      · exact DeclaredSourceRequests.capture_without_disposal_from_checked_request_with_input
          source cut isValue fresh (Or.inr internal) noDispose

theorem capture_from_checked_request
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (noDispose : (lookup operation (tables handler)).map ClauseContract.dispose = some false) :
    ∃ (contract : Owners.Contract) (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      contract.closeRow = none ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨contract, after, nextDemand, nextRow, inputKnown, rest⟩ :=
    capture_from_checked_request_with_input source cut isValue fresh noDispose
  exact ⟨contract, after, nextDemand, nextRow, rest⟩

namespace Examples
open SourceCallableExamples (operations policy effect operation_known)
open ClosingBudgetGap (contracts)

def callbackEffect : Instance := .user 192 []
def callback : Code := .lambda 0 .unit

theorem callback_source : Summary operations [] Environment.empty [] callback
    (.function .unit .unit [callbackEffect] []) [] := by
  exact .lambda .unit (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources,
    callbackEffect, Instance.resources])

def action : ActionData := ⟨102, callback,
  ScopedPorts.typed_value_closed (CoherentSourceTypes.port_typing callback_source .none) trivial,
  .none, .unit, [callbackEffect]⟩
def localHandler : HandlerData := ⟨103, callbackEffect, .nil, .none, .unit, rfl⟩
def handler : HandlerData := ClosingBudgetGap.shadow
def tables : CallableProtectionFrames.Tables := fun data =>
  if data.activation = handler.activation then SourceCallableExamples.table else []
def outer : Stack := .push (.handler handler) .nil
def middle : Stack := .push (.handler localHandler) outer
def whole : Stack := .push (.armed action) middle
def plan : List CloseEntry := [.invoke action]
def empty : Requirements [] := .request [] []
def outerRequirements : Requirements [] := .sequence (empty.prepend []) empty
def middleRequirements : Requirements [] :=
  .sequence (empty.prepend (OwnerPhases.ofStack tables outer)) outerRequirements
def wholeRequirements : Requirements [] :=
  .sequence (empty.prepend (OwnerPhases.ofStack tables middle)) middleRequirements
def request : Code := .perform (Instantiation.freezeEffect effect) 0 .unit

theorem local_handler_typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types [] (.handler localHandler) := by
  refine .handler (residual := []) ⟨.none, .none⟩ .nil ?_ (by decide)
  intro operation input output known
  have impossible : operations.ports localHandler.effectInst operation = none := by
    simp [Operations.ports, operations, localHandler, callbackEffect, effect]
  rw [impossible] at known
  cases known

theorem pending_source : Segment operations policy contracts tables [] whole .unit .unit [] wholeRequirements [] := by
  have outerSource : Segment operations policy contracts tables [] outer .unit .unit [] outerRequirements [] :=
    DeclaredSourceFrames.push
      (.handler (tables := tables) ClosingBudgetGap.shadow_typed rfl
        (DeclaredSources.Examples.declaration contracts Environment.empty)
        (.cons (.resume rfl .unit) .nil) (.cons (by decide) .nil)) .nil
  have middleSource : Segment operations policy contracts tables [] middle .unit .unit [] middleRequirements [] :=
    DeclaredSourceFrames.push (.handler (tables := tables) (allowed := []) local_handler_typed rfl .nil .nil .nil) outerSource
  exact DeclaredSourceFrames.push
    (.armed (action := action) ⟨.none, .none⟩ (DeclaredSourceValues.from_legacy callback_source) rfl) middleSource

theorem checked_request : CheckedState operations policy contracts tables [] [] .none request whole .unit [] [] := by
  have current : DeclaredSources.Expression operations policy contracts [] [effect] .none Environment.empty request .unit []
      (.emitAfter empty [] [⟨effect, 0, false⟩]) :=
    .perform operation_known List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .checked (.checked current .none pending_source) (.push (.push (.push .nil)))
    (by decide) (RecursiveRequirements.evaluate_sound (by
      simp only [wholeRequirements, middleRequirements, outerRequirements, empty,
        Requirements.prepend, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel]
      decide)) (by rfl)

/-- A raw plan exists, but removing the local provider fails the structural
request-preservation check for the callback's conservative declared requests. -/
theorem closing_rejected : makePlan whole = some plan ∧
    ClosingAdmission.checkedDisposal whole.erase Stack.nil.erase = none := by
  exact ⟨rfl, by decide⟩

/-- This is a checked source request, not merely a raw control example. Its
selected clause promises resumption and needs no permission to run that plan. -/
theorem resume_only_progress :
    ∃ (contract : Owners.Contract) (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      contract.closeRow = none ∧
      RawStep ⟨request, .none, whole⟩ after [.ticket 20] [] ∧
      CheckedState operations policy (contracts.insert 20 contract) tables [] []
        after.scope after.expression after.stack .unit nextDemand nextRow ∧
      nextDemand.Perm [20] ∧ nextRow ⊆ [] ∧ ownedTickets after.stack = [20] := by
  have cut : HandlerCut effect whole whole .nil handler :=
    .push _ _ _ _ _ (by decide) (.push _ _ _ _ _ (by decide) (.hit handler .nil rfl))
  exact capture_from_checked_request checked_request cut trivial (by decide) (by decide)

end Examples
end Ash.OneShot.ResumeOnlyCapture

#print axioms Ash.OneShot.ResumeOnlyCapture.capture_with_raw_plan
#print axioms Ash.OneShot.ResumeOnlyCapture.capture_from_checked_request
#print axioms Ash.OneShot.ResumeOnlyCapture.Examples.callback_source
#print axioms Ash.OneShot.ResumeOnlyCapture.Examples.local_handler_typed
#print axioms Ash.OneShot.ResumeOnlyCapture.Examples.pending_source
#print axioms Ash.OneShot.ResumeOnlyCapture.Examples.checked_request
#print axioms Ash.OneShot.ResumeOnlyCapture.Examples.closing_rejected
#print axioms Ash.OneShot.ResumeOnlyCapture.Examples.resume_only_progress

#print axioms Ash.OneShot.ResumeOnlyCapture.capture_with_raw_plan_input
#print axioms Ash.OneShot.ResumeOnlyCapture.capture_from_checked_request_with_input
