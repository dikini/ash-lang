import DeclaredSourceCapture

/-! Derive actual request-capture inputs from one hereditary checked state.
Payload typing, clause selection, capabilities and the offered effect export
are recovered from that state. Actual closing compatibility and its budget
remain finite local obligations; no future execution is assumed. -/
namespace Ash.OneShot.DeclaredSourceRequests
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSources (Expression)
open DeclaredSourceStates (CheckedState)
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available spendAll)

/-- Retain the hereditary value witness while reusing existing empty-demand
and value-row results. This is constructor inversion, not a new induction. -/
theorem request_operand
    (source : Expression operations policy contracts world allowed scope environment
      (.perform (Instantiation.freezeEffect requested) operation operand) result demand requirements)
    (isValue : operand.IsValue) :
    ∃ argument, operations requested operation = some (argument, result) ∧
      DeclaredSourceValues.ValueSummary operations policy contracts world environment allowed operand argument ∧
      demand = [] := by
  generalize encoded : Instantiation.freezeEffect requested = effect at source
  cases source with
  | stable summary => cases summary with
    | perform known admitted operand formed =>
        cases freeze_effect_injective encoded
        exact ⟨_, known, DeclaredSourceValues.from_legacy (CoherentSourceTypes.value_row operand isValue ▸ operand), rfl⟩
  | callable summary => cases summary with
    | summaryPerform known admitted operand formed =>
        cases freeze_effect_injective encoded
        have empty := CallableSources.value_row operand.to_generic isValue
        rw [empty] at operand
        exact ⟨_, known, operand, rfl⟩
  | perform known admitted operand formed =>
      cases freeze_effect_injective encoded
      exact ⟨_, known, DeclaredSourceValues.value_summary operand isValue,
        SourceTemplates.expression_value_demand (DeclaredSources.expression_erase operand) isValue⟩

/-- Decompose one checked request once for both capture paths. Every witness
comes from its current source derivation or the actual selected handler cut. -/
theorem request_parts
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue) :
    ∃ (input argument : Value) (payloadAllowed : List Instance) (requirements : Requirements demand)
      (records disposals : RecursiveRequirements.Store) (parameter binder : Nat) (body : Code)
      (offered : ClauseContract) (offeredRow requestRow pendingRow : Footprint),
      operations requested operation = some (argument, input) ∧
      DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument ∧
      ClosedValue operand ∧
      DeclaredSourceFrames.Segment operations policy contracts tables world whole input output demand requirements records ∧
      DeclaredSourceClosing.Records operations policy contracts tables world whole disposals ∧
      Checked (records ++ disposals) [] (available (ownedTickets whole)) requirements pendingRow ∧
      (ownedTickets whole).Nodup ∧
      ClauseAt operation handler.clauses parameter binder body ∧ ClausesUse policy handler.clauses ∧
      lookup operation (tables handler) = some offered ∧
      modeCheck offered.dispose (ProtectionContexts.protectedMode capture.erase) = true ∧
      offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow ∧
      residualize (CallableProtectionFrames.contextOf tables tail) offeredRow = some requestRow ∧
      checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) offeredRow = true ∧
      checkFootprint outside pendingRow = true ∧ row = requestRow ++ pendingRow := by
  cases source with
  | checked configuration closing unique evaluated accepted => cases configuration with
    | checked current scopeTyped pending =>
      obtain ⟨argument, operationKnown, payload, rfl⟩ := request_operand current isValue
      have closed : ClosedValue operand :=
        ScopedPorts.typed_value_closed ((DeclaredSourceValues.erase payload).ports .none) isValue
      obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, sameRow⟩ :=
        RecursiveRequirements.checked_sequence_parts evaluated
      have requestExport := RecursiveRequirements.checked_complete
        (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
      rw [RecursiveDispatch.request_evaluation (DeclaredSources.expression_erase current) isValue] at requestExport
      simp only [List.append_nil, OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] at requestExport
      obtain ⟨offered, offeredRow, found, mode, availableRow, exported⟩ :=
        RecursiveDispatch.cut_residual cut requestExport
      simp only [Bool.false_or] at mode availableRow
      have currentAccepted : checkFootprint outside currentRow = true := by
        rw [sameRow] at accepted
        exact checked_footprint_subset accepted (List.subset_append_left _ _)
      have pendingAccepted : checkFootprint outside pendingRow = true := by
        rw [sameRow] at accepted
        exact checked_footprint_subset accepted (List.subset_append_right _ _)
      have offeredAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) offeredRow = true :=
        residual_admitted_iff.mpr ⟨currentRow, exported, currentAccepted⟩
      obtain ⟨answer, capDemand, tailDemand, capRequirements, tailRequirements, capRecords, tailRecords,
        annotation, selected, saved, surviving, sameDemand, sameRecords, evaluation⟩ :=
        RecursiveCapture.capture_segments_with_frames cut pending
      cases selected with
      | handler typed annotation declarations capabilities modes =>
        have portKnown := port_lookup operationKnown
        rw [← ScopedTyping.handler_cut_instance cut] at portKnown
        have covered : operation ∈ ScopedTyping.clauseKeys handler.clauses := by
          cases typed with
          | handler scopeKnown clauses coverage distinct => exact coverage _ _ _ portKnown
        obtain ⟨parameter, binder, body, clause⟩ := ScopedTyping.clause_at_of_key covered
        exact ⟨_, argument, _, _, _, _, parameter, binder, body, offered, offeredRow,
          currentRow, pendingRow, operationKnown, payload, closed, pending, closing,
          pendingCheck, unique, clause, capabilities, found, mode, availableRow, exported,
          offeredAccepted, pendingAccepted, sameRow⟩

/-- The current source state supplies all request, payload and declaration
premises of the established capture theorem. The remaining implication checks
the closing row against the actual newly allocated continuation budget. -/
theorem capture_from_checked_request
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (closingBound : EffectBounds.Covers upperClosing raw)
    (closingAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) upperClosing = true) :
    ∃ (contract : Owners.Contract) (requestRow closingRow : Footprint),
      contract.closeRow = some closingRow ∧
      residualize (CallableProtectionFrames.contextOf tables tail) raw = some closingRow ∧
      requestRow ⊆ row ∧
      ∀ (_ : closingRow ⊆ requestRow ++ contract.resumeRow),
        ∃ (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
          RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
          CheckedState operations policy (contracts.insert owner contract) tables world outside
            after.scope after.expression after.stack output nextDemand nextRow ∧
          nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
          ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨input, argument, payloadAllowed, requirements, records, disposals, parameter, binder, body,
    offered, offeredRow, currentRow, pendingRow, operationKnown, payload, closed, pending, closing,
    pendingCheck, unique, clause, capabilities, found, mode, availableRow, exported, offeredAccepted,
    pendingAccepted, sameRow⟩ := request_parts source cut isValue
  obtain ⟨contract, allowed, clauseDemand, clauseRequirements, store, remainingDemand, tailRow,
    closingRow, requestRow, requestExport, inputSame, closeRowSame, closingExport, closingAllowed,
    balance, clauseSource, resumeCheck, disposeCheck, finish⟩ :=
    DeclaredSourceCapture.capture_from_declaration cut pending closing pendingCheck unique fresh clause capabilities
      operationKnown payload closed found availableRow offeredAccepted pendingAccepted
      built internal template closingBound closingAccepted
  have requestSame : requestRow = currentRow := Option.some.inj (requestExport.symm.trans exported)
  subst requestRow
  refine ⟨contract, currentRow, closingRow, closeRowSame, closingExport, ?_, ?_⟩
  · rw [sameRow]
    exact List.subset_append_left _ _
  · intro closingWithinBudget
    obtain ⟨clauseRow, step, checked, demandBalance, rowBound, owners⟩ := finish closingWithinBudget
    exact ⟨_, _, _, step, checked, by simpa only [List.nil_append] using demandBalance,
      by simpa only [sameRow] using rowBound, owners⟩

/-- A successful structural disposal check chooses the actual source closing
plan and removes the independent plan, internal-use and callback-typing
premises. Only its outward effect check and combined budget remain to supply. -/
theorem capture_from_checked_disposal
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (disposal : ClosingAdmission.checkedDisposal capture.erase tail.erase = some erasedPlan) :
    ∃ plan raw, ∃ closingRequirements : Requirements (OwnerClosingSource.retirements plan),
      makePlan capture = some plan ∧
      Discardable capture.erase tail.erase (plan.map CloseEntry.erase) ∧
      InternalUses capture.erase.liveTickets capture.erase.pending ∧
      DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements ∧
      (OwnerClosingSource.retirements plan).Perm (ownedTickets capture) ∧
      ∀ (_ : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) raw = true),
        ∃ (contract : Owners.Contract) (requestRow closingRow : Footprint),
          contract.closeRow = some closingRow ∧
          residualize (CallableProtectionFrames.contextOf tables tail) raw = some closingRow ∧
          requestRow ⊆ row ∧
          ∀ (_ : closingRow ⊆ requestRow ++ contract.resumeRow),
            ∃ (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
              RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
              CheckedState operations policy (contracts.insert owner contract) tables world outside
                after.scope after.expression after.stack output nextDemand nextRow ∧
              nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
              ownedTickets after.stack = owner :: ownedTickets whole := by
  have prepared : ∃ plan raw, ∃ closingRequirements : Requirements (OwnerClosingSource.retirements plan),
      makePlan capture = some plan ∧
      Discardable capture.erase tail.erase (plan.map CloseEntry.erase) ∧
      InternalUses capture.erase.liveTickets capture.erase.pending ∧
      DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements ∧
      (OwnerClosingSource.retirements plan).Perm (ownedTickets capture) := by
    cases source with
    | checked configuration closing unique evaluated accepted => cases configuration with
      | checked current scopeTyped pending =>
        obtain ⟨answer, capDemand, tailDemand, capRequirements, tailRequirements, capRecords, tailRecords,
          annotation, selected, saved, surviving, sameDemand, sameRecords, evaluation⟩ :=
          RecursiveCapture.capture_segments_with_frames cut pending
        obtain ⟨plan, raw, closingRequirements, built, safe, internal, template, owners, unprotected⟩ :=
          DeclaredSourceClosing.checked_disposal_template saved disposal
        exact ⟨plan, raw, closingRequirements, built, safe, internal, template, owners⟩
  obtain ⟨plan, raw, closingRequirements, built, safe, internal, template, owners⟩ := prepared
  refine ⟨plan, raw, closingRequirements, built, safe, internal, template, owners, ?_⟩
  intro accepted
  exact capture_from_checked_request source cut isValue fresh built internal template (List.Subset.refl _) accepted

/-- The unavailable-disposal path reuses the same request decomposition and
existing capture theorem. The selected offer is checked to deny disposal. -/
theorem capture_without_disposal_from_checked_request_with_input
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (unavailable : makePlan capture = none ∨ ¬ InternalUses capture.erase.liveTickets capture.erase.pending)
    (noDispose : (lookup operation (tables handler)).map ClauseContract.dispose = some false) :
    ∃ (contract : Owners.Contract) (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      (∃ argument, operations requested operation = some (argument, contract.input)) ∧
      contract.closeRow = none ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨input, argument, payloadAllowed, requirements, records, disposals, parameter, binder, body,
    offered, offeredRow, currentRow, pendingRow, operationKnown, payload, closed, pending, closing,
    pendingCheck, unique, clause, capabilities, found, mode, availableRow, exported, offeredAccepted,
    pendingAccepted, sameRow⟩ := request_parts source cut isValue
  have denied : offered.dispose = false := by simpa only [found, Option.map_some, Option.some.injEq] using noDispose
  obtain ⟨contract, allowed, clauseDemand, clauseRequirements, store, remainingDemand, tailRow,
    requestRow, requestExport, inputSame, closeRowSame, balance, clauseSource, resumeCheck, impossible,
    clauseRow, step, checked, demandBalance, rowBound, owners⟩ :=
    DeclaredSourceCapture.capture_without_disposal_from_declaration cut pending closing pendingCheck unique fresh clause capabilities
      operationKnown payload closed found availableRow offeredAccepted pendingAccepted unavailable denied
  have requestSame : requestRow = currentRow := Option.some.inj (requestExport.symm.trans exported)
  subst requestRow
  exact ⟨contract, _, _, _, ⟨argument, by simpa only [inputSame] using operationKnown⟩, closeRowSame, step, checked, demandBalance,
    by simpa only [sameRow] using rowBound, owners⟩

theorem capture_without_disposal_from_checked_request
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (unavailable : makePlan capture = none ∨ ¬ InternalUses capture.erase.liveTickets capture.erase.pending)
    (noDispose : (lookup operation (tables handler)).map ClauseContract.dispose = some false) :
    ∃ (contract : Owners.Contract) (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      contract.closeRow = none ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨contract, after, nextDemand, nextRow, inputKnown, rest⟩ :=
    capture_without_disposal_from_checked_request_with_input source cut isValue fresh unavailable noDispose
  exact ⟨contract, after, nextDemand, nextRow, rest⟩

/-- Protection itself supplies both unavailable closing and the selected
handler's denial of disposal. No independent mode certificate is requested. -/
theorem capture_protected_request
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (held : ProtectionContexts.protectedMode capture.erase = true) :
    ∃ (contract : Owners.Contract) (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      contract.closeRow = none ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  have blocked : makePlan capture = none := by
    have classified := CaptureInterfaces.plan_available capture
    simpa [held] using classified
  obtain ⟨input, argument, payloadAllowed, requirements, records, disposals, parameter, binder, body,
    offered, offeredRow, currentRow, pendingRow, operationKnown, payload, closed, pending, closing,
    pendingCheck, unique, clause, capabilities, found, mode, availableRow, exported, offeredAccepted,
    pendingAccepted, sameRow⟩ := request_parts source cut isValue
  have denied : offered.dispose = false := mode_check_iff.mp mode held
  apply capture_without_disposal_from_checked_request source cut isValue fresh (Or.inl blocked)
  simp only [found, Option.map_some, denied]

/-- Reuse the existing exact plan/protection classification in the other
direction: failed raw plan construction needs no new admission hypothesis. -/
theorem capture_unclosable_request
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (blocked : makePlan capture = none) :
    ∃ (contract : Owners.Contract) (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      contract.closeRow = none ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  apply capture_protected_request source cut isValue fresh
  have classified := CaptureInterfaces.plan_available capture
  simpa [blocked] using classified.symm

end Ash.OneShot.DeclaredSourceRequests

#print axioms Ash.OneShot.DeclaredSourceRequests.request_operand
#print axioms Ash.OneShot.DeclaredSourceRequests.request_parts
#print axioms Ash.OneShot.DeclaredSourceRequests.capture_from_checked_request
#print axioms Ash.OneShot.DeclaredSourceRequests.capture_from_checked_disposal
#print axioms Ash.OneShot.DeclaredSourceRequests.capture_without_disposal_from_checked_request
#print axioms Ash.OneShot.DeclaredSourceRequests.capture_protected_request
#print axioms Ash.OneShot.DeclaredSourceRequests.capture_unclosable_request

#print axioms Ash.OneShot.DeclaredSourceRequests.capture_without_disposal_from_checked_request_with_input
