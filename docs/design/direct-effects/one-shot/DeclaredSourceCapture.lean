import DeclaredSourceAllocation
import DeclaredSourceStates

/-! Capture retains hereditary clause, frame and closing-record evidence.
Actual clause checking is derived from the row schema retained by the selected
declaration. Closing-plan and unavailable-disposal compatibility remain explicit. The
existing clause completion and ownership-balance lemmas are reused. -/
namespace Ash.OneShot.DeclaredSourceCapture
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSources (Expression)
open DeclaredSourceFrames (Segment)
open DeclaredSourceClosing (Records)
open DeclaredSourceStates (CheckedState)
open DeclaredSourceAllocation (allocate_selected_clause allocate_selected_without_disposal)
open RecursiveRequirements (Requirements Checked Key Store)
open OwnerPhaseTransitions (Phases available spend spendAll)

theorem checked_clause_configuration
    (known : contracts owner = some contract)
    (source : Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (closing : Records operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) disposals)
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : spend (available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (current : Expression operations policy contracts world allowed (.ticket binder owner)
      Environment.empty code contract.answer clauseDemand clauseRequirements)
    (currentCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail))
      (available (ownedTickets (.live owner inputType answerType capture caller tail)))
      clauseRequirements clauseRow)
    (sameDemand : clauseDemand.Perm (owner :: contract.resumeDemand))
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    CheckedState operations policy contracts tables world outside (.ticket binder owner)
      code (.live owner inputType answerType capture caller tail) output
      (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
    (clauseDemand ++ tailDemand).Perm ((owner :: contract.resumeDemand) ++ tailDemand) := by
  let initial := available (ownedTickets (.live owner inputType answerType capture caller tail))
  change spend initial owner = before at phases
  have consumed : before owner = .consumed := phases ▸ OwnerPhaseTransitions.spend_self initial owner
  have afterOwner : spendAll before contract.resumeDemand owner = .consumed :=
    OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedCheck) consumed
  have pending : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (spendAll initial clauseDemand) (.sequence (.spent owner) tailRequirements) tailRow := by
    rw [PhaseRechecking.spendAll_permutation sameDemand]
    simpa only [spendAll, phases, List.nil_append] using
      (Checked.sequence (Checked.spent (store := ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)))
        (receiving := []) afterOwner) tailCheck)
  exact ⟨.checked (.checked current (.bound (Owners.ports_lookup known)) source) closing unique
    (.sequence (RecursiveRequirements.checked_prepend_iff.mpr
      (by simpa only [List.append_nil, List.cons_append] using currentCheck)) pending) accepted,
    sameDemand.append_right _⟩

theorem fresh_clause_configuration
    (known : contracts owner = some contract)
    (source : Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (closing : Records operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) disposals)
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : spend (available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (current : Expression operations policy contracts world allowed (.ticket binder owner)
      Environment.empty code contract.answer clauseDemand clauseRequirements)
    (currentCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail))
      (available (ownedTickets (.live owner inputType answerType capture caller tail)))
      clauseRequirements clauseRow)
    (balance : contract.closeDemand.Perm contract.resumeDemand)
    (completed : spendAll (available (ownedTickets (.live owner inputType answerType capture caller tail)))
      clauseDemand owner = .consumed)
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    CheckedState operations policy contracts tables world outside (.ticket binder owner)
      code (.live owner inputType answerType capture caller tail) output
      (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
    (clauseDemand ++ tailDemand).Perm ((owner :: contract.resumeDemand) ++ tailDemand) := by
  have sameDemand := RecursiveClauseOwnership.consuming_clause_balance (DeclaredSources.expression_erase current) known currentCheck
    (by simp [available, ownedTickets]) completed balance
  exact checked_clause_configuration known source closing savedCheck tailCheck phases unique
    current currentCheck sameDemand accepted

/-- Assemble capture from the supplied checked source cut and retain its
resumption row. The legacy entry point below only chooses the cut evidence. -/
theorem capture_from_declaration_split
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (closing : Records operations policy contracts tables world whole disposals)
    (cutAnnotation : answer.port = ScopedPorts.eraseType handler.answer)
    (selected : DeclaredSourceFrames.Frame operations policy contracts tables world
      (.handler handler) answer answer [] (.request [] []))
    (saved : Segment operations policy contracts tables world capture input answer capDemand savedRequirements capRecords)
    (surviving : Segment operations policy contracts tables world tail answer output remainingDemand remainingRequirements tailRecords)
    (cutDemand : demand = capDemand ++ remainingDemand) (cutRecords : records = capRecords ++ tailRecords)
    (cutRow : row = capRow ++ remainingRow)
    (savedChecked : Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
      (OwnerPhaseTransitions.available (ownedTickets whole)) savedRequirements capRow)
    (remainingChecked : Checked (records ++ disposals) []
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) remainingRequirements remainingRow)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (capabilities : ClausesUse policy handler.clauses)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (offeredAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) offeredRow = true)
    (pendingAccepted : checkFootprint outside row = true)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (closingBound : EffectBounds.Covers upperClosing raw)
    (closingAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) upperClosing = true) :
    ∃ (contract : Owners.Contract) (allowed : List Instance) (clauseDemand : List Nat)
      (clauseRequirements : Requirements clauseDemand) (store : Store) (tailDemand : List Nat) (tailRow closingRow requestRow : Footprint),
      contract.resumeRow = capRow ∧
      ProtectionResiduals.residualize (CallableProtectionFrames.contextOf tables tail) offeredRow = some requestRow ∧
      contract.input = input ∧ contract.closeRow = some closingRow ∧
      ProtectionResiduals.residualize (CallableProtectionFrames.contextOf tables tail) raw = some closingRow ∧
      checkFootprint outside closingRow = true ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) closingRow ∧
      ∀ (_ : closingRow ⊆ requestRow ++ contract.resumeRow),
        ∃ clauseRow,
          RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
            ⟨body.subst parameter operand, .ticket binder owner,
              .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
          CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
            (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
            output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
          (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
          (clauseRow ++ tailRow) ⊆ (requestRow ++ row) ∧
          ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  obtain ⟨requestRow, requestExport, requestAccepted⟩ := ProtectionResiduals.residual_admitted_iff.mp offeredAccepted
  have accepted : checkFootprint outside (requestRow ++ row) = true := by
    rw [check_footprint_append, requestAccepted, pendingAccepted]; rfl
  obtain ⟨upperClosingRow, upperExport, upperAccepted⟩ := ProtectionResiduals.residual_admitted_iff.mp closingAccepted
  obtain ⟨closingRow, closingExport, actualClosingBound⟩ := UniformClauseBounds.residual_coverage closingBound upperExport
  have closingAllowed := EffectBounds.check_covered upperAccepted actualClosingBound
  obtain ⟨contract, allowed, clauseDemand, clauseRequirements, capReq, tailDemand, tailReq, tailRow,
    resumeDemandSame, resumeRowSame, inputSame, closeDemandSame, closeRowSame, balance, heldSame, clauseSource, clauseRows, boundary, closingAfter,
    demandSame, rowSame, capCheck, tailCheck, afterUnique⟩ :=
    DeclaredSourceAllocation.allocate_selected_clause_from_split cut source closing cutAnnotation selected saved surviving
      cutDemand cutRecords cutRow savedChecked remainingChecked unique fresh clause operationKnown found available
      built internal template (some closingRow)
  let store : Store := (⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) ::
    (records ++ ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals))
  have phases := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.port)
    cut (RecursiveCapture.fresh_unowned source.erase fresh)
  have resumeCheck := RecursiveClauses.fresh_resume_check capCheck phases
  have templateAfter := DeclaredSourceClosing.template_extension template (Owners.insert_extends (contract := contract) contracts fresh)
  have looked : RecursiveRequirements.lookup ⟨owner, .dispose⟩ store =
      some ⟨OwnerClosingSource.retirements plan, closingRequirements⟩ := by
    change RecursiveRequirements.lookup ⟨owner, .dispose⟩
      (((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) :: records) ++
        ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals)) = _
    rw [RecursiveDisposalCapture.lookup_after_resumes (fun key body member => RecursiveRecords.resume_mode boundary.erase member)]
    simp [RecursiveRequirements.lookup]
  have disposeCheck := RecursiveDisposalCapture.closing_invocation_from_record (DeclaredSourceClosing.template_erase templateAfter) looked afterUnique built
    (RecursivePlanAdmission.captured_evaluation (DeclaredSourceClosing.template_erase templateAfter) built afterUnique closingExport)
  rw [← closeDemandSame] at disposeCheck
  refine ⟨contract, allowed, clauseDemand, clauseRequirements, store, tailDemand, tailRow, closingRow, requestRow, resumeRowSame, requestExport,
    inputSame, closeRowSame, closingExport, closingAllowed, balance, clauseSource, resumeCheck, disposeCheck, ?_⟩
  intro closingWithinBudget
  let initial := OwnerPhaseTransitions.available (ownedTickets
    (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
  have interface : ClauseRowAdmission.Interface owner contract offered.dispose store (OwnerPhases.ofStack tables tail) initial requestRow := by
    refine ⟨?_, ?_, fun _ => ⟨closingRow, closeRowSame⟩, ?_, OwnerPhaseTransitions.capture_tail_fresh cut (RecursiveCapture.fresh_unowned source.erase fresh)⟩
    · simpa only [OwnerPhases.ofStack, heldSame] using resumeCheck
    · intro _ actual same
      cases Option.some.inj (closeRowSame.symm.trans same)
      simpa only [OwnerPhases.ofStack, heldSame] using disposeCheck
    · intro _ actual same
      cases Option.some.inj (closeRowSame.symm.trans same)
      exact closingWithinBudget
  have exported : OwnerSource.exportAt (OwnerPhases.ofStack tables tail) initial offeredRow = some requestRow := by
    rw [OwnerSource.exportAt, OwnerPhaseTransitions.project_agrees, OwnerPhases.project_stack]
    · exact requestExport
    · intro nested member
      rw [OwnerPhaseTransitions.liveNames_stack] at member
      simp [initial, OwnerPhaseTransitions.available, ownedTickets, active_tickets_owned tail member]
  obtain ⟨clauseRow, clauseChecked, covered⟩ := ClauseRowAdmission.Rows.instantiate clauseRows interface exported
      (ClauseRowAdmission.SourceStore.of_source boundary.erase (DeclaredSourceClosing.records_erase closingAfter) (by simp [Owners.Contracts.insert]))
  have clauseCheck : Checked store
      (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) initial
      clauseRequirements clauseRow := by
    simpa only [OwnerPhases.ofStack, heldSame] using clauseChecked
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have payloadAfter := DeclaredSourceValues.extension (DeclaredSourceValues.change_allowed payload closed.1 allowed)
    (Owners.insert_extends (contract := contract) contracts fresh)
  have current := DeclaredSourceSubstitution.substitution clauseSource payloadAfter closed
  have completed := RecursiveClauseUsage.declared_clause_completed clause capabilities (DeclaredSources.expression_erase clauseSource) clauseCheck
  have included : (clauseRow ++ tailRow) ⊆ (requestRow ++ row) := by
    rw [rowSame, ← List.append_assoc]
    exact ScopedExpressions.append_subset covered (List.Subset.refl _)
  have result := fresh_clause_configuration known boundary closingAfter capCheck tailCheck
    (RecursiveCapture.capture_phase_consumed cut (RecursiveCapture.fresh_unowned source.erase fresh)) afterUnique
    current clauseCheck balance completed (checked_footprint_subset accepted included)
  have ready : ClosedExcept parameter body := by
    obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut (SourceTemplates.segment_ports source.erase)
    cases handlerTyped with
    | handler scopeKnown clauses coverage unique =>
        obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed clause clauses
        exact ScopedPorts.typed_suffix_ready bodyTyped
  refine ⟨clauseRow, RawStep.capture requested operation parameter binder owner operand body scope whole capture tail handler
    (ScopedPorts.embedPort input.port) cut clause closed ready, result.1, ?_, included, RecursiveCapture.capture_owned cut⟩
  simpa only [demandSame, List.cons_append] using result.2

theorem capture_from_declaration
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (closing : Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (capabilities : ClausesUse policy handler.clauses)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (offeredAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) offeredRow = true)
    (pendingAccepted : checkFootprint outside row = true)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (closingBound : EffectBounds.Covers upperClosing raw)
    (closingAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) upperClosing = true) :
    ∃ (contract : Owners.Contract) (allowed : List Instance) (clauseDemand : List Nat)
      (clauseRequirements : Requirements clauseDemand) (store : Store) (tailDemand : List Nat) (tailRow closingRow requestRow : Footprint),
      ProtectionResiduals.residualize (CallableProtectionFrames.contextOf tables tail) offeredRow = some requestRow ∧
      contract.input = input ∧ contract.closeRow = some closingRow ∧
      ProtectionResiduals.residualize (CallableProtectionFrames.contextOf tables tail) raw = some closingRow ∧
      checkFootprint outside closingRow = true ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) closingRow ∧
      ∀ (_ : closingRow ⊆ requestRow ++ contract.resumeRow),
        ∃ clauseRow,
          RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
            ⟨body.subst parameter operand, .ticket binder owner,
              .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
          CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
            (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
            output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
          (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
          (clauseRow ++ tailRow) ⊆ (requestRow ++ row) ∧
          ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  obtain ⟨answer, capDemand, remainingDemand, savedRequirements, remainingRequirements, capRecords, tailRecords, capRow, remainingRow,
    cutAnnotation, selected, saved, surviving, cutDemand, cutRecords, cutRow, savedChecked, remainingChecked⟩ :=
    RecursiveCapture.capture_segments_checked_with_frames cut source checked
  obtain ⟨contract, allowed, clauseDemand, clauseRequirements, store, tailDemand, tailRow, closingRow, requestRow,
    resumeRowSame, result⟩ :=
    capture_from_declaration_split cut source closing cutAnnotation selected saved surviving cutDemand cutRecords cutRow
      (by simpa only [List.append_nil] using savedChecked) remainingChecked unique fresh clause capabilities
      operationKnown payload closed found available offeredAccepted pendingAccepted built internal template closingBound closingAccepted
  exact ⟨contract, allowed, clauseDemand, clauseRequirements, store, tailDemand, tailRow, closingRow, requestRow, result⟩

/-- A capture without disposal still admits a declared one-shot clause from its
    upper certificate. Its absent disposal capability is proved separately. -/
theorem capture_without_disposal_from_declaration
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (closing : Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (capabilities : ClausesUse policy handler.clauses)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (offeredAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) offeredRow = true)
    (pendingAccepted : checkFootprint outside row = true)
    (unavailable : makePlan capture = none ∨ ¬ InternalUses capture.erase.liveTickets capture.erase.pending)
    (noDispose : offered.dispose = false) :
    ∃ (contract : Owners.Contract) (allowed : List Instance) (clauseDemand : List Nat)
      (clauseRequirements : Requirements clauseDemand) (store : Store) (tailDemand : List Nat) (tailRow requestRow : Footprint),
      ProtectionResiduals.residualize (CallableProtectionFrames.contextOf tables tail) offeredRow = some requestRow ∧
      contract.input = input ∧ contract.closeRow = none ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      (∀ nested nearer row, ¬ Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .dispose⟩ nested nearer) row) ∧
        ∃ clauseRow,
          RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
            ⟨body.subst parameter operand, .ticket binder owner,
              .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
          CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
            (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
            output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
          (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
          (clauseRow ++ tailRow) ⊆ (requestRow ++ row) ∧
          ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  obtain ⟨requestRow, requestExport, requestAccepted⟩ := ProtectionResiduals.residual_admitted_iff.mp offeredAccepted
  have accepted : checkFootprint outside (requestRow ++ row) = true := by
    rw [check_footprint_append, requestAccepted, pendingAccepted]; rfl
  obtain ⟨contract, allowed, clauseDemand, clauseRequirements, capReq, tailDemand, tailReq, tailRow,
    inputSame, closeDemandSame, closeRowSame, balance, heldSame, clauseSource, clauseRows, boundary, closingAfter,
    demandSame, rowSame, capCheck, tailCheck, afterUnique⟩ :=
    allocate_selected_without_disposal cut source closing checked unique fresh clause operationKnown found available unavailable
  let store : Store := (⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) ::
    (records ++ disposals)
  have phases := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.port)
    cut (RecursiveCapture.fresh_unowned source.erase fresh)
  have resumeCheck := RecursiveClauses.fresh_resume_check capCheck phases
  refine ⟨contract, allowed, clauseDemand, clauseRequirements, store, tailDemand, tailRow, requestRow, requestExport,
    inputSame, closeRowSame, balance, clauseSource, resumeCheck, ?_, ?_⟩
  · intro nested nearer row
    exact SourceClauseCapture.unavailable_disposal_rejected boundary.erase (DeclaredSourceClosing.records_erase closingAfter) afterUnique unavailable
  · let initial := OwnerPhaseTransitions.available (ownedTickets
      (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
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
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) initial
        clauseRequirements clauseRow := by
      simpa only [OwnerPhases.ofStack, heldSame] using clauseChecked
    have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
    have payloadAfter := DeclaredSourceValues.extension (DeclaredSourceValues.change_allowed payload closed.1 allowed)
      (Owners.insert_extends (contract := contract) contracts fresh)
    have current := DeclaredSourceSubstitution.substitution clauseSource payloadAfter closed
    have completed := RecursiveClauseUsage.declared_clause_completed clause capabilities (DeclaredSources.expression_erase clauseSource) clauseCheck
    have included : (clauseRow ++ tailRow) ⊆ (requestRow ++ row) := by
      rw [rowSame, ← List.append_assoc]
      exact ScopedExpressions.append_subset covered (List.Subset.refl _)
    have result := fresh_clause_configuration known boundary closingAfter capCheck tailCheck
      (RecursiveCapture.capture_phase_consumed cut (RecursiveCapture.fresh_unowned source.erase fresh)) afterUnique
      current clauseCheck balance completed (checked_footprint_subset accepted included)
    have ready : ClosedExcept parameter body := by
      obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut (SourceTemplates.segment_ports source.erase)
      cases handlerTyped with
      | handler scopeKnown clauses coverage unique =>
          obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed clause clauses
          exact ScopedPorts.typed_suffix_ready bodyTyped
    refine ⟨clauseRow, RawStep.capture requested operation parameter binder owner operand body scope whole capture tail handler
      (ScopedPorts.embedPort input.port) cut clause closed ready, result.1, ?_, included, RecursiveCapture.capture_owned cut⟩
    simpa only [demandSame, List.cons_append] using result.2


end Ash.OneShot.DeclaredSourceCapture

#print axioms Ash.OneShot.DeclaredSourceCapture.checked_clause_configuration
#print axioms Ash.OneShot.DeclaredSourceCapture.fresh_clause_configuration
#print axioms Ash.OneShot.DeclaredSourceCapture.capture_from_declaration
#print axioms Ash.OneShot.DeclaredSourceCapture.capture_without_disposal_from_declaration

#print axioms Ash.OneShot.DeclaredSourceCapture.capture_from_declaration_split
