import DeclaredSourceClosing

/-! Chosen-template allocation from hereditary clause families and indexed
saved frames. Existing allocation supplies the exact contract and checks;
hereditary closing evidence is transported under that same contract extension. -/
namespace Ash.OneShot.DeclaredSourceAllocation
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSourceFrames (Segment)
open RecursiveRequirements (Requirements Store Checked)

/-- Retain the actual resumption row from the supplied source cut. The
allocation and ownership construction are unchanged. -/
theorem allocate_selected_clause_from_split
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (closing : DeclaredSourceClosing.Records operations policy contracts tables world whole disposals)
    (annotation : answer.port = ScopedPorts.eraseType handler.answer)
    (declaration : DeclaredSourceFrames.Frame operations policy contracts tables world
      (.handler handler) answer answer [] (.request [] []))
    (saved : Segment operations policy contracts tables world capture input answer capDemand capReq capRecords)
    (outside : Segment operations policy contracts tables world tail answer output tailDemand tailReq tailRecords)
    (sameDemand : demand = capDemand ++ tailDemand) (sameRecords : records = capRecords ++ tailRecords)
    (sameRow : row = capRow ++ tailRow)
    (savedCheck : Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
      (OwnerPhaseTransitions.available (ownedTickets whole)) capReq capRow)
    (tailCheck : Checked (records ++ disposals) []
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (closeRow : Option Footprint) :
    ∃ (contract : Owners.Contract) (allowed : List Instance) (clauseDemand : List Nat)
      (clauseRequirements : Requirements clauseDemand) (capReq : Requirements contract.resumeDemand)
      (tailDemand : List Nat) (tailReq : Requirements tailDemand) (tailRow : Footprint),
      contract.resumeDemand = capDemand ∧ contract.resumeRow = capRow ∧
      contract.input = input ∧ contract.closeDemand = OwnerClosingSource.retirements plan ∧
      contract.closeRow = closeRow ∧ contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      DeclaredSources.Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements ∧
      ClauseRowAdmission.Rows ⟨owner, contract, offered.dispose, offeredRow⟩ clauseRequirements (ClauseRowAdmission.SourceStore operations owner contract) ∧
      Segment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailReq)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) :: records) ∧
      DeclaredSourceClosing.Records operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals) ∧
      demand = contract.resumeDemand ++ tailDemand ∧ row = contract.resumeRow ++ tailRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) ::
        (records ++ ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals)))
        (OwnerPhases.ofStack tables tail) (OwnerPhaseTransitions.available (ownedTickets whole)) capReq contract.resumeRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) ::
        (records ++ ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals))) []
        (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) contract.resumeDemand) tailReq tailRow ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)).Nodup := by
  obtain ⟨allowed, clauses⟩ := DeclaredSourceFrames.frame_declarations declaration
  obtain ⟨declaredArgument, declaredInput, resumeEffects, closeEffects, knownOperation, resumeInterface, closeInterface, family⟩ :=
    DeclaredSources.selected_body clauses clause found available
  rw [ScopedTyping.handler_cut_instance cut] at knownOperation
  have sameTypes := Prod.mk.inj (Option.some.inj (knownOperation.symm.trans operationKnown))
  rcases sameTypes with ⟨rfl, rfl⟩
  have chosen := DeclaredSourceClosing.capture_records_with_template
    (owner := owner) (input := ScopedPorts.embedPort declaredInput.port) (answer := handler.answer) (caller := handler.scope)
    cut closing built internal template
  have keys : ∀ (key : RecursiveRequirements.Key) (body : RecursiveRequirements.Template),
      (key, body) ∈ [(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] →
      key.owner = owner ∧ key.mode = .dispose := by
    intro key body member
    cases List.mem_singleton.mp member
    exact ⟨rfl, rfl⟩
  obtain ⟨contract, capturedRequirements, remainingDemand, remainingRequirements, remainingRow,
    answerSame, resumeDemandSame, resumeRowSame, heldSame, inputSame, answerAnnotation, selected,
    closeDemandSame, closeRowSame, resumeSame, closeSame, demandSame, rowSame,
    boundary, closingAfter, addedKeys, capCheck, remainingCheck, afterUnique, phases⟩ :=
    RecursiveAllocation.allocate_split_with_frames cut source annotation declaration saved outside
      sameDemand sameRecords sameRow savedCheck tailCheck
      unique fresh (OwnerClosingSource.retirements plan) closeRow resumeEffects closeEffects (DeclaredSourceClosing.records_erase chosen) keys
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have ordinaryBoundary := boundary.erase
  have certificate := SourceTemplates.records_certified ordinaryBoundary
    (key := ⟨owner, .resume⟩) (body := ⟨contract.resumeDemand, capturedRequirements⟩) List.mem_cons_self
  obtain ⟨actualContract, actualRequirements, actualRecords, actualKnown, actualTemplate, captured⟩ :=
    SourceTemplates.certified_selected certificate afterUnique SourceTemplates.ActiveCapture.here
  have sameContract := Option.some.inj (actualKnown.symm.trans known)
  cases sameContract
  have sameRequirements := eq_of_heq (Sigma.mk.inj actualTemplate).2
  subst actualRequirements
  have captureBalance := RecursiveDisposalCapture.captured_segment_balance ordinaryBoundary closingAfter afterUnique
    SourceTemplates.CapturedIn.here internal captured capCheck (by
      intro nested member
      apply if_pos
      rw [handler_cut_reconstructs cut, owned_tickets_append]
      exact List.mem_append_left _ member)
  have balance : contract.closeDemand.Perm contract.resumeDemand := by
    rw [closeDemandSame]
    exact (OwnerClosingSource.retirements_capture built).trans captureBalance.symm
  have supplied := family owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  rw [← answerSame] at supplied
  cases supplied with
  | typed clauseSource clauseRows =>
    rename_i clauseDemand clauseRequirements
    have declarationsAfter : Segment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort declaredInput.port) handler.answer capture handler.scope tail)
        contract.answer output remainingDemand (.sequence (.spent owner) remainingRequirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) :=
      DeclaredSourceFrames.segment_reindex_contracts boundary (Owners.insert_extends contracts fresh)
    exact ⟨contract, allowed, clauseDemand, clauseRequirements, capturedRequirements,
      remainingDemand, remainingRequirements, remainingRow, resumeDemandSame, resumeRowSame, inputSame, closeDemandSame, closeRowSame,
      balance, heldSame, clauseSource, clauseRows, declarationsAfter, DeclaredSourceClosing.records_extension chosen (Owners.insert_extends contracts fresh), demandSame, rowSame, capCheck, remainingCheck, afterUnique⟩

theorem allocate_selected_clause
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (closing : DeclaredSourceClosing.Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (closeRow : Option Footprint) :
    ∃ (contract : Owners.Contract) (allowed : List Instance) (clauseDemand : List Nat)
      (clauseRequirements : Requirements clauseDemand) (capReq : Requirements contract.resumeDemand)
      (tailDemand : List Nat) (tailReq : Requirements tailDemand) (tailRow : Footprint),
      contract.input = input ∧ contract.closeDemand = OwnerClosingSource.retirements plan ∧
      contract.closeRow = closeRow ∧ contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      DeclaredSources.Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements ∧
      ClauseRowAdmission.Rows ⟨owner, contract, offered.dispose, offeredRow⟩ clauseRequirements (ClauseRowAdmission.SourceStore operations owner contract) ∧
      Segment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailReq)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) :: records) ∧
      DeclaredSourceClosing.Records operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals) ∧
      demand = contract.resumeDemand ++ tailDemand ∧ row = contract.resumeRow ++ tailRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) ::
        (records ++ ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals)))
        (OwnerPhases.ofStack tables tail) (OwnerPhaseTransitions.available (ownedTickets whole)) capReq contract.resumeRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) ::
        (records ++ ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals))) []
        (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) contract.resumeDemand) tailReq tailRow ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)).Nodup := by
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capRow, tailRow,
    annotation, declaration, saved, outside, sameDemand, sameRecords, sameRow, savedCheck, tailCheck⟩ :=
    RecursiveCapture.capture_segments_checked_with_frames cut source checked
  obtain ⟨contract, allowed, clauseDemand, clauseRequirements, capReq, tailDemand, tailReq, tailRow,
    resumeDemandSame, resumeRowSame, result⟩ :=
    allocate_selected_clause_from_split cut source closing annotation declaration saved outside
      sameDemand sameRecords sameRow (by simpa only [List.append_nil] using savedCheck) tailCheck
      unique fresh clause operationKnown found available built internal template closeRow
  exact ⟨contract, allowed, clauseDemand, clauseRequirements, capReq, tailDemand, tailReq, tailRow, result⟩

/-- Resume-only allocation retains declarations without constructing a closing
    plan. The unused closing demand is set equal to the actual resume demand. -/
theorem allocate_selected_without_disposal
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (closing : DeclaredSourceClosing.Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (unavailable : makePlan capture = none ∨ ¬ InternalUses capture.erase.liveTickets capture.erase.pending) :
    ∃ (contract : Owners.Contract) (allowed : List Instance) (clauseDemand : List Nat)
      (clauseRequirements : Requirements clauseDemand) (capReq : Requirements contract.resumeDemand)
      (tailDemand : List Nat) (tailReq : Requirements tailDemand) (tailRow : Footprint),
      contract.input = input ∧ contract.closeDemand = contract.resumeDemand ∧
      contract.closeRow = none ∧ contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      DeclaredSources.Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements ∧
      ClauseRowAdmission.Rows ⟨owner, contract, offered.dispose, offeredRow⟩ clauseRequirements (ClauseRowAdmission.SourceStore operations owner contract) ∧
      Segment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailReq)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) :: records) ∧
      DeclaredSourceClosing.Records operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        disposals ∧
      demand = contract.resumeDemand ++ tailDemand ∧ row = contract.resumeRow ++ tailRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) ::
        (records ++ disposals))
        (OwnerPhases.ofStack tables tail) (OwnerPhaseTransitions.available (ownedTickets whole)) capReq contract.resumeRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) ::
        (records ++ disposals)) []
        (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) contract.resumeDemand) tailReq tailRow ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)).Nodup := by
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capRow, tailRow,
    annotation, declaration, saved, outside, sameDemand, sameRecords, sameRow, savedCheck, tailCheck⟩ :=
    RecursiveCapture.capture_segments_checked_with_frames cut source checked
  obtain ⟨allowed, clauses⟩ := DeclaredSourceFrames.frame_declarations declaration
  obtain ⟨declaredArgument, declaredInput, resumeEffects, closeEffects, knownOperation, resumeInterface, closeInterface, family⟩ :=
    DeclaredSources.selected_body clauses clause found available
  rw [ScopedTyping.handler_cut_instance cut] at knownOperation
  have sameTypes := Prod.mk.inj (Option.some.inj (knownOperation.symm.trans operationKnown))
  rcases sameTypes with ⟨rfl, rfl⟩
  obtain ⟨nested, remaining, savedClosing, tailClosing, sameClosings⟩ :=
    DeclaredSourceClosing.split_append (handler_cut_reconstructs cut ▸ closing)
  have chosen : DeclaredSourceClosing.Records operations policy contracts tables world
      (.live owner (ScopedPorts.embedPort declaredInput.port) handler.answer capture handler.scope tail) ([] ++ disposals) := by
    rw [List.nil_append, sameClosings]
    rcases unavailable with blocked | external
    · exact .unclosable blocked savedClosing tailClosing
    · exact .external external savedClosing tailClosing
  have keys : ∀ (key : RecursiveRequirements.Key) (body : RecursiveRequirements.Template),
      (key, body) ∈ ([] : Store) → key.owner = owner ∧ key.mode = .dispose := by simp
  obtain ⟨contract, capturedRequirements, remainingDemand, remainingRequirements, remainingRow,
    answerSame, resumeDemandSame, resumeRowSame, heldSame, inputSame, answerAnnotation, selected,
    closeDemandSame, closeRowSame, resumeSame, closeSame, demandSame, rowSame,
    boundary, closingAfter, addedKeys, capCheck, remainingCheck, afterUnique, phases⟩ :=
    RecursiveAllocation.allocate_split_with_frames cut source annotation declaration saved outside
      sameDemand sameRecords sameRow (by simpa only [List.append_nil] using savedCheck) tailCheck
      unique fresh capDemand none resumeEffects closeEffects (DeclaredSourceClosing.records_erase chosen) keys
  have equalDemands : contract.closeDemand = contract.resumeDemand := closeDemandSame.trans resumeDemandSame.symm
  have balance : contract.closeDemand.Perm contract.resumeDemand := equalDemands ▸ List.Perm.refl _
  have supplied := family owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  rw [← answerSame] at supplied
  cases supplied with
  | typed clauseSource clauseRows =>
    rename_i clauseDemand clauseRequirements
    have declarationsAfter : Segment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort declaredInput.port) handler.answer capture handler.scope tail)
        contract.answer output remainingDemand (.sequence (.spent owner) remainingRequirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) :=
      DeclaredSourceFrames.segment_reindex_contracts boundary (Owners.insert_extends contracts fresh)
    exact ⟨contract, allowed, clauseDemand, clauseRequirements, capturedRequirements,
      remainingDemand, remainingRequirements, remainingRow, inputSame, equalDemands, closeRowSame,
      balance, heldSame, clauseSource, clauseRows, declarationsAfter, DeclaredSourceClosing.records_extension chosen (Owners.insert_extends contracts fresh), demandSame, rowSame, capCheck, remainingCheck, afterUnique⟩


end Ash.OneShot.DeclaredSourceAllocation

#print axioms Ash.OneShot.DeclaredSourceAllocation.allocate_selected_clause
#print axioms Ash.OneShot.DeclaredSourceAllocation.allocate_selected_without_disposal

#print axioms Ash.OneShot.DeclaredSourceAllocation.allocate_selected_clause_from_split
