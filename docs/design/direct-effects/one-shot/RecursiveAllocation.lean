import RecursiveExecution

/-!
Fresh capture retains both recursively collected continuation modes. New
closing entries are authenticated from the actual capture and cannot affect
checks at phases where their fresh owner is consumed. Clause admission and
operation-effect bounds remain explicit structural premises.
-/

namespace Ash.OneShot.RecursiveAllocation
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open SourceTemplates (Expression Segment)
open RecursiveRecords (Records CheckedState)
open RecursiveRequirements (Requirements Store Checked evaluate)
open OwnerPhaseTransitions (Phases available spendAll)
open CallableProtectionFrames (Tables contextOf pushContext)
open RecursiveCapture (capture_segments fresh_unowned capture_unique checked_insert_consumed)
open RecursiveClauses (consuming_demand fresh_resume_check compile)
open RecursiveDispatch (request_evaluation cut_residual)

/-- Inserting records for one owner leaves every other lookup unchanged. -/
theorem lookup_add_closing {records added disposals : Store}
    (keys : ∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose)
    (different : key.owner ≠ owner) :
    RecursiveRequirements.lookup key (records ++ (added ++ disposals)) =
      RecursiveRequirements.lookup key (records ++ disposals) := by
  have skip : RecursiveRequirements.lookup key (added ++ disposals) = RecursiveRequirements.lookup key disposals := by
    induction added with
    | nil => rfl
    | cons entry rest ih =>
        have entryOwner := (keys entry.1 entry.2 List.mem_cons_self).1
        have notKey : key ≠ entry.1 := fun same => different ((congrArg RecursiveRequirements.Key.owner same).trans entryOwner)
        simp only [List.cons_append, RecursiveRequirements.lookup, if_neg notKey]
        exact ih (fun candidate body member => keys candidate body (List.mem_cons_of_mem _ member))
  induction records with
  | nil => exact skip
  | cons entry rest ih =>
      simp only [List.cons_append, RecursiveRequirements.lookup]
      split
      · rfl
      · exact ih

theorem checked_add_closing
    (checked : Checked (records ++ disposals) receiving before requirements row)
    (consumed : before owner = .consumed)
    (keys : ∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose) :
    Checked (records ++ (added ++ disposals)) receiving before requirements row := by
  apply RecursiveTransport.checked_transport checked _ rfl
  intro key ready
  have different : key.owner ≠ owner := by
    intro same
    rw [same, consumed] at ready
    cases ready
  exact (lookup_add_closing keys different).symm

theorem capture_segments_checked
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (checked : Checked store receiving before requirements row) :
    ∃ (answer : Value) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedRow tailRow : Footprint),
      answer.port = ScopedPorts.eraseType handler.answer ∧
      Segment operations policy contracts tables world capture input answer capturedDemand capturedRequirements capturedRecords ∧
      Segment operations policy contracts tables world tail answer output tailDemand tailRequirements tailRecords ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧ row = capturedRow ++ tailRow ∧
      Checked store (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements capturedRow ∧
      Checked store receiving (spendAll before capturedDemand) tailRequirements tailRow := by
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
    annotation, saved, outside, sameDemand, sameRecords, evaluation⟩ := capture_segments cut source
  have original := RecursiveRequirements.checked_complete checked
  rw [evaluation] at original
  obtain ⟨capturedRow, tailRow, inside, rest, sameRow⟩ := PhaseRechecking.merge_split original
  exact ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capturedRow, tailRow,
    annotation, saved, outside, sameDemand, sameRecords, sameRow,
    RecursiveRequirements.evaluate_sound inside, RecursiveRequirements.evaluate_sound rest⟩

/-- Allocation transports the supplied closing records through the fresh
    contract extension. Their template data is chosen before that extension. -/
theorem allocate_split_with_frames
    (cut : HandlerCut requested whole capture tail handler)
    (annotated : RecursiveCapture.AnnotatedSegment predicate operations policy contracts tables world whole input output demand requirements records)
    (annotation : answer.port = ScopedPorts.eraseType handler.answer)
    (selected : predicate (.handler handler) answer answer [] (.request [] []))
    (saved : RecursiveCapture.AnnotatedSegment predicate operations policy contracts tables world capture input answer capDemand capReq capRecords)
    (outside : RecursiveCapture.AnnotatedSegment predicate operations policy contracts tables world tail answer output tailDemand tailReq tailRecords)
    (sameDemand : demand = capDemand ++ tailDemand) (sameRecords : records = capRecords ++ tailRecords)
    (sameRow : row = capRow ++ tailRow)
    (savedCheck : Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
      (OwnerPhaseTransitions.available (ownedTickets whole)) capReq capRow)
    (tailCheck : Checked (records ++ disposals) []
      (spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (closeDemand : List Nat) (closeRow : Option Footprint) (resumeEffects closeEffects : List Instance)
    (chosen : Records operations policy contracts tables world
      (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) (added ++ disposals))
    (addedKeys : ∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose) :
    ∃ (contract : Owners.Contract) (capturedRequirements : Requirements contract.resumeDemand)
      (tailDemand : List Nat) (tailRequirements : Requirements tailDemand) (tailRow : Footprint),
      contract.answer = answer ∧ contract.resumeDemand = capDemand ∧ contract.resumeRow = capRow ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      predicate (.handler handler) contract.answer contract.answer [] (.request [] []) ∧
      contract.closeDemand = closeDemand ∧ contract.closeRow = closeRow ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      demand = contract.resumeDemand ++ tailDemand ∧ row = contract.resumeRow ++ tailRow ∧
      RecursiveCapture.AnnotatedSegment predicate operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailRequirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) ∧
      Records operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) (added ++ disposals) ∧
      (∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose) ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ (added ++ disposals)))
        (OwnerPhases.ofStack tables tail) (OwnerPhaseTransitions.available (ownedTickets whole))
        capturedRequirements contract.resumeRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ (added ++ disposals))) []
        (spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) contract.resumeDemand) tailRequirements tailRow ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)).Nodup ∧
      OwnerPhaseTransitions.available
        (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) =
        OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner := by
  have source := annotated.erase
  let contract : Owners.Contract := ⟨input, answer, ProtectionContexts.protectedMode capture.erase,
    capDemand, capRow, closeDemand, closeRow, resumeEffects, closeEffects⟩
  have extension := Owners.insert_extends (contract := contract) contracts fresh
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have types := ScopedPorts.effect_extension_has_type_extension (Owners.port_contracts_extension extension)
  have scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types handler.scope := by
    obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut (SourceTemplates.segment_ports source)
    cases handlerTyped with
    | handler known clauses coverage unique => exact known
  have consumed : OwnerPhaseTransitions.available (ownedTickets whole) owner = .consumed := by
    simp only [OwnerPhaseTransitions.available, if_neg (fresh_unowned source fresh)]
  have consumedLater : spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand owner = .consumed :=
    OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedCheck) consumed
  have closingAfter := RecursiveRecords.records_extension chosen extension
  have savedAdded := checked_add_closing savedCheck consumed addedKeys
  have tailAdded := checked_add_closing tailCheck consumedLater addedKeys
  refine ⟨contract, capReq, tailDemand, tailReq, tailRow, rfl, rfl, rfl, rfl, rfl, annotation, selected, rfl, rfl, rfl, rfl,
    sameDemand, sameRow, ?_, closingAfter, addedKeys, ?_, checked_insert_consumed tailAdded consumedLater,
    capture_unique cut source unique fresh, OwnerPhaseTransitions.capture_map cut⟩
  · rw [sameRecords]
    exact .live known (ScopedPorts.erase_embed_port input.port).symm annotation
      (ScopedPorts.scope_known_extension scopeKnown types) rfl
      (saved.extension extension (fun _ _ _ _ _ current => current)) (outside.extension extension (fun _ _ _ _ _ current => current))
  · exact checked_insert_consumed (by simpa only [List.append_nil] using savedAdded) consumed

theorem capture_record_with_frames
    (cut : HandlerCut requested whole capture tail handler)
    (annotated : RecursiveCapture.AnnotatedSegment predicate operations policy contracts tables world whole input output demand requirements records)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (closeDemand : List Nat) (closeRow : Option Footprint) (resumeEffects closeEffects : List Instance)
    (chosen : Records operations policy contracts tables world
      (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) (added ++ disposals))
    (addedKeys : ∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose) :
    ∃ (contract : Owners.Contract) (capturedRequirements : Requirements contract.resumeDemand)
      (tailDemand : List Nat) (tailRequirements : Requirements tailDemand) (tailRow : Footprint),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      predicate (.handler handler) contract.answer contract.answer [] (.request [] []) ∧
      contract.closeDemand = closeDemand ∧ contract.closeRow = closeRow ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      demand = contract.resumeDemand ++ tailDemand ∧ row = contract.resumeRow ++ tailRow ∧
      RecursiveCapture.AnnotatedSegment predicate operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailRequirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) ∧
      Records operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) (added ++ disposals) ∧
      (∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose) ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ (added ++ disposals)))
        (OwnerPhases.ofStack tables tail) (OwnerPhaseTransitions.available (ownedTickets whole))
        capturedRequirements contract.resumeRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ (added ++ disposals))) []
        (spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) contract.resumeDemand) tailRequirements tailRow ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)).Nodup ∧
      OwnerPhaseTransitions.available
        (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) =
        OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner := by
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capRow, tailRow,
    annotation, selected, saved, outside, sameDemand, sameRecords, sameRow, savedCheck, tailCheck⟩ :=
    RecursiveCapture.capture_segments_checked_with_frames cut annotated checked
  obtain ⟨contract, capturedRequirements, tailDemand, tailRequirements, tailRow,
    answerSame, resumeDemandSame, resumeRowSame, heldSame, result⟩ :=
    allocate_split_with_frames cut annotated annotation selected saved outside sameDemand sameRecords sameRow
      (by simpa only [List.append_nil] using savedCheck) tailCheck unique fresh closeDemand closeRow
      resumeEffects closeEffects chosen addedKeys
  exact ⟨contract, capturedRequirements, tailDemand, tailRequirements, tailRow, result⟩

theorem capture_record_with_closing
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (closeDemand : List Nat) (closeRow : Option Footprint) (resumeEffects closeEffects : List Instance)
    (chosen : Records operations policy contracts tables world
      (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) (added ++ disposals))
    (addedKeys : ∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose) :
    ∃ (contract : Owners.Contract) (capturedRequirements : Requirements contract.resumeDemand)
      (tailDemand : List Nat) (tailRequirements : Requirements tailDemand) (tailRow : Footprint),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = closeDemand ∧ contract.closeRow = closeRow ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      demand = contract.resumeDemand ++ tailDemand ∧ row = contract.resumeRow ++ tailRow ∧
      Segment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailRequirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) ∧
      Records operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) (added ++ disposals) ∧
      (∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose) ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ (added ++ disposals)))
        (OwnerPhases.ofStack tables tail) (OwnerPhaseTransitions.available (ownedTickets whole))
        capturedRequirements contract.resumeRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ (added ++ disposals))) []
        (spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) contract.resumeDemand) tailRequirements tailRow ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)).Nodup ∧
      OwnerPhaseTransitions.available
        (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) =
        OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner := by
  obtain ⟨contract, capturedRequirements, tailDemand, tailRequirements, tailRow,
    inputSame, answerSame, selected, closeDemandSame, closeRowSame, resumeSame, closeSame,
    sameDemand, sameRow, boundary, closingAfter, keys, savedCheck, tailCheck, afterUnique, phases⟩ :=
    capture_record_with_frames cut (RecursiveCapture.AnnotatedSegment.trivial source) checked unique fresh
      closeDemand closeRow resumeEffects closeEffects chosen addedKeys
  exact ⟨contract, capturedRequirements, tailDemand, tailRequirements, tailRow,
    inputSame, answerSame, closeDemandSame, closeRowSame, resumeSame, closeSame,
    sameDemand, sameRow, boundary.erase, closingAfter, keys, savedCheck, tailCheck, afterUnique, phases⟩

theorem capture_record
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (closing : Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (closeDemand : List Nat) (closeRow : Option Footprint) (resumeEffects closeEffects : List Instance) :
    ∃ (contract : Owners.Contract) (capturedRequirements : Requirements contract.resumeDemand)
      (tailDemand : List Nat) (tailRequirements : Requirements tailDemand) (tailRow : Footprint) (added : Store),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = closeDemand ∧ contract.closeRow = closeRow ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      demand = contract.resumeDemand ++ tailDemand ∧ row = contract.resumeRow ++ tailRow ∧
      Segment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailRequirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) ∧
      Records operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) (added ++ disposals) ∧
      (∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose) ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ (added ++ disposals)))
        (OwnerPhases.ofStack tables tail) (OwnerPhaseTransitions.available (ownedTickets whole))
        capturedRequirements contract.resumeRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ (added ++ disposals))) []
        (spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) contract.resumeDemand) tailRequirements tailRow ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)).Nodup ∧
      OwnerPhaseTransitions.available
        (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) =
        OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner := by
  obtain ⟨added, chosen, keys⟩ := RecursiveRecords.capture_records
    (owner := owner) (inputType := ScopedPorts.embedPort input.port) (answerType := handler.answer) (caller := handler.scope)
    cut source closing (fun _ _ known => known)
  obtain ⟨contract, capturedRequirements, tailDemand, tailRequirements, tailRow, result⟩ :=
    capture_record_with_closing cut source checked unique fresh closeDemand closeRow resumeEffects closeEffects chosen keys
  exact ⟨contract, capturedRequirements, tailDemand, tailRequirements, tailRow, added, result⟩

/-- Allocate using this exact closing template, with no second collection
    choosing a different witness. The legacy allocation wrapper remains available. -/
theorem capture_record_with_template
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements records)
    (closing : Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (closeRow : Option Footprint) (resumeEffects closeEffects : List Instance)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : RecursiveClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements) :
    ∃ (contract : Owners.Contract) (capturedRequirements : Requirements contract.resumeDemand)
      (tailDemand : List Nat) (tailRequirements : Requirements tailDemand) (tailRow : Footprint),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = OwnerClosingSource.retirements plan ∧ contract.closeRow = closeRow ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      demand = contract.resumeDemand ++ tailDemand ∧ row = contract.resumeRow ++ tailRow ∧
      Segment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailRequirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) ∧
      Records operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals) ∧
      (∀ (key : RecursiveRequirements.Key) (body : RecursiveRequirements.Template), (key, body) ∈ [(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] → key.owner = owner ∧ key.mode = .dispose) ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals)))
        (OwnerPhases.ofStack tables tail) (OwnerPhaseTransitions.available (ownedTickets whole))
        capturedRequirements contract.resumeRow ∧
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals))) []
        (spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) contract.resumeDemand) tailRequirements tailRow ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)).Nodup ∧
      OwnerPhaseTransitions.available
        (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) =
        OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner := by
  have chosen := RecursiveRecords.capture_records_with_template
    (owner := owner) (input := ScopedPorts.embedPort input.port) (answer := handler.answer) (caller := handler.scope)
    cut closing built internal template
  have keys : ∀ (key : RecursiveRequirements.Key) (body : RecursiveRequirements.Template), (key, body) ∈ [(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] →
      key.owner = owner ∧ key.mode = .dispose := by
    intro key body member
    cases List.mem_singleton.mp member
    exact ⟨rfl, rfl⟩
  exact capture_record_with_closing cut source checked unique fresh (OwnerClosingSource.retirements plan)
    closeRow resumeEffects closeEffects chosen keys

/-- A new resume clause may restore a saved computation that uses nested
    disposal records. The newly bound clause itself remains resume-only here. -/
theorem fresh_clause_configuration_transport
    (known : contracts owner = some contract)
    (source : SourceTemplates.Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (closing : Records operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) disposals)
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (OwnerPhaseTransitions.spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : OwnerPhaseTransitions.spend
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (resumeOnly : contract.closeRow = none)
    (clause : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail)) world
      environment allowed (.ticket binder owner)
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail)))
      code after contract.answer clauseDemand clauseRow)
    (closeSource : ∀ demand requirements,
      SourceTemplates.Expression operations policy contracts world allowed (.ticket binder owner) environment
        code contract.answer demand requirements →
      SourceTemplates.Expression operations policy contracts world allowed (.ticket binder owner) Environment.empty
        nextCode contract.answer demand requirements)
    (completed : after owner = .consumed)
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    CheckedState operations policy contracts tables world outside (.ticket binder owner)
      nextCode (.live owner inputType answerType capture caller tail) output
      ((owner :: contract.resumeDemand) ++ tailDemand) (clauseRow ++ tailRow) := by
  let initial := OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))
  change OwnerPhaseTransitions.spend initial owner = before at phases
  have sameDemand := consuming_demand clause known resumeOnly
    (by simp [OwnerPhaseTransitions.available, ownedTickets]) completed
  subst clauseDemand
  have invocation := fresh_resume_check savedCheck phases
  obtain ⟨requirements, current, currentCheck⟩ := compile clause known invocation
    (fun closingRow closable => by rw [resumeOnly] at closable; cases closable) (fun _ => rfl)
  have consumed : before owner = .consumed := phases ▸ OwnerPhaseTransitions.spend_self initial owner
  have afterOwner : OwnerPhaseTransitions.spendAll before contract.resumeDemand owner = .consumed :=
    OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedCheck) consumed
  have pending : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (OwnerPhaseTransitions.spendAll initial (owner :: contract.resumeDemand))
      (.sequence (.spent owner) tailRequirements) tailRow := by
    have combined := Checked.sequence
      (Checked.spent (store := ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)))
        (receiving := []) afterOwner) tailCheck
    simpa only [OwnerPhaseTransitions.spendAll, phases, List.nil_append] using combined
  exact .checked (.checked (closeSource _ _ current) (.bound (Owners.ports_lookup known)) source) closing unique
    (.sequence (RecursiveRequirements.checked_prepend_iff.mpr
      (by simpa only [List.append_nil, List.cons_append] using currentCheck)) pending) accepted

theorem fresh_clause_configuration
    (known : contracts owner = some contract)
    (source : SourceTemplates.Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (closing : Records operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) disposals)
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (OwnerPhaseTransitions.spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : OwnerPhaseTransitions.spend
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (resumeOnly : contract.closeRow = none)
    (clause : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail)) world
      Environment.empty allowed (.ticket binder owner)
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail)))
      code after contract.answer clauseDemand clauseRow)
    (completed : after owner = .consumed)
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    CheckedState operations policy contracts tables world outside (.ticket binder owner)
      code (.live owner inputType answerType capture caller tail) output
      ((owner :: contract.resumeDemand) ++ tailDemand) (clauseRow ++ tailRow) :=
  fresh_clause_configuration_transport known source closing savedCheck tailCheck phases unique resumeOnly clause
    (fun _ _ current => current) completed accepted

theorem fresh_substituted_clause_configuration
    (known : contracts owner = some contract)
    (source : SourceTemplates.Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (closing : Records operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) disposals)
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (OwnerPhaseTransitions.spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : OwnerPhaseTransitions.spend
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (resumeOnly : contract.closeRow = none)
    (clause : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail)) world
      (Environment.empty.extend parameter argument) allowed (.ticket binder owner)
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail)))
      code after contract.answer clauseDemand clauseRow)
    (operand : SourceTemplates.ValueSummary operations policy contracts world Environment.empty allowed value argument)
    (closed : ClosedValue value)
    (completed : after owner = .consumed)
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    CheckedState operations policy contracts tables world outside (.ticket binder owner)
      (code.subst parameter value) (.live owner inputType answerType capture caller tail) output
      ((owner :: contract.resumeDemand) ++ tailDemand) (clauseRow ++ tailRow) :=
  fresh_clause_configuration_transport known source closing savedCheck tailCheck phases unique resumeOnly clause
    (fun _ _ current => SourceCallableSubstitution.substitution current operand closed) completed accepted

/-- Actual dispatch with both record modes retained. The selected new clause
    is still subject to structural admission and a resume-only contract. -/
theorem capture_from_structural_clause
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (resumeEffects : List Instance) :
    ∃ (contract : Owners.Contract) (offeredContract : ClauseContract) (offered requestRow tailRow : Footprint),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeRow = none ∧ contract.resumeEffects = resumeEffects ∧
      contract.resumeDemand.Sublist demand ∧
      row = (requestRow ++ contract.resumeRow) ++ tailRow ∧
      lookup operation (tables handler) = some offeredContract ∧
      modeCheck offeredContract.dispose (ProtectionContexts.protectedMode capture.erase) = true ∧
      offeredContract.row (ProtectionContexts.protectedMode capture.erase) = some offered ∧
      residualize (contextOf tables tail) offered = some requestRow ∧
      ∀ (allowed : List Instance) (after : Phases) (clauseDemand : List Nat) (clauseRow : Footprint),
        Owners.Derives operations policy (contracts.insert owner contract)
          (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) world
          (Environment.empty.extend parameter argument) allowed (.ticket binder owner)
          (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          body after contract.answer clauseDemand clauseRow →
        after owner = .consumed → clauseRow ⊆ (requestRow ++ contract.resumeRow) →
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
          ⟨body.subst parameter operand, .ticket binder owner,
            .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
        CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
          (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
          output (owner :: demand) (clauseRow ++ tailRow) ∧
        (clauseRow ++ tailRow) ⊆ row ∧
        ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨actualArgument, knownOperation, operandSummary, empty⟩ := RecursiveCapture.request_operand current isValue
        obtain ⟨sameArgument, sameInput⟩ := Prod.mk.inj (Option.some.inj (knownOperation.symm.trans operationKnown))
        subst_vars
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, sameRow⟩ := RecursiveRequirements.checked_sequence_parts checked
        have requestExport := RecursiveRequirements.checked_complete (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
        rw [request_evaluation current isValue] at requestExport
        simp only [List.append_nil, OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] at requestExport
        obtain ⟨offeredContract, offered, offeredKnown, offeredMode, offeredRow, offeredExport⟩ := cut_residual cut requestExport
        simp only [Bool.false_or] at offeredMode offeredRow
        obtain ⟨contract, capReq, tailDemand, tailReq, tailRow, added, inputSame, annotation, closeDemandSame, closeRowSame,
          resumeEffectsSame, closeEffectsSame, sameDemand, capturedRow, boundary, closingAfter, addedKeys, capCheck, tailCheck, afterUnique, map⟩ :=
          capture_record cut pending closing pendingCheck unique fresh [] none resumeEffects []
        have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
        have totalRow : row = (currentRow ++ contract.resumeRow) ++ tailRow := by
          simp only [sameRow, capturedRow, List.append_assoc]
        have closed : ClosedValue operand :=
          ScopedPorts.typed_value_closed (operandSummary.ports .none) isValue
        have ready : ClosedExcept parameter body := by
          obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut (SourceTemplates.segment_ports pending)
          cases handlerTyped with
          | handler scopeKnown clauses coverage unique =>
              obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed clause clauses
              exact ScopedPorts.typed_suffix_ready bodyTyped
        refine ⟨contract, offeredContract, offered, currentRow, tailRow, inputSame, annotation, closeRowSame,
          resumeEffectsSame, (by simpa only [sameDemand, List.nil_append] using List.sublist_append_left contract.resumeDemand tailDemand), totalRow, offeredKnown, offeredMode, offeredRow, offeredExport, ?_⟩
        intro allowed after clauseDemand clauseRow bodySource completed bounded
        have included : (clauseRow ++ tailRow) ⊆ row := by
          rw [totalRow]
          intro request member
          rcases List.mem_append.mp member with current | remaining
          · exact List.mem_append_left _ (bounded current)
          · exact List.mem_append_right _ remaining
        have afterChecked := fresh_substituted_clause_configuration known boundary closingAfter capCheck tailCheck
          (RecursiveCapture.capture_phase_consumed cut (RecursiveCapture.fresh_unowned pending fresh)) afterUnique closeRowSame
          bodySource ((operandSummary.change_allowed isValue allowed).extension (Owners.insert_extends contracts fresh)) closed
          completed (checked_footprint_subset accepted included)
        refine ⟨.capture requested operation parameter binder owner operand body scope whole capture tail handler
          _ cut clause closed ready, ?_, included, RecursiveCapture.capture_owned cut⟩
        simpa only [sameDemand, List.nil_append, List.cons_append] using afterChecked


namespace Examples
open RecursiveRecords.Examples (policy inner)

def effect : Instance := .user 91 []
def operations : Operations := fun target operation => if target = effect ∧ operation = 0 then some (.unit, .unit) else none
def contracts : Owners.Contracts := fun owner => if owner = 19 then some inner else none
def clause : Code := .resume 1 .unit
def handler : HandlerData := ⟨73, effect, .cons 0 2 1 clause .nil, .none, .unit, rfl⟩
def tables : Tables := fun _ => [(0, ⟨false, some [], some []⟩)]
def binding : PlainData := ⟨.bind 99 (.discard 0), .ticket 0 19, .unit, .unit, [19], rfl⟩
def handlerStack : Stack := .push (.handler handler) .nil
def innerBoundary : Stack := .live 19 .unit .unit .nil .none handlerStack
def capture : Stack := .push (.plain binding) innerBoundary
def boundary : Stack := .live 23 .unit .unit capture .none .nil

def emptyRequirements : Requirements [] := .request [] []
def handlerRequirements : Requirements [] := .sequence (emptyRequirements.prepend []) emptyRequirements
def innerRequirements : Requirements [] := .sequence (.spent 19) handlerRequirements
def pendingRequirements : Requirements [19] := .sequence
  ((Requirements.invoke ⟨19, .dispose⟩ [] []).prepend (OwnerPhases.ofStack tables innerBoundary)) innerRequirements

def resumes : Store := [(⟨19, .resume⟩, ⟨[], emptyRequirements⟩)]
def disposals : Store := [(⟨19, .dispose⟩, ⟨[], emptyRequirements⟩)]
def requestRequirements : Requirements [] := .emitAfter emptyRequirements [] [⟨effect, 0, false⟩]

theorem operation_known : operations effect 0 = some (.unit, .unit) := rfl
theorem inner_known : contracts 19 = some inner := rfl

theorem handler_typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types [] (.handler handler) := by
  have body : ScopedPorts.Typed operations.ports [] (ScopedPorts.TypeEnv.empty.extend 2 .unit)
      (.bound 1 .unit .unit [] []) [] clause .unit :=
    .resume .unit (by simp) (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources])
  refine .handler (residual := []) ⟨.none, .none⟩ (.cons (port_lookup operation_known) body .nil) ?_ (by decide)
  intro operation input output known
  by_cases same : operation = 0
  · subst operation
    simp [handler, ScopedTyping.clauseKeys]
  · simp [Operations.ports, operations, same, handler] at known

theorem pending_source : Segment operations policy contracts tables [] capture .unit .unit [19] pendingRequirements resumes := by
  have body : Expression operations policy contracts [] [] binding.scope (Environment.empty.extend 99 .unit)
      (.discard 0) .unit [19] (.invoke ⟨19, .dispose⟩ [] []) :=
    .discard inner_known rfl rfl rfl (by simp [inner])
  exact .push (.plain (.bind body) (.bound (Owners.ports_lookup inner_known)) rfl rfl)
    (.live inner_known rfl rfl ⟨.none, .none⟩ rfl .nil (.push (.handler handler_typed rfl) .nil))

theorem pending_closing : Records operations policy contracts tables [] capture disposals :=
  .push (.close rfl .nil .nil .nil (.push .nil))

theorem pending_checked : Checked (resumes ++ disposals) [] (available (ownedTickets capture)) pendingRequirements [] := by
  have first : Checked (resumes ++ disposals) [] (available (ownedTickets capture))
      ((Requirements.invoke ⟨19, .dispose⟩ [] []).prepend (OwnerPhases.ofStack tables innerBoundary)) [] :=
    .invoke rfl (by decide) (by exact OwnerPhases.Consumes.hit)
      (.request (by simp [OwnerSource.exportAt, residual_empty]))
  have handlerCheck : Checked (resumes ++ disposals) [] (spendAll (available (ownedTickets capture)) [19]) handlerRequirements [] := by
    apply RecursiveRequirements.evaluate_sound
    simp [handlerRequirements, emptyRequirements, RecursiveRequirements.evaluate_sequence,
      RecursiveRequirements.evaluate_prepend, RecursiveRecomposition.evaluate_empty,
      RecursiveRecomposition.merge_empty_left, spendAll]
  have rest : Checked (resumes ++ disposals) [] (spendAll (available (ownedTickets capture)) [19]) innerRequirements [] :=
    .sequence (.spent (by decide)) handlerCheck
  exact .sequence first rest

/-- The captured pending computation genuinely needs the nested disposal
    record; retaining only resume records cannot check the requesting state. -/
theorem missing_disposal_rejected :
    ¬ Checked resumes [] (available (ownedTickets capture)) pendingRequirements row := by
  intro checked
  obtain ⟨firstRow, tailRow, first, rest, same⟩ := RecursiveRequirements.checked_sequence_parts checked
  have invocation := RecursiveRequirements.checked_prepend_iff.mp first
  obtain ⟨body, waiting, known, ready, selected, bodyCheck⟩ := RecursiveRequirements.checked_invocation invocation
  simp [resumes, RecursiveRequirements.lookup] at known

theorem request_checked : CheckedState operations policy contracts tables [] [] (.ticket 0 19)
    (.perform (Instantiation.freezeEffect effect) 0 .unit) capture .unit [19] [] := by
  have current : Expression operations policy contracts [] [effect] (.ticket 0 19) Environment.empty
      (.perform (Instantiation.freezeEffect effect) 0 .unit) .unit [] requestRequirements :=
    .perform operation_known List.mem_cons_self (.stable .unit) (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  have currentCheck : Checked (resumes ++ disposals) (OwnerPhases.ofStack tables capture)
      (available (ownedTickets capture)) requestRequirements [] :=
    .emitAfter (bodyRow := []) (requestRow := [])
      (.request (by simp [OwnerSource.exportAt, residual_empty])) (by decide)
  have prefixed : Checked (resumes ++ disposals) [] (available (ownedTickets capture))
      (requestRequirements.prepend (OwnerPhases.ofStack tables capture)) [] :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)
  exact .checked (.checked current (.bound (Owners.ports_lookup inner_known)) pending_source) pending_closing (by decide)
    (by simpa only [List.nil_append] using Checked.sequence prefixed pending_checked) (by decide)

theorem selected_cut : HandlerCut effect capture capture .nil handler :=
  .push (.plain binding) innerBoundary innerBoundary .nil handler (by decide)
    (.live 19 .unit .unit .nil .none handlerStack handlerStack .nil handler (.hit handler .nil rfl))

theorem capture_preserved : ∃ contract : Owners.Contract,
    RawStep ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .ticket 0 19, capture⟩
      ⟨clause, .ticket 1 23, boundary⟩ [.ticket 23] [] ∧
    CheckedState operations policy (contracts.insert 23 contract) tables [] [] (.ticket 1 23) clause boundary .unit [23, 19] [] := by
  obtain ⟨contract, offeredContract, offered, requestRow, tailRow, input, annotation, closing, effects,
    capturedDemand, totalRow, knownOffer, permitted, offeredRow, exported, dispatch⟩ :=
    capture_from_structural_clause request_checked selected_cut (.hit) operation_known (by trivial) (owner := 23) (by decide) []
  obtain ⟨headEmpty, tailEmpty⟩ := List.append_eq_nil_iff.mp totalRow.symm
  obtain ⟨requestEmpty, resumeEmpty⟩ := List.append_eq_nil_iff.mp headEmpty
  have answer : contract.answer = .unit := by
    change contract.answer.port = .unit at annotation
    cases same : contract.answer <;> simp_all [Value.port]
  let initial := available (ownedTickets boundary)
  have unique : (23 :: contract.resumeDemand).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, capturedDemand.nodup (by decide)⟩
    intro member
    have impossible := capturedDemand.subset member
    simp at impossible
  have transition : OwnerPhaseTransitions.Trace initial (23 :: contract.resumeDemand)
      (spendAll initial (23 :: contract.resumeDemand)) :=
    OwnerPhaseTransitions.trace_of_available unique (by
      intro owner member
      rcases List.mem_cons.mp member with same | nested
      · subst owner
        rfl
      · have only := capturedDemand.subset nested
        have same : owner = 19 := List.mem_singleton.mp only
        subst owner
        rfl)
  have known : (contracts.insert 23 contract) 23 = some contract := by simp [Owners.Contracts.insert]
  have operand : Owners.Derives operations policy (contracts.insert 23 contract)
      (OwnerPhases.ofStack tables boundary) [] (Environment.empty.extend 2 .unit) [] (.ticket 1 23)
      initial .unit initial contract.input [] [] :=
    input.symm ▸ .stable .unit (by simp [OwnerSource.exportAt, residual_empty])
  have body := Owners.Derives.resume (policy := policy) (binder := 1) known (by rfl) (by rfl) operand transition
    (effects.symm ▸ List.nil_subset []) (answer.symm ▸ (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
  have bounded : ([] : Footprint) ⊆ requestRow ++ contract.resumeRow := List.nil_subset _
  obtain ⟨step, checked, included, owned⟩ := dispatch [] (spendAll initial (23 :: contract.resumeDemand))
    (23 :: contract.resumeDemand) [] (by simpa only [input, handler, boundary, clause, initial, Value.port, ScopedPorts.embedPort, List.nil_append, resumeEmpty] using body)
    (OwnerPhaseTransitions.trace_consumed transition List.mem_cons_self) bounded
  exact ⟨contract, by simpa [clause, Code.subst, handler, boundary, Value.port, ScopedPorts.embedPort] using step,
    by simpa [tailEmpty, clause, Code.subst, handler, boundary, Value.port, ScopedPorts.embedPort] using checked⟩

def outerSpent : Stack := .spent 23 .unit .none .nil
def waiting : Stack := handlerStack.append outerSpent
def innerSpent : Stack := .spent 19 .unit .none waiting
def closingStack : Stack := .push (.closing 41 (.ticket 0 19)) innerSpent

theorem saved_continuation_finishes
    (source : CheckedState operations policy (contracts.insert 23 contract) tables [] [] (.ticket 1 23)
      clause boundary .unit [23, 19] []) :
    RawTrace ⟨clause, .ticket 1 23, boundary⟩ ⟨.unit, .none, .nil⟩ [.close 41] [.close 41, .ticket 19, .ticket 23] ∧
    CheckedState operations policy (contracts.insert 23 contract) tables [] [] .none .unit .nil .unit [] [] := by
  have closed := CallableProtection.Examples.unit_closed
  obtain ⟨remaining, resumed, same, transition⟩ := RecursiveConsumption.resume_cut_preserves (front := .nil) source rfl closed
  have remainder : remaining = [19] := (List.cons.inj same).2.symm
  have restored : CheckedState operations policy (contracts.insert 23 contract) tables [] [] (.ticket 1 23) .unit
      (capture.append outerSpent) .unit [19] [] := remainder ▸ resumed
  have plugged := RecursiveExecution.plug_preserves restored closed
  have bound : CheckedState operations policy (contracts.insert 23 contract) tables [] [] (.ticket 0 19)
      (.discard 0) (innerBoundary.append outerSpent) .unit [19] [] := RecursiveExecution.bind_preserves plugged closed
  obtain ⟨remaining, disposed, same, transition⟩ := RecursiveConsumption.discard_cut_preserves (front := .nil) bound rfl (by rfl) 41
  have empty : remaining = [] := (List.cons.inj same).2.symm
  have installed : CheckedState operations policy (contracts.insert 23 contract) tables [] [] (.ticket 0 19) .unit closingStack .unit [] [] := empty ▸ disposed
  have finished := RecursiveExecution.finish_close installed
  have innerReturned := RecursiveExecution.leave_clause finished (by trivial)
  have handlerReturned := RecursiveExecution.leave_handler innerReturned (by trivial)
  have terminal := RecursiveExecution.leave_clause handlerReturned (by trivial)
  have e0 : RawStep ⟨clause, .ticket 1 23, boundary⟩ ⟨.unit, .ticket 1 23, capture.append outerSpent⟩ [] [.ticket 23] :=
    .resume 1 23 (.ticket 1 23) .none .unit .unit .nil capture .nil .unit closed rfl
  have e1 := RawStep.plug binding .unit closed (.ticket 1 23) (innerBoundary.append outerSpent)
  have e2 := RawStep.bind 99 .unit (.discard 0) (.ticket 0 19) (innerBoundary.append outerSpent) closed
    (by simp [ClosedExcept, Code.dependencies])
  have e3 := RawStep.discard 0 19 41 (.ticket 0 19) .none .unit .unit .nil .nil waiting [] rfl rfl
  have e4 := RawStep.finishClose 41 (.ticket 0 19) (.ticket 0 19) innerSpent
  have e5 := RawStep.leaveClause 19 .unit .unit closed (.ticket 0 19) .none waiting
  have e6 := RawStep.leaveHandler handler .unit closed .none outerSpent
  have e7 := RawStep.leaveClause 23 .unit .unit closed .none .none .nil
  exact ⟨.next e0 (.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.next e7 (.refl _)))))))), terminal⟩

def initial : RunState := ⟨⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .ticket 0 19, capture⟩, [.ticket 19], []⟩
def terminal : RunState := ⟨⟨.unit, .none, .nil⟩, [.ticket 19, .ticket 23, .close 41], [.close 41, .ticket 19, .ticket 23]⟩

theorem initial_ledger : Ledger initial.erase := ⟨.refl _, by decide⟩

/-- Fresh capture, resumption, nested disposal and return form one actual run.
    Every continuation step uses the combined store constructed by capture. -/
theorem capture_through_disposal : ∃ contract : Owners.Contract,
    RunSteps initial terminal ∧
    CheckedState operations policy (contracts.insert 23 contract) tables [] [] .none .unit .nil .unit [] [] ∧
    Ledger terminal.erase ∧ terminal.completed.Nodup := by
  obtain ⟨contract, captured, source⟩ := capture_preserved
  obtain ⟨rest, returned⟩ := saved_continuation_finishes source
  have trace : RawTrace initial.configuration terminal.configuration [.ticket 23, .close 41] [.close 41, .ticket 19, .ticket 23] :=
    .next captured rest
  have run : RunSteps initial terminal := raw_trace_enacts trace (issued := [.ticket 19]) (completed := []) (by decide)
  have ledger := run_steps_preserve_ledger run initial_ledger
  exact ⟨contract, run, returned, ledger, ledger_no_double_completion ledger⟩

end Examples

end Ash.OneShot.RecursiveAllocation

#print axioms Ash.OneShot.RecursiveAllocation.lookup_add_closing
#print axioms Ash.OneShot.RecursiveAllocation.checked_add_closing
#print axioms Ash.OneShot.RecursiveAllocation.capture_segments_checked
#print axioms Ash.OneShot.RecursiveAllocation.capture_record
#print axioms Ash.OneShot.RecursiveAllocation.fresh_clause_configuration
#print axioms Ash.OneShot.RecursiveAllocation.capture_from_structural_clause

#print axioms Ash.OneShot.RecursiveAllocation.Examples.operation_known
#print axioms Ash.OneShot.RecursiveAllocation.Examples.inner_known
#print axioms Ash.OneShot.RecursiveAllocation.Examples.handler_typed
#print axioms Ash.OneShot.RecursiveAllocation.Examples.pending_source
#print axioms Ash.OneShot.RecursiveAllocation.Examples.pending_closing
#print axioms Ash.OneShot.RecursiveAllocation.Examples.pending_checked
#print axioms Ash.OneShot.RecursiveAllocation.Examples.request_checked
#print axioms Ash.OneShot.RecursiveAllocation.Examples.selected_cut
#print axioms Ash.OneShot.RecursiveAllocation.Examples.capture_preserved

#print axioms Ash.OneShot.RecursiveAllocation.Examples.saved_continuation_finishes
#print axioms Ash.OneShot.RecursiveAllocation.Examples.initial_ledger
#print axioms Ash.OneShot.RecursiveAllocation.Examples.capture_through_disposal

#print axioms Ash.OneShot.RecursiveAllocation.Examples.missing_disposal_rejected

#print axioms Ash.OneShot.RecursiveAllocation.fresh_clause_configuration_transport
#print axioms Ash.OneShot.RecursiveAllocation.fresh_substituted_clause_configuration

#print axioms Ash.OneShot.RecursiveAllocation.capture_record_with_closing

#print axioms Ash.OneShot.RecursiveAllocation.capture_record_with_template

#print axioms Ash.OneShot.RecursiveAllocation.capture_record_with_frames

#print axioms Ash.OneShot.RecursiveAllocation.allocate_split_with_frames
