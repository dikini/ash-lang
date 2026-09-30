import SourceClauseDeclarations
import RecursiveHandlerTables

/-! Retain full clause source declarations on actual typed frames. Selection and
    fresh allocation use the same full answer witness. Advertised clause bounds
    and preserved declarations in executable code remain separate obligations. -/
namespace Ash.OneShot.SourceClauseCapture
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open RecursiveRequirements (Requirements Store Checked)
open RecursiveCapture (AnnotatedSegment)
open SourceClauseDeclarations (SourceClauses Body)

/-- Source evidence at a handler is indexed by its full input/answer value.
    Other frames obtain their typing from the underlying segment judgment. -/
def FrameSource (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) : ExecFrame → Value → Value → Prop
  | .handler handler, answer, _ => ∃ allowed,
      SourceClauses operations policy contracts world Environment.empty allowed handler.effectInst answer handler.clauses (tables handler)
  | _, _, _ => True

abbrev DeclaredSegment operations policy contracts tables world :=
  AnnotatedSegment (fun entry input output _ _ => FrameSource operations policy contracts tables world entry input output) operations policy contracts tables world

theorem FrameSource.extension
    (source : FrameSource operations policy contracts tables world entry input output)
    (extension : contracts.Extends next) :
    FrameSource operations policy next tables world entry input output := by
  cases entry <;> try exact source
  case handler handler =>
    obtain ⟨allowed, clauses⟩ := source
    exact ⟨allowed, clauses.extension extension⟩

theorem FrameSource.world_weaken
    (source : FrameSource operations policy contracts tables world entry input output)
    (larger : world ⊆ next) :
    FrameSource operations policy contracts tables next entry input output := by
  cases entry <;> try exact source
  case handler handler =>
    obtain ⟨allowed, clauses⟩ := source
    exact ⟨allowed, clauses.world_weaken larger⟩

theorem declared_extension
    (source : DeclaredSegment operations policy contracts tables world stack input output demand requirements records)
    (extension : contracts.Extends next) :
    DeclaredSegment operations policy next tables world stack input output demand requirements records :=
  source.extension extension (fun _ _ _ _ _ current => current.extension extension)

theorem declared_world_weaken
    (source : DeclaredSegment operations policy contracts tables world stack input output demand requirements records)
    (larger : world ⊆ next) :
    DeclaredSegment operations policy contracts tables next stack input output demand requirements records :=
  source.world_weaken larger (fun _ _ _ _ _ current => current.world_weaken larger)

theorem FrameSource.tables_congr
    (source : FrameSource operations policy contracts first world entry input output)
    (agree : ∀ handler, handler.activation ∈ entry.erase.activation → first handler = second handler) :
    FrameSource operations policy contracts second world entry input output := by
  cases entry <;> try exact source
  case handler handler =>
    obtain ⟨allowed, clauses⟩ := source
    exact ⟨allowed, agree handler List.mem_cons_self ▸ clauses⟩

/-- Registry agreement preserves declarations in both active and dormant
    segments, using the established interpretation-context equality. -/
theorem declared_tables_congr
    (source : DeclaredSegment operations policy contracts first world stack input output demand requirements records)
    (agree : ∀ handler, handler.activation ∈ stack.erase.activations → first handler = second handler) :
    DeclaredSegment operations policy contracts second world stack input output demand requirements records :=
  RecursiveHandlerTables.annotated_segment_congr source
    (fun _ _ _ _ _ agreed current => current.tables_congr agreed) agree

theorem register_declarations
    (source : DeclaredSegment operations policy contracts tables world stack input output demand requirements records)
    (fresh : activation ∉ stack.erase.activations) :
    DeclaredSegment operations policy contracts (RecursiveHandlerTables.register tables activation clauses)
      world stack input output demand requirements records :=
  declared_tables_congr source (RecursiveHandlerTables.register_agrees fresh)

/-- Entry stores the supplied full declaration on the new handler frame. All
    previously retained declarations survive fresh table registration. -/
theorem declared_handler_entry
    (body : SourceTemplates.Expression operations policy contracts world (effect :: residual) scope Environment.empty
      code answer bodyDemand bodyRequirements)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (clausesTyped : ScopedPorts.ClausesTyped operations.ports world ScopedPorts.TypeEnv.empty effect answer.port residual clauses)
    (declaration : SourceClauses operations policy contracts world Environment.empty residual effect answer clauses table)
    (coverage : ScopedPorts.Covers operations.ports effect clauses)
    (clauseUnique : (ScopedTyping.clauseKeys clauses).Nodup)
    (pending : DeclaredSegment operations policy contracts tables world stack answer output tailDemand tailRequirements resumes)
    (closing : RecursiveRecords.Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (bodyCheck : Checked (resumes ++ disposals)
      (.ordinary (.handler effect 0 table) :: OwnerPhases.ofStack tables stack)
      (OwnerPhaseTransitions.available (ownedTickets stack)) bodyRequirements bodyRow)
    (tailCheck : Checked (resumes ++ disposals) []
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets stack)) bodyDemand) tailRequirements tailRow)
    (accepted : checkFootprint outside (bodyRow ++ tailRow) = true)
    (retained : stack.erase.activations ⊆ history) :
    ∃ handler : HandlerData, handler.activation ∉ history ∧
      RecursiveHandlerTables.register tables handler.activation table handler = table ∧
      RawStep ⟨.handle (Instantiation.freezeEffect effect) code clauses, scope, stack⟩
        ⟨code, scope, .push (.handler handler) stack⟩ [] [] ∧
      RecursiveRecords.CheckedState operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        world outside scope code (.push (.handler handler) stack) output (bodyDemand ++ tailDemand) (bodyRow ++ tailRow) ∧
      DeclaredSegment operations policy contracts (RecursiveHandlerTables.register tables handler.activation table) world
        (.push (.handler handler) stack) answer output tailDemand
        (.sequence ((Requirements.request [] []).prepend
          (OwnerPhases.ofStack (RecursiveHandlerTables.register tables handler.activation table) stack)) tailRequirements) resumes ∧
      ownedTickets (.push (.handler handler) stack) = ownedTickets stack ∧
      handler.clauses = clauses ∧ handler.effectInst = effect := by
  obtain ⟨handler, fresh, installed, step, checked, owners, clausesSame, effectSame, frame⟩ :=
    RecursiveHandlerTables.handler_entry_with_frame body scopeTyped clausesTyped coverage clauseUnique pending.erase closing unique
      bodyCheck tailCheck accepted retained
  have pendingAfter := register_declarations pending (clauses := table) (fun member => fresh (retained member))
  have current : FrameSource operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
      world (.handler handler) answer answer := by
    refine ⟨residual, ?_⟩
    simpa only [effectSame, clausesSame, installed] using declaration
  exact ⟨handler, fresh, installed, step, checked, .push current frame pendingAfter, owners, clausesSame, effectSame⟩

/-- The allocated contract supplies the selected clause's source derivation.
    No clause source premise is required after allocation. Closing ownership
    balance is obtained from the existing authenticated-record theorem. -/
theorem allocate_selected_clause
    (cut : HandlerCut requested whole capture tail handler)
    (source : DeclaredSegment operations policy contracts tables world whole input output demand requirements records)
    (closing : RecursiveRecords.Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : RecursiveClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (closeRow : Option Footprint) :
    ∃ (contract : Owners.Contract) (allowed : List Instance) (clauseDemand : List Nat)
      (clauseRequirements : Requirements clauseDemand) (capReq : Requirements contract.resumeDemand)
      (tailDemand : List Nat) (tailReq : Requirements tailDemand) (tailRow : Footprint),
      contract.input = input ∧ contract.closeDemand = OwnerClosingSource.retirements plan ∧
      contract.closeRow = closeRow ∧ contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      SourceTemplates.Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements ∧
      DeclaredSegment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailReq)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) :: records) ∧
      RecursiveRecords.Records operations policy (contracts.insert owner contract) tables world
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
  obtain ⟨allowed, clauses⟩ := declaration
  obtain ⟨declaredArgument, declaredInput, resumeEffects, closeEffects, knownOperation, family⟩ :=
    SourceClauseDeclarations.selected_family clauses clause found available
  rw [ScopedTyping.handler_cut_instance cut] at knownOperation
  have sameTypes := Prod.mk.inj (Option.some.inj (knownOperation.symm.trans operationKnown))
  rcases sameTypes with ⟨rfl, rfl⟩
  have chosen := RecursiveRecords.capture_records_with_template
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
    RecursiveAllocation.allocate_split_with_frames cut source annotation ⟨allowed, clauses⟩ saved outside
      sameDemand sameRecords sameRow (by simpa only [List.append_nil] using savedCheck) tailCheck
      unique fresh (OwnerClosingSource.retirements plan) closeRow resumeEffects closeEffects chosen keys
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
  obtain ⟨clauseDemand, clauseRequirements, clauseSource⟩ :=
    SourceClauseDeclarations.instantiate family fresh inputSame answerSame resumeSame closeSame heldSame balance
  have declarationsAfter : DeclaredSegment operations policy (contracts.insert owner contract) tables world
      (.live owner (ScopedPorts.embedPort declaredInput.port) handler.answer capture handler.scope tail)
      contract.answer output remainingDemand (.sequence (.spent owner) remainingRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) :=
    boundary.extension (fun _ _ current => current)
      (fun _ _ _ _ _ current => FrameSource.extension current (Owners.insert_extends contracts fresh))
  exact ⟨contract, allowed, clauseDemand, clauseRequirements, capturedRequirements,
    remainingDemand, remainingRequirements, remainingRow, inputSame, closeDemandSame, closeRowSame,
    balance, heldSame, clauseSource, declarationsAfter, closingAfter, demandSame, rowSame, capCheck, remainingCheck, afterUnique⟩

/-- Resume-only allocation retains declarations without constructing a closing
    plan. The unused closing demand is set equal to the actual resume demand. -/
theorem allocate_selected_without_disposal
    (cut : HandlerCut requested whole capture tail handler)
    (source : DeclaredSegment operations policy contracts tables world whole input output demand requirements records)
    (closing : RecursiveRecords.Records operations policy contracts tables world whole disposals)
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
      SourceTemplates.Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements ∧
      DeclaredSegment operations policy (contracts.insert owner contract) tables world
        (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
        contract.answer output tailDemand (.sequence (.spent owner) tailReq)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) :: records) ∧
      RecursiveRecords.Records operations policy (contracts.insert owner contract) tables world
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
  obtain ⟨allowed, clauses⟩ := declaration
  obtain ⟨declaredArgument, declaredInput, resumeEffects, closeEffects, knownOperation, family⟩ :=
    SourceClauseDeclarations.selected_family clauses clause found available
  rw [ScopedTyping.handler_cut_instance cut] at knownOperation
  have sameTypes := Prod.mk.inj (Option.some.inj (knownOperation.symm.trans operationKnown))
  rcases sameTypes with ⟨rfl, rfl⟩
  obtain ⟨nested, remaining, savedClosing, tailClosing, sameClosings⟩ :=
    RecursiveRecords.split_append (handler_cut_reconstructs cut ▸ closing)
  have chosen : RecursiveRecords.Records operations policy contracts tables world
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
    RecursiveAllocation.allocate_split_with_frames cut source annotation ⟨allowed, clauses⟩ saved outside
      sameDemand sameRecords sameRow (by simpa only [List.append_nil] using savedCheck) tailCheck
      unique fresh capDemand none resumeEffects closeEffects chosen keys
  have equalDemands : contract.closeDemand = contract.resumeDemand := closeDemandSame.trans resumeDemandSame.symm
  have balance : contract.closeDemand.Perm contract.resumeDemand := equalDemands ▸ List.Perm.refl _
  obtain ⟨clauseDemand, clauseRequirements, clauseSource⟩ :=
    SourceClauseDeclarations.instantiate family fresh inputSame answerSame resumeSame closeSame heldSame balance
  have declarationsAfter : DeclaredSegment operations policy (contracts.insert owner contract) tables world
      (.live owner (ScopedPorts.embedPort declaredInput.port) handler.answer capture handler.scope tail)
      contract.answer output remainingDemand (.sequence (.spent owner) remainingRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) :=
    boundary.extension (fun _ _ current => current)
      (fun _ _ _ _ _ current => FrameSource.extension current (Owners.insert_extends contracts fresh))
  exact ⟨contract, allowed, clauseDemand, clauseRequirements, capturedRequirements,
    remainingDemand, remainingRequirements, remainingRow, inputSame, equalDemands, closeRowSame,
    balance, heldSame, clauseSource, declarationsAfter, closingAfter, demandSame, rowSame, capCheck, remainingCheck, afterUnique⟩

/-- A checked disposal would supply a plan and internal-use proof for the
    selected capture. Either structural unavailability witness contradicts it. -/
theorem unavailable_disposal_rejected
    (source : SourceTemplates.Segment operations policy contracts tables world
      (.live owner input answer capture caller tail) result output demand requirements resumes)
    (closing : RecursiveRecords.Records operations policy contracts tables world
      (.live owner input answer capture caller tail) disposals)
    (unique : (ownedTickets (.live owner input answer capture caller tail)).Nodup)
    (unavailable : makePlan capture = none ∨ ¬ InternalUses capture.erase.liveTickets capture.erase.pending) :
    ¬ Checked (resumes ++ disposals) receiving before (.invoke ⟨owner, .dispose⟩ nested nearer) row := by
  intro checked
  obtain ⟨body, waiting, known, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation checked
  obtain ⟨plan, raw, requirements, built, internal, same, template⟩ :=
    RecursiveRecords.certified_selected (RecursiveRecords.lookup_certified source closing known) unique
      SourceTemplates.ActiveCapture.here
  rcases unavailable with blocked | external
  · rw [blocked] at built; cases built
  · exact external internal

/-- Full clause typing comes from the retained declaration. The remaining
    certificate premises concern only structural upper effect bounds. -/
theorem capture_with_upper_certificate
    (cut : HandlerCut requested whole capture tail handler)
    (source : DeclaredSegment operations policy contracts tables world whole input output demand requirements records)
    (closing : RecursiveRecords.Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (capabilities : ClausesUse policy handler.clauses)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourceTemplates.ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (offeredAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) offeredRow = true)
    (pendingAccepted : checkFootprint outside row = true)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : RecursiveClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (closingBound : EffectBounds.Covers upperClosing raw)
    (closingAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) upperClosing = true) :
    ∃ (contract : Owners.Contract) (allowed : List Instance) (clauseDemand : List Nat)
      (clauseRequirements : Requirements clauseDemand) (store : Store) (tailDemand : List Nat) (tailRow closingRow requestRow : Footprint),
      ProtectionResiduals.residualize (CallableProtectionFrames.contextOf tables tail) offeredRow = some requestRow ∧
      contract.input = input ∧ contract.closeRow = some closingRow ∧
      ProtectionResiduals.residualize (CallableProtectionFrames.contextOf tables tail) raw = some closingRow ∧
      checkFootprint outside closingRow = true ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      SourceTemplates.Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) closingRow ∧
      ∀ (upperRequirements : Requirements clauseDemand) (upperStore : Store) (upperRow : Footprint),
        RecursiveBounds.StoreBounds store upperStore →
        RecursiveBounds.Bounds clauseRequirements upperRequirements →
        Checked upperStore
          (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
          (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          upperRequirements upperRow →
        upperRow ⊆ (requestRow ++ contract.resumeRow) →
        ∃ clauseRow,
          RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
            ⟨body.subst parameter operand, .ticket binder owner,
              .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
          RecursiveRecords.CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
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
    inputSame, closeDemandSame, closeRowSame, balance, heldSame, clauseSource, boundary, closingAfter,
    demandSame, rowSame, capCheck, tailCheck, afterUnique⟩ :=
    allocate_selected_clause cut source closing checked unique fresh clause operationKnown found available
      built internal template (some closingRow)
  let store : Store := (⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) ::
    (records ++ ([(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)] ++ disposals))
  have phases := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.port)
    cut (RecursiveCapture.fresh_unowned source.erase fresh)
  have resumeCheck := RecursiveClauses.fresh_resume_check capCheck phases
  have templateAfter := RecursiveRecords.template_extension template (Owners.insert_extends (contract := contract) contracts fresh)
  have looked : RecursiveRequirements.lookup ⟨owner, .dispose⟩ store =
      some ⟨OwnerClosingSource.retirements plan, closingRequirements⟩ := by
    change RecursiveRequirements.lookup ⟨owner, .dispose⟩
      (((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) :: records) ++
        ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals)) = _
    rw [RecursiveDisposalCapture.lookup_after_resumes (fun key body member => RecursiveRecords.resume_mode boundary.erase member)]
    simp [RecursiveRequirements.lookup]
  have disposeCheck := RecursiveDisposalCapture.closing_invocation_from_record templateAfter looked afterUnique built
    (RecursivePlanAdmission.captured_evaluation templateAfter built afterUnique closingExport)
  rw [← closeDemandSame] at disposeCheck
  refine ⟨contract, allowed, clauseDemand, clauseRequirements, store, tailDemand, tailRow, closingRow, requestRow, requestExport,
    inputSame, closeRowSame, closingExport, closingAllowed, balance, clauseSource, resumeCheck, disposeCheck, ?_⟩
  intro upperRequirements upperStore upperRow storeBound requirementsBound upperChecked upperBound
  obtain ⟨clauseRow, clauseCheck, covered⟩ := RecursiveBounds.checked_below upperChecked storeBound requirementsBound
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have payloadAfter := (payload.change_allowed closed.1 allowed).extension
    (Owners.insert_extends (contract := contract) contracts fresh)
  have current := SourceCallableSubstitution.substitution clauseSource payloadAfter closed
  have completed := RecursiveClauseUsage.declared_clause_completed clause capabilities clauseSource clauseCheck
  have included : (clauseRow ++ tailRow) ⊆ (requestRow ++ row) := by
    rw [rowSame, ← List.append_assoc]
    exact ScopedExpressions.append_subset (EffectBounds.covers_trans upperBound covered) (List.Subset.refl _)
  have result := RecursiveClauseOwnership.fresh_clause_configuration known boundary.erase closingAfter capCheck tailCheck
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

/-- A capture without disposal still admits a declared one-shot clause from its
    upper certificate. Its absent disposal capability is proved separately. -/
theorem capture_without_disposal_with_upper_certificate
    (cut : HandlerCut requested whole capture tail handler)
    (source : DeclaredSegment operations policy contracts tables world whole input output demand requirements records)
    (closing : RecursiveRecords.Records operations policy contracts tables world whole disposals)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets whole)) requirements row)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (capabilities : ClausesUse policy handler.clauses)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourceTemplates.ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some offeredRow)
    (offeredAccepted : checkFootprint (CallableProtectionFrames.contextOf tables tail ++ outside) offeredRow = true)
    (pendingAccepted : checkFootprint outside row = true)
    (unavailable : makePlan capture = none ∨ ¬ InternalUses capture.erase.liveTickets capture.erase.pending) :
    ∃ (contract : Owners.Contract) (allowed : List Instance) (clauseDemand : List Nat)
      (clauseRequirements : Requirements clauseDemand) (store : Store) (tailDemand : List Nat) (tailRow requestRow : Footprint),
      ProtectionResiduals.residualize (CallableProtectionFrames.contextOf tables tail) offeredRow = some requestRow ∧
      contract.input = input ∧ contract.closeRow = none ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      SourceTemplates.Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      (∀ nested nearer row, ¬ Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .dispose⟩ nested nearer) row) ∧
      ∀ (upperRequirements : Requirements clauseDemand) (upperStore : Store) (upperRow : Footprint),
        RecursiveBounds.StoreBounds store upperStore →
        RecursiveBounds.Bounds clauseRequirements upperRequirements →
        Checked upperStore
          (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
          (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          upperRequirements upperRow →
        upperRow ⊆ (requestRow ++ contract.resumeRow) →
        ∃ clauseRow,
          RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
            ⟨body.subst parameter operand, .ticket binder owner,
              .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
          RecursiveRecords.CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
            (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
            output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
          (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
          (clauseRow ++ tailRow) ⊆ (requestRow ++ row) ∧
          ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  obtain ⟨requestRow, requestExport, requestAccepted⟩ := ProtectionResiduals.residual_admitted_iff.mp offeredAccepted
  have accepted : checkFootprint outside (requestRow ++ row) = true := by
    rw [check_footprint_append, requestAccepted, pendingAccepted]; rfl
  obtain ⟨contract, allowed, clauseDemand, clauseRequirements, capReq, tailDemand, tailReq, tailRow,
    inputSame, closeDemandSame, closeRowSame, balance, heldSame, clauseSource, boundary, closingAfter,
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
    exact unavailable_disposal_rejected boundary.erase closingAfter afterUnique unavailable
  · intro upperRequirements upperStore upperRow storeBound requirementsBound upperChecked upperBound
    obtain ⟨clauseRow, clauseCheck, covered⟩ := RecursiveBounds.checked_below upperChecked storeBound requirementsBound
    have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
    have payloadAfter := (payload.change_allowed closed.1 allowed).extension
      (Owners.insert_extends (contract := contract) contracts fresh)
    have current := SourceCallableSubstitution.substitution clauseSource payloadAfter closed
    have completed := RecursiveClauseUsage.declared_clause_completed clause capabilities clauseSource clauseCheck
    have included : (clauseRow ++ tailRow) ⊆ (requestRow ++ row) := by
      rw [rowSame, ← List.append_assoc]
      exact ScopedExpressions.append_subset (EffectBounds.covers_trans upperBound covered) (List.Subset.refl _)
    have result := RecursiveClauseOwnership.fresh_clause_configuration known boundary.erase closingAfter capCheck tailCheck
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

/-- A value operand contributes no effects or ownership demand. Reuse its
    existing evaluation theorem to construct an immediate-resume certificate. -/
theorem resume_value_certificate
    (source : SourceTemplates.Expression operations policy contracts world allowed (.ticket binder owner)
      environment (.resume binder value) result demand requirements)
    (isValue : value.IsValue) (known : contracts owner = some contract)
    (invocation : Checked store receiving before (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow) :
    Checked store receiving before requirements contract.resumeRow := by
  cases source with
  | stable summary => cases summary
  | callable summary => cases summary
  | resume actual resolved permission operand admitted formed =>
      have sameOwner := RecursiveClauses.resolved_owner resolved
      subst_vars
      have sameContract := Option.some.inj (actual.symm.trans known)
      cases sameContract
      have empty := SourceTemplates.expression_value_demand operand isValue
      have operandCheck := RecursiveRequirements.evaluate_sound
        (RecursiveRecomposition.value_evaluation (store := store) (receiving := receiving) (before := before) operand isValue)
      have checked := Checked.sequence operandCheck
        (by simpa only [empty, OwnerPhaseTransitions.spendAll] using invocation)
      simpa only [List.nil_append] using checked

namespace Examples
open SharedSourceSegments.Examples (operations policy contracts tables handler plain capture effect operation_known handler_typed selected_cut)

theorem family : Body operations policy contracts [] Environment.empty [] 2 7 .unit .integer .boolean [] [] held
    (.resume 7 (.integer 17)) := by
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have operand : SourceTemplates.Expression operations policy (contracts.insert owner contract) [] [] (.ticket 7 owner)
      (Environment.empty.extend 2 .unit) (.integer 17) contract.input [] (.request [] []) :=
    inputSame.symm ▸ .stable .integer
  have source := SourceTemplates.Expression.resume (binder := 7) known (by simp [Execution.Scope.resolve]) rfl operand
    (resumeSame.symm ▸ List.Subset.refl [])
    (answerSame.symm ▸ (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
  exact ⟨_, _, answerSame ▸ source⟩

theorem declaration : SourceClauses operations policy contracts [] Environment.empty [] effect .boolean handler.clauses (tables handler) :=
  .cons operation_known (.available family) (.available family) .nil

theorem retained : DeclaredSegment operations policy contracts tables [] capture .integer .boolean []
    RecursiveCapture.Examples.captureRequirements [] := by
  have context : SourceTemplates.Context operations policy contracts [] Environment.empty [] .none
      (.bind 8 (.boolean true)) .integer .boolean [] (.request [] []) := .bind (.stable .boolean)
  exact .push True.intro (.plain (plain := plain) context .none rfl rfl)
    (.push ⟨[], declaration⟩ (.handler handler_typed rfl) .nil)

theorem allocated_clause_source : ∃ (contract : Owners.Contract) (allowed : List Instance) (demand : List Nat)
    (requirements : Requirements demand),
    contract.input = .integer ∧ contract.closeDemand.Perm contract.resumeDemand ∧
    SourceTemplates.Expression operations policy (contracts.insert 29 contract) [] allowed (.ticket 7 29)
      (Environment.empty.extend 2 .unit) (.resume 7 (.integer 17)) contract.answer demand requirements := by
  obtain ⟨contract, allowed, demand, requirements, capReq, tailDemand, tailReq, tailRow,
    inputSame, closeDemandSame, closeRowSame, balance, heldSame, source, rest⟩ :=
    allocate_selected_clause selected_cut retained (.push (.push .nil))
      RecursiveCapture.Examples.captured_check (by decide) (owner := 29) (by decide)
      ClauseAt.hit operation_known (by rfl) (offeredRow := []) (by rfl)
      (plan := []) (by rfl) (by constructor <;> decide) RecursiveClosing.PlanTemplate.nil (some [])
  exact ⟨contract, allowed, demand, requirements, inputSame, balance, source⟩

/-- The actual upper certificate is constructed from the authenticated saved
    invocation; the result includes the runtime capture step and checked state. -/
theorem declared_capture_steps : ∃ (contract : Owners.Contract) (demand : List Nat) (row : Footprint),
    RawStep ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none, capture⟩
      ⟨.resume 7 (.integer 17), .ticket 7 29,
        .live 29 .integer handler.answer capture handler.scope .nil⟩ [.ticket 29] [] ∧
    RecursiveRecords.CheckedState operations policy (contracts.insert 29 contract) tables [] [] (.ticket 7 29)
      (.resume 7 (.integer 17)) (.live 29 .integer handler.answer capture handler.scope .nil) .boolean demand row := by
  obtain ⟨contract, allowed, clauseDemand, clauseRequirements, store, tailDemand, tailRow, closingRow, requestRow,
    exported, inputSame, closeSame, closingExport, closingAccepted, balance, current, resumed, disposed, enter⟩ :=
    capture_with_upper_certificate (scope := .none) (outside := []) selected_cut retained (.push (.push .nil))
      RecursiveCapture.Examples.captured_check (by decide) (owner := 29) (by decide)
      ClauseAt.hit (.cons (.resume rfl .integer) .nil) operation_known
      (SourceTemplates.ValueSummary.stable (allowed := []) .unit) ScopedExecution.Examples.unit_closed
      (by rfl) (offeredRow := []) (by rfl) (by rfl) (by rfl)
      (plan := []) (by rfl) (by constructor <;> decide) RecursiveClosing.PlanTemplate.nil
      (EffectBounds.covers_refl []) (by rfl)
  have requestEmpty : requestRow = [] := Option.some.inj exported.symm
  have known : (contracts.insert 29 contract) 29 = some contract := by simp [Owners.Contracts.insert]
  have certificate := resume_value_certificate current trivial known resumed
  obtain ⟨clauseRow, step, after, ownership, covered, tickets⟩ :=
    enter clauseRequirements store contract.resumeRow (RecursiveBounds.store_refl store)
      (RecursiveBounds.bounds_refl clauseRequirements) certificate
      (by simpa only [requestEmpty, List.nil_append] using List.Subset.refl contract.resumeRow)
  exact ⟨contract, clauseDemand ++ tailDemand, clauseRow ++ tailRow, step, after⟩

def cleanupCallback : Code := .lambda 0 .unit

theorem cleanup_callback_source : Summary operations [] Environment.empty [] cleanupCallback (.function .unit .unit [] []) [] :=
  .lambda .unit (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

def cleanupAction : ActionData := ⟨43, cleanupCallback,
  ScopedPorts.typed_value_closed (CoherentSourceTypes.port_typing cleanup_callback_source .none) trivial,
  .none, .boolean, []⟩

theorem saved_boolean_closed : ClosedValue (.boolean true) := ⟨trivial, rfl, by intro dependency member; cases member⟩

def cleanupPlain : PlainData := ⟨.bind 8 .unit, .none, .integer, .unit, [], rfl⟩
def guardedTail : Stack := .push (.handler handler) .nil
def guardedMiddle : Stack := .push (.running cleanupAction (.boolean true) saved_boolean_closed) guardedTail
def guardedCapture : Stack := .push (.plain cleanupPlain) guardedMiddle

def guardedRequirements : Requirements [] :=
  .sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables guardedMiddle))
    (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables guardedTail))
      RecursiveCapture.Examples.handlerRequirements)

theorem guarded_source : DeclaredSegment operations policy contracts tables [] guardedCapture .integer .boolean [] guardedRequirements [] := by
  have context : SourceTemplates.Context operations policy contracts [] Environment.empty [] .none
      (.bind 8 .unit) .integer .unit [] (.request [] []) := .bind (.stable .unit)
  exact .push True.intro (.plain (plain := cleanupPlain) context .none rfl rfl)
    (.push True.intro (.running (action := cleanupAction) ⟨.none, .none⟩ (.stable cleanup_callback_source) (.stable .boolean) rfl)
      (.push ⟨[], declaration⟩ (.handler handler_typed rfl) .nil))

theorem guarded_checked : Checked [] receiving before guardedRequirements [] := by
  apply RecursiveRequirements.evaluate_sound
  simp only [guardedRequirements, RecursiveCapture.Examples.handlerRequirements,
    RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
    RecursiveRecomposition.evaluate_empty, ProtectionResiduals.merge, List.nil_append]

theorem guarded_cut : HandlerCut effect guardedCapture guardedCapture .nil handler :=
  .push (.plain cleanupPlain) guardedMiddle guardedMiddle .nil handler (by decide)
    (.push (.running cleanupAction (.boolean true) saved_boolean_closed) guardedTail guardedTail .nil handler (by decide)
      (.hit handler .nil rfl))

theorem guarded_unclosable : makePlan guardedCapture = none ∧ ProtectionContexts.protectedMode guardedCapture.erase = true := by decide

/-- An operation during cleanup can capture and resume through its running
    callback frame. The same captured continuation has no checked disposal. -/
theorem guarded_capture_steps : ∃ (contract : Owners.Contract) (store : Store) (demand : List Nat) (row : Footprint),
    contract.closeRow = none ∧
    (∀ nested nearer row, ¬ Checked store
      (OwnerPhases.ofStack tables (.live 29 .integer handler.answer guardedCapture handler.scope .nil))
      (OwnerPhaseTransitions.available (ownedTickets (.live 29 .integer handler.answer guardedCapture handler.scope .nil)))
      (.invoke ⟨29, .dispose⟩ nested nearer) row) ∧
    RawStep ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none, guardedCapture⟩
      ⟨.resume 7 (.integer 17), .ticket 7 29,
        .live 29 .integer handler.answer guardedCapture handler.scope .nil⟩ [.ticket 29] [] ∧
    RecursiveRecords.CheckedState operations policy (contracts.insert 29 contract) tables [] [] (.ticket 7 29)
      (.resume 7 (.integer 17)) (.live 29 .integer handler.answer guardedCapture handler.scope .nil) .boolean demand row := by
  obtain ⟨contract, allowed, clauseDemand, clauseRequirements, store, tailDemand, tailRow, requestRow,
    exported, inputSame, closeSame, balance, current, resumed, denied, enter⟩ :=
    capture_without_disposal_with_upper_certificate (scope := .none) (outside := []) guarded_cut guarded_source
      (.push (.push (.push .nil))) guarded_checked (by decide) (owner := 29) (by decide)
      ClauseAt.hit (.cons (.resume rfl .integer) .nil) operation_known
      (SourceTemplates.ValueSummary.stable (allowed := []) .unit) ScopedExecution.Examples.unit_closed
      (by rfl) (offeredRow := []) (by rfl) (by rfl) (by rfl) (Or.inl guarded_unclosable.1)
  have requestEmpty : requestRow = [] := Option.some.inj exported.symm
  have known : (contracts.insert 29 contract) 29 = some contract := by simp [Owners.Contracts.insert]
  have certificate := resume_value_certificate current trivial known resumed
  obtain ⟨clauseRow, step, after, ownership, covered, tickets⟩ :=
    enter clauseRequirements store contract.resumeRow (RecursiveBounds.store_refl store)
      (RecursiveBounds.bounds_refl clauseRequirements) certificate
      (by simpa only [requestEmpty, List.nil_append] using List.Subset.refl contract.resumeRow)
  exact ⟨contract, store, clauseDemand ++ tailDemand, clauseRow ++ tailRow, closeSame, denied, step, after⟩

theorem guarded_capture_then_resume : ∃ (contract : Owners.Contract) (consumed : Nat) (restored : Stack)
    (remaining : List Nat) (row : Footprint),
    contract.closeRow = none ∧
    RawStep ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none, guardedCapture⟩
      ⟨.resume 7 (.integer 17), .ticket 7 29,
        .live 29 .integer handler.answer guardedCapture handler.scope .nil⟩ [.ticket 29] [] ∧
    RawStep ⟨.resume 7 (.integer 17), .ticket 7 29,
        .live 29 .integer handler.answer guardedCapture handler.scope .nil⟩
      ⟨.integer 17, .ticket 7 29, restored⟩ [] [.ticket consumed] ∧
    RecursiveRecords.CheckedState operations policy (contracts.insert 29 contract) tables [] [] (.ticket 7 29)
      (.integer 17) restored .boolean remaining row := by
  obtain ⟨contract, store, demand, row, closeSame, denied, captured, checked⟩ := guarded_capture_steps
  have closed : ClosedValue (.integer 17) := ⟨trivial, rfl, by intro dependency member; cases member⟩
  obtain ⟨consumed, restored, remaining, resumed, after, demandSame, ownership⟩ :=
    RecursiveConsumption.resume_preserves checked closed
  exact ⟨contract, consumed, restored, remaining, row, closeSame, captured, resumed, after⟩

end Examples

namespace EntryExamples
open SourceCallableExamples (operations policy contracts effect function functionType function_value_summary operation_known)
open SourceClauseDeclarations.Examples (clauses table source_declaration)

def tables : CallableProtectionFrames.Tables := fun _ => []

theorem clause_ports : ScopedPorts.ClausesTyped operations.ports [] ScopedPorts.TypeEnv.empty
    effect functionType.port [] clauses := by
  let model : Owners.Contract := ⟨.unit, functionType, false, [], [], [], some [], [], []⟩
  obtain ⟨demand, requirements, source⟩ := SourceClauseDeclarations.instantiate
    (SourceClauseDeclarations.Examples.body_family (held := false)) (contract := model) (owner := 29)
    (by rfl) rfl rfl rfl rfl rfl (List.Perm.refl [])
  have known : (contracts.insert 29 model) 29 = some model := by simp [Owners.Contracts.insert]
  have typed := SourceTemplates.expression_ports source (ScopedPorts.EffectScope.bound (Owners.ports_lookup known))
  have environmentSame : CoherentSourceTypes.Environment.empty.ports = ScopedPorts.TypeEnv.empty := by
    funext name; rfl
  rw [ports_extend, environmentSame] at typed
  refine .cons (port_lookup operation_known) ?_ .nil
  simpa only [model, Owners.Contract.ports] using typed

theorem coverage : ScopedPorts.Covers operations.ports effect clauses := by
  intro operation input output known
  by_cases same : operation = 0
  · simp [same, clauses, ScopedTyping.clauseKeys]
  · simp [Operations.ports, SourceCallableExamples.operations, same] at known

/-- Installation preserves a full function answer and its clause family. The
    function body itself contains a computational handler. -/
theorem install_function_answer : ∃ handler : HandlerData,
    RawStep ⟨.handle (Instantiation.freezeEffect effect) function clauses, .none, .nil⟩
      ⟨function, .none, .push (.handler handler) .nil⟩ [] [] ∧
    RecursiveRecords.CheckedState operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
      [] [] .none function (.push (.handler handler) .nil) functionType [] [] ∧
    DeclaredSegment operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
      [] (.push (.handler handler) .nil) functionType functionType []
      (.sequence (.request [] []) (.request [] [])) [] := by
  have body := (function_value_summary.change_allowed trivial [effect]).expression Execution.Scope.none
  obtain ⟨handler, fresh, installed, step, checked, declared, owners, clausesSame, effectSame⟩ :=
    declared_handler_entry (history := []) (outside := []) (tables := tables) body ScopedPorts.EffectScope.none
      clause_ports source_declaration coverage (by decide) AnnotatedSegment.nil RecursiveRecords.Records.nil
      (by decide) (bodyRow := []) (tailRow := [])
      (.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty]))
      (.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty]))
      (by rfl) (by intro activation member; cases member)
  exact ⟨handler, step, checked, declared⟩

end EntryExamples

end Ash.OneShot.SourceClauseCapture
#print axioms Ash.OneShot.SourceClauseCapture.FrameSource.extension
#print axioms Ash.OneShot.SourceClauseCapture.FrameSource.world_weaken
#print axioms Ash.OneShot.SourceClauseCapture.declared_extension
#print axioms Ash.OneShot.SourceClauseCapture.declared_world_weaken
#print axioms Ash.OneShot.SourceClauseCapture.allocate_selected_clause

#print axioms Ash.OneShot.SourceClauseCapture.Examples.family
#print axioms Ash.OneShot.SourceClauseCapture.Examples.declaration
#print axioms Ash.OneShot.SourceClauseCapture.Examples.retained
#print axioms Ash.OneShot.SourceClauseCapture.Examples.allocated_clause_source

#print axioms Ash.OneShot.SourceClauseCapture.capture_with_upper_certificate

#print axioms Ash.OneShot.SourceClauseCapture.resume_value_certificate
#print axioms Ash.OneShot.SourceClauseCapture.Examples.declared_capture_steps

#print axioms Ash.OneShot.SourceClauseCapture.allocate_selected_without_disposal
#print axioms Ash.OneShot.SourceClauseCapture.unavailable_disposal_rejected

#print axioms Ash.OneShot.SourceClauseCapture.capture_without_disposal_with_upper_certificate

#print axioms Ash.OneShot.SourceClauseCapture.Examples.cleanup_callback_source
#print axioms Ash.OneShot.SourceClauseCapture.Examples.saved_boolean_closed
#print axioms Ash.OneShot.SourceClauseCapture.Examples.guarded_source
#print axioms Ash.OneShot.SourceClauseCapture.Examples.guarded_checked
#print axioms Ash.OneShot.SourceClauseCapture.Examples.guarded_cut
#print axioms Ash.OneShot.SourceClauseCapture.Examples.guarded_unclosable
#print axioms Ash.OneShot.SourceClauseCapture.Examples.guarded_capture_steps

#print axioms Ash.OneShot.SourceClauseCapture.Examples.guarded_capture_then_resume

#print axioms Ash.OneShot.SourceClauseCapture.FrameSource.tables_congr
#print axioms Ash.OneShot.SourceClauseCapture.declared_tables_congr
#print axioms Ash.OneShot.SourceClauseCapture.register_declarations
#print axioms Ash.OneShot.SourceClauseCapture.declared_handler_entry

#print axioms Ash.OneShot.SourceClauseCapture.EntryExamples.clause_ports
#print axioms Ash.OneShot.SourceClauseCapture.EntryExamples.coverage
#print axioms Ash.OneShot.SourceClauseCapture.EntryExamples.install_function_answer
