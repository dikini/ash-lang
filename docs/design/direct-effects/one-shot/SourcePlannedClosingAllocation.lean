import SourcePlannedClosingRecords

/-! Actual allocation uses the closing template extracted from joint source.
Its exact requirement body supplies the allocated disposal record and retains
strong callback source under the same refined contract as the live stack.
Scheduling and the complete runtime preservation theorem remain separate. -/
namespace Ash.OneShot.SourcePlannedClosingAllocation
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (lookupDependencies modeDependencies)
open SourceDependencySchemes
open SourcePlannedCheckedAllocationData (CaptureData)
open SourcePlannedClosingAllocationData (Certificate capture_closing)

/-- The allocation result retains all existing record, ownership and row
checks, and recovers the stronger clause under that exact contract extension. -/
theorem allocate {hints : SourceContextualHints.Hints wholeScope}
    (operations : SourcePlannedTyping.Operations) (contracts : SourcePlannedTyping.Contracts)
    (argument input : SourcePlannedTyping.Value)
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourcePlannedCheckedFrames.Segment operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets whole)) world
      whole input output demand requirements records hints .nil incoming outgoing)
    (request : SourcePlannedChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world
      (.request (effect := requested) (operation := operation)) hints)
    (compatible : SourceContextualHintChecking.Compatible hints .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourcePlannedSources.ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (layout : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world whole disposals)
    (closingRecords : SourcePlannedClosingRecords.Records operations policy contracts tables annotations world whole disposals)
    (annotationBound : Closing.Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (pendingCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (OwnerPhaseTransitions.available (ownedTickets whole)) requirements pendingRow)
    (unique : (ownedTickets whole).Nodup)
    (requestCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables whole)
      (OwnerPhaseTransitions.available (ownedTickets whole))
      (.request [] [⟨requested, operation, false⟩]) requestRow) :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capScope tailScope : Receiving) (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies) (captureRow tailRow raw : Footprint)
      (closingRequirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan)),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
        ⟨code.subst parameter operand, .ticket binder owner,
          .live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
      ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) =
        owner :: ownedTickets whole ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)).Nodup ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)))
        world (family owner) (.live owner capScope tailScope) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)))
        world (.live owner capScope tailScope) .nil ∧
      CaptureData operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing
        answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq ∧
      Certificate operations policy contracts tables world plan capScope raw closingRequirements ∧
      pendingRow = captureRow ++ tailRow ∧
      RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
        (OwnerPhaseTransitions.available (ownedTickets whole)) capReq captureRow ∧
      RecursiveRequirements.Checked (records ++ disposals) []
        (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow ∧
      (OwnerClosingSource.retirements plan).Perm capDemand ∧
      let closeRow := RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
        (OwnerPhaseTransitions.available (ownedTickets whole)) closingRequirements;
      let contract : SourceDependencyAnnotations.Contract := ⟨input.erase, answer, capScope.held,
          capDemand, captureRow, OwnerClosingSource.retirements plan, closeRow, resumeEffects, closeEffects⟩;
        (∃ refinedAnswer : SourcePlannedTyping.Value, ∃ bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner),
          ∃ (saved : SourceContextualHints.Hints capScope) (waiting : SourceContextualHints.Hints tailScope),
          refinedAnswer.erase = answer ∧ (SourcePlannedSources.refineContract contract input refinedAnswer).erase = contract ∧
          SourcePlannedChecks.Local outward (actions.insert owner code.requiredActions)
            (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
            (bodies owner) (.live (owner := owner) saved waiting) ∧
          SourcePlannedSources.Body operations policy
            (contracts.insert owner (SourcePlannedSources.refineContract contract input refinedAnswer)) world residual
            (.ticket binder owner) (fun _ => none) (code.subst parameter operand) refinedAnswer
            ⟨owner, contract.erase, offered.dispose, row⟩ (SourcePlanSignatures.signature (bodies owner)) ∧
          SourcePlannedCheckedFrames.Segment operations policy
            (contracts.insert owner (SourcePlannedSources.refineContract contract input refinedAnswer)) tables families required
            (actions.insert owner code.requiredActions) outward
            (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
            (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
            refinedAnswer output tailDemand (.sequence (.spent owner) tailReq)
            ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live (owner := owner) saved waiting) .nil residual outgoing ∧
          Certificate operations policy (contracts.insert owner (SourcePlannedSources.refineContract contract input refinedAnswer))
            tables world plan capScope raw closingRequirements ∧
          SourcePlannedClosingRecords.Records operations policy
            (contracts.insert owner (SourcePlannedSources.refineContract contract input refinedAnswer)) tables
            (fun other => if other = owner then some capScope else annotations other) world
            (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals)) ∧
        SourceDependencyAnnotations.Body operations.erase policy (contracts.erase.insert owner contract) world residual (.ticket binder owner)
          SourceDependencyAnnotations.Environment.empty (code.subst parameter operand) answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) ∧
        SourceDependencyFrames.Segment operations.erase policy (contracts.erase.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world
          (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
          answer output.erase tailDemand (.sequence (.spent owner) tailReq)
          ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live owner capScope tailScope) residual outgoing ∧
        let nextAnnotations := fun other => if other = owner then some capScope else annotations other;
        Closing.Bound nextAnnotations (.live owner capScope tailScope) ∧
          Closing.Template operations.erase policy (contracts.erase.insert owner contract) tables world .none
            plan raw closingRequirements capScope.forClosing ∧
          DeclaredSourceClosing.Records operations.erase.erase policy (contracts.erase.insert owner contract).erase tables world
            (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          Closing.Records operations.erase policy (contracts.erase.insert owner contract) tables nextAnnotations world
            (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          let store := ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals);
          RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail)
            (OwnerPhaseTransitions.available (ownedTickets whole)) capReq captureRow ∧
          RecursiveRequirements.Checked store []
            (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow ∧
          RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)))
            (.invoke ⟨owner, .resume⟩ capDemand []) captureRow ∧
          (∀ closingRow, closeRow = some closingRow → RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)))
            (.invoke ⟨owner, .dispose⟩ (OwnerClosingSource.retirements plan) []) closingRow) ∧
          ((offered.dispose = true → DeclaredCallbackAdmission.checkClosing (CallableProtectionFrames.contextOf tables tail) outside
            raw (requestRow ++ captureRow) = true) →
            ∃ (clauseDemand : List Nat) (clauseRequirements : RecursiveRequirements.Requirements clauseDemand) (clauseRow : Footprint),
              SourceDependencyAnnotations.Expression operations.erase policy (contracts.erase.insert owner contract) world residual
                (.ticket binder owner) SourceDependencyAnnotations.Environment.empty (code.subst parameter operand)
                answer clauseDemand clauseRequirements (family owner) ∧
              RecursiveRequirements.Checked store
                (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail))
                (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)))
                clauseRequirements clauseRow ∧
              EffectBounds.Covers (requestRow ++ captureRow) clauseRow) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    resumeEffects, closeEffects, family, savedHints, waitingHints, annotation, scopeKnown, declaration, saved, waiting,
    scopeSame, hintsSame, demandSame, recordsSame, resume, close, located, typed, evaluation⟩ :=
    SourcePlannedCheckedInterfaces.capture_interfaces cut source request compatible selected found available operationKnown freshContract freshAction
  have data := CaptureData.checked annotation scopeKnown saved waiting recordsSame resume close typed
  obtain ⟨checked, retained⟩ := data.clause.erase_checks
  have oldFresh : contracts.erase owner = none := by simp [SourcePlannedTyping.Contracts.erase, freshContract]
  have oldPayload : SourceDependencyAnnotations.ValueSummary operations.erase policy contracts.erase world
      SourceDependencyAnnotations.Environment.empty payloadAllowed operand argument.erase := by
    have erased := SourcePlannedSources.expression_erase payload
    have emptyErasure : SourcePlannedTyping.Environment.erase (fun _ => none) = SourceDependencyAnnotations.Environment.empty := rfl
    rw [emptyErasure] at erased
    exact erased
  have result := SourceDependencySchemes.allocate_capture_source_from_closing_interfaces
    (outside := outside) (caller := caller)
    (closingCertificate := fun _ _ _ capScope _ _ _ _ _ _ _ => Certificate operations policy contracts tables world plan capScope)
    (certificate := fun answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq =>
      CaptureData operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing
        answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    cut source.source.erase
    ⟨answer.erase, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
      resumeEffects, closeEffects, family, annotation, scopeKnown, declaration.erase.erase.source, saved.source.erase, waiting.source.erase, scopeSame, demandSame,
      recordsSame, resume, close, located, checked, retained, data, evaluation,
      fun contract fresh inputSame answerSame resumeSame closeSame heldSame balance =>
        data.clause.erase_body contract fresh inputSame answerSame resumeSame closeSame heldSame balance⟩
    (by
      intro answer residual capDemand capReq capRecords capScope saved family tailScope resumeEffects closeEffects tailDemand tailReq data
      exact capture_closing data built)
    selected found available (SourcePlannedSources.operation_erase operationKnown) oldPayload closed oldFresh freshAction layout closingRecords.erase
    annotationBound freshAnnotation built internal pendingCheck unique requestCheck
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, captureRow, tailRow, raw, closingRequirements,
    step, owners, uniqueAfter, scopeSame, demandSame, checked, retained, kept, closingEvidence, rowSame,
    savedCheck, tailCheck, balance, rest⟩ := result
  refine ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, captureRow, tailRow, raw, closingRequirements,
    step, owners, uniqueAfter, scopeSame, demandSame, checked, retained, kept, closingEvidence, rowSame,
    savedCheck, tailCheck, balance, ?_, rest⟩
  let allocated : SourceDependencyAnnotations.Contract := ⟨input.erase, answer, capScope.held,
    capDemand, captureRow, OwnerClosingSource.retirements plan,
    RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
      (OwnerPhaseTransitions.available (ownedTickets whole)) closingRequirements,
    resumeEffects, closeEffects⟩
  obtain ⟨refinedAnswer, bodies, savedHints, waitingHints, answerSame, exactErasure, localCheck, body, joint⟩ :=
    kept.allocated allocated freshContract freshAction rfl rfl rfl rfl rfl rfl balance payload closed
  exact ⟨refinedAnswer, bodies, savedHints, waitingHints, answerSame, exactErasure, localCheck, body, joint,
    closingEvidence.transport (SourcePlannedTyping.insert_extends contracts freshContract),
    closingRecords.capture cut built freshAnnotation closingEvidence (SourcePlannedTyping.insert_extends contracts freshContract)⟩

end Ash.OneShot.SourcePlannedClosingAllocation

#print axioms Ash.OneShot.SourcePlannedClosingAllocation.allocate
