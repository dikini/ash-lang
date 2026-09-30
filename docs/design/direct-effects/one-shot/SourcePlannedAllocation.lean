import SourcePlannedAllocationData

/-! Reuse the shared allocation proof with synchronized clause data. The same
constructed contract and records supply the stronger substituted source body;
no independent contract or second allocation is chosen. The saved/closing
source forest remains at the existing annotation layer. -/
namespace Ash.OneShot.SourcePlannedAllocation
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (lookupDependencies modeDependencies)
open SourceDependencySchemes
open SourcePlannedAllocationData (ClauseData)

/-- The allocation result retains all existing record, ownership and row
checks, and recovers the stronger clause under that exact contract extension. -/
theorem allocate
    (operations : SourcePlannedTyping.Operations) (contracts : SourcePlannedTyping.Contracts)
    (argument input : SourcePlannedTyping.Value)
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.Segment operations.erase policy contracts.erase tables families actions world
      whole input.erase output demand requirements records wholeScope incoming outgoing)
    (interfaces :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capRecords tailRecords : RecursiveRequirements.Store) (capScope tailScope : Receiving)
      (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      answer.erase.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope ∧
      DeclaredSourceFrames.Frame operations.erase.erase policy contracts.erase.erase tables world
        (.handler handler) answer.erase answer.erase [] (.request [] []) ∧
      SourceDependencyFrames.Segment operations.erase policy contracts.erase tables families actions world
        capture input.erase answer capDemand capReq capRecords capScope incoming residual ∧
      SourceDependencyFrames.Segment operations.erase policy contracts.erase tables families actions world
        tail answer output tailDemand tailReq tailRecords tailScope residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies capScope.held) = some family ∧
      ClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) world outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        owner parameter binder code argument input offered row answer residual family capScope tailScope resumeEffects closeEffects ∧
      (∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capReq)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourcePlannedSources.ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (layout : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world whole disposals)
    (closingRecords : Closing.Records operations.erase policy contracts.erase tables annotations world whole disposals)
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
      ClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) world outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        owner parameter binder code argument input offered row answer residual family capScope tailScope resumeEffects closeEffects ∧
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
          SourceContextualHintChecking.Matches tables families required (.live (owner := owner) saved waiting)
            (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) ∧
          SourcePlannedChecks.Local outward (actions.insert owner code.requiredActions)
            (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
            (bodies owner) (.live (owner := owner) saved waiting) ∧
          SourcePlannedChecks.Pending outward (actions.insert owner code.requiredActions)
            (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
            (.live (owner := owner) saved waiting) .nil ∧
          SourcePlannedSources.Body operations policy
            (contracts.insert owner (SourcePlannedSources.refineContract contract input refinedAnswer)) world residual
            (.ticket binder owner) (fun _ => none) (code.subst parameter operand) refinedAnswer
            ⟨owner, contract.erase, offered.dispose, row⟩ (SourcePlanSignatures.signature (bodies owner))) ∧
        SourceDependencyAnnotations.Body operations.erase policy (contracts.erase.insert owner contract) world residual (.ticket binder owner)
          SourceDependencyAnnotations.Environment.empty (code.subst parameter operand) answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) ∧
        SourceDependencyFrames.Segment operations.erase policy (contracts.erase.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world
          (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
          answer output tailDemand (.sequence (.spent owner) tailReq)
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
    resumeEffects, closeEffects, family, annotation, scopeKnown, declaration, saved, waiting, scopeSame, demandSame,
    recordsSame, resume, close, located, data, evaluation⟩ := interfaces
  obtain ⟨checked, retained⟩ := data.erase_checks
  have oldFresh : contracts.erase owner = none := by simp [SourcePlannedTyping.Contracts.erase, freshContract]
  have oldPayload : SourceDependencyAnnotations.ValueSummary operations.erase policy contracts.erase world
      SourceDependencyAnnotations.Environment.empty payloadAllowed operand argument.erase := by
    have erased := SourcePlannedSources.expression_erase payload
    have emptyErasure : SourcePlannedTyping.Environment.erase (fun _ => none) = SourceDependencyAnnotations.Environment.empty := rfl
    rw [emptyErasure] at erased
    exact erased
  have result := SourceDependencySchemes.allocate_capture_source_from_interfaces
    (outside := outside) (caller := caller)
    (certificate := fun answer residual family capScope tailScope resumeEffects closeEffects _ _ _ _ =>
      ClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) world outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        owner parameter binder code argument input offered row answer residual family capScope tailScope resumeEffects closeEffects)
    cut source
    ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
      resumeEffects, closeEffects, family, annotation, scopeKnown, declaration, saved, waiting, scopeSame, demandSame,
      recordsSame, resume, close, located, checked, retained, data, evaluation,
      fun contract fresh inputSame answerSame resumeSame closeSame heldSame balance =>
        data.erase_body contract fresh inputSame answerSame resumeSame closeSame heldSame balance⟩
    selected found available (SourcePlannedSources.operation_erase operationKnown) oldPayload closed oldFresh freshAction layout closingRecords
    annotationBound freshAnnotation built internal pendingCheck unique requestCheck
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, captureRow, tailRow, raw, closingRequirements,
    step, owners, uniqueAfter, scopeSame, demandSame, checked, retained, kept, rowSame,
    savedCheck, tailCheck, balance, rest⟩ := result
  refine ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, captureRow, tailRow, raw, closingRequirements,
    step, owners, uniqueAfter, scopeSame, demandSame, checked, retained, kept, rowSame,
    savedCheck, tailCheck, balance, ?_, rest⟩
  exact kept.allocated_body _ freshContract rfl rfl rfl rfl rfl balance payload closed

end Ash.OneShot.SourcePlannedAllocation

#print axioms Ash.OneShot.SourcePlannedAllocation.allocate
