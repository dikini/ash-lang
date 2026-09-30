import SourcePlannedFrameCuts

/-! Derive allocation interfaces from the synchronized retained source stack.
The selected installed handler supplies its actual declarations and structural
recipes; exact dispatch aligns their capture data with the typed stack split. -/
namespace Ash.OneShot.SourcePlannedFrameInterfaces
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (lookupDependencies modeDependencies chosen)
open SourcePlannedAllocationData (ClauseData)
open SourceContextualHints (Hints)
open SourceContextualHintChecking (Compatible)
open SourcePlannedChecks (Local Pending)
open SourceDependencySchemes (Checked Retained)
abbrev Receiving := SourceDependencyCapture.Scope

theorem capture_interfaces {hints : Hints wholeScope}
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourcePlannedFrames.Segment operations policy contracts tables families required actions world
      whole input output demand requirements records hints incoming outgoing)
    (checked : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world
      (.request (effect := requested) (operation := operation)) hints)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world hints .nil)
    (compatible : Compatible hints .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (freshContract : contracts owner = none) (freshAction : actions owner = none) :
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
        tail answer output.erase tailDemand tailReq tailRecords tailScope residual outgoing ∧
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
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    savedHints, waitingHints, annotation, frame, saved, waiting, scopeSame, demandSame, recordsSame, selection, evaluation⟩ :=
    SourcePlannedFrameCuts.capture_segments cut source
  have freshErased : contracts.erase.erase owner = none := by
    simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
  have absent := RecursiveCapture.fresh_unowned source.erase.erase.source.erase freshErased
  cases declared : lookupDependencies operation (families handler) with
  | none =>
      have missing : SourceDependencyCapture.select requested operation wholeScope = none := by
        simpa only [chosen, found, declared] using selection operation
      have guard := SourceDependencySchemes.checked_request checked.erase
      simp only [SourceDependencyCapture.checkCapture, missing] at guard
      cases guard
  | some modes =>
      have chosenScope : SourceDependencyCapture.select requested operation wholeScope =
          some (.handler capScope tailScope offered modes) := by
        simpa only [chosen, found, declared] using selection operation
      cases frame with
      | handler scopeKnown annotation clauses coverage unique declarations recipes capabilities clauseModes =>
          have handlerFrame := SourcePlannedFrames.Frame.handler (evidence := SourcePlannedFrames.recipeEvidence) scopeKnown annotation clauses coverage unique declarations recipes capabilities clauseModes
          have declarationsAtRequest := (ScopedTyping.handler_cut_instance cut) ▸ declarations
          obtain ⟨actualCap, actualTail, resumeEffects, closeEffects, family, actualScope, actualSelection,
            resume, close, located, data⟩ :=
            SourcePlannedAllocationData.capture_data cut source.matches declarationsAtRequest recipes clauseModes
              selected found available declared checked retained compatible freshAction absent operationKnown
          cases Option.some.inj (chosenScope.symm.trans actualSelection)
          exact ⟨answer.erase, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
            resumeEffects, closeEffects, family, annotation, scopeKnown, handlerFrame.erase.erase.source, saved.erase, waiting.erase,
            scopeSame, demandSame, recordsSame, resume, close, by simpa only [declared] using located, data, evaluation⟩

/-- Allocation obtains its selected source and clause checks from the stronger
retained stack. It preserves the established allocation result and strengthens
its current clause; the successor saved-source layer is still the older one. -/
theorem allocate {hints : Hints wholeScope}
    (operations : SourcePlannedTyping.Operations) (contracts : SourcePlannedTyping.Contracts)
    (argument input : SourcePlannedTyping.Value)
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourcePlannedFrames.Segment operations policy contracts tables families required actions world
      whole input output demand requirements records hints incoming outgoing)
    (checked : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world
      (.request (effect := requested) (operation := operation)) hints)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world hints .nil)
    (compatible : Compatible hints .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourcePlannedSources.ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (layout : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world whole disposals)
    (closingRecords : SourceDependencySchemes.Closing.Records operations.erase policy contracts.erase tables annotations world whole disposals)
    (annotationBound : SourceDependencySchemes.Closing.Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
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
          answer output.erase tailDemand (.sequence (.spent owner) tailReq)
          ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live owner capScope tailScope) residual outgoing ∧
        let nextAnnotations := fun other => if other = owner then some capScope else annotations other;
        SourceDependencySchemes.Closing.Bound nextAnnotations (.live owner capScope tailScope) ∧
          SourceDependencySchemes.Closing.Template operations.erase policy (contracts.erase.insert owner contract) tables world .none
            plan raw closingRequirements capScope.forClosing ∧
          DeclaredSourceClosing.Records operations.erase.erase policy (contracts.erase.insert owner contract).erase tables world
            (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          SourceDependencySchemes.Closing.Records operations.erase policy (contracts.erase.insert owner contract) tables nextAnnotations world
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
  exact SourcePlannedAllocation.allocate operations contracts argument input cut source.erase
    (capture_interfaces cut source checked retained compatible selected found available operationKnown freshContract freshAction)
    selected found available operationKnown payload closed freshContract freshAction layout closingRecords
    annotationBound freshAnnotation built internal pendingCheck unique requestCheck

end Ash.OneShot.SourcePlannedFrameInterfaces

#print axioms Ash.OneShot.SourcePlannedFrameInterfaces.capture_interfaces

#print axioms Ash.OneShot.SourcePlannedFrameInterfaces.allocate
