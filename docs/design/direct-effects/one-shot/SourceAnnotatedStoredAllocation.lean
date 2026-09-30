import SourceAnnotatedStoredClosingData
import SourceAnnotatedStoredCaptureInterfaces

/-! Capture allocation retains the actual scheduling forests. When closing is
available, its exact template supplies a disposal record. When it is structurally
unavailable, checked source derives disposal denial and only a resume record is
added. Both paths reuse joint capture reconstruction, substitution and ownership
proofs; existing disposal records retain their exact saved-plan annotations. -/
namespace Ash.OneShot.SourceAnnotatedStoredAllocation

variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (lookupDependencies modeDependencies)
open SourceDependencySchemes
open SourceAnnotatedStoredAllocationData (CaptureData)
open SourceAnnotatedAllocationData (ClauseEvidence noClauseEvidence)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Annotations)
open SourcePlannedClosingAllocationData (Certificate)

variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

/-- The allocation result retains all existing record, ownership and row
checks, and recovers the stronger clause under that exact contract extension. -/
theorem allocate_retaining (currentEvidence : ClauseEvidence) {hints : SourceContextualHints.Hints wholeScope} {forest : Forest hints}
    (operations : SourcePlannedTyping.Operations) (contracts : SourcePlannedTyping.Contracts)
    (argument input : SourcePlannedTyping.Value)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (source : SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      whole input output demand requirements records forest .nil incoming outgoing stored)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (request : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourceAnnotatedSources.ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand.erase)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (layout : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world whole.erase disposals)
    (closingRecords : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world whole disposals)
    (freshAnnotation : annotations owner = none)
    (built : makePlan capture.erase = some plan)
    (internal : InternalUses capture.erase.erase.liveTickets capture.erase.erase.pending)
    (pendingCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) requirements pendingRow)
    (unique : (ownedTickets whole.erase).Nodup)
    (requestCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables whole.erase)
      (OwnerPhaseTransitions.available (ownedTickets whole.erase))
      (.request [] [⟨requested, operation, false⟩]) requestRow)
    (requirementsAtCapture : ∀ (packet : SourceConsumingStoredBounds.HandlerBounds families handler),
      stored.handlerAt requested = some ⟨handler, packet⟩ →
      evidence (required handler.erase) packet.plans →
      ∀ {modes}, lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held packet.plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
        currentEvidence (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capScope tailScope : Receiving) (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies) (captureRow tailRow raw : Footprint)
      (closingRequirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan)),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, caller, whole.erase⟩
        ⟨code.erase.subst parameter operand.erase, .ticket binder owner,
          .live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase⟩ [.ticket owner] [] ∧
      ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase) =
        owner :: ownedTickets whole.erase ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)).Nodup ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      Checked outward (actions.insert owner code.erase.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)))
        world (family owner) (.live owner capScope tailScope) ∧
      Retained outward (actions.insert owner code.erase.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)))
        world (.live owner capScope tailScope) .nil ∧
      CaptureData (evidence := evidence) operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing annotations (fun _ => True) (stored.atCut cut).1 (stored.atCut cut).2
        answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq ∧
      Certificate operations policy contracts tables world plan capScope raw closingRequirements ∧
      pendingRow = captureRow ++ tailRow ∧
      RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables tail.erase)
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) capReq captureRow ∧
      RecursiveRequirements.Checked (records ++ disposals) []
        (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole.erase)) capDemand) tailReq tailRow ∧
      (OwnerClosingSource.retirements plan).Perm capDemand ∧
      let closeRow := RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail.erase)
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) closingRequirements;
      let contract : SourceDependencyAnnotations.Contract := ⟨input.erase, answer, capScope.held,
          capDemand, captureRow, OwnerClosingSource.retirements plan, closeRow, resumeEffects, closeEffects⟩;
        (∃ refinedAnswer : SourcePlannedTyping.Value, ∃ bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner),
          ∃ (savedHints : SourceContextualHints.Hints capScope) (waitingHints : SourceContextualHints.Hints tailScope),
          ∃ (saved : Forest savedHints) (waiting : Forest waitingHints),
          refinedAnswer.erase = answer ∧ (SourcePlannedSources.refineContract contract input refinedAnswer).erase = contract ∧
          SourceScheduledSavedPlans.Matches (annotations.insert owner ⟨capScope, savedHints, saved⟩)
            (.live (owner := owner) saved waiting) ∧
          SourceScheduledChecks.Local outward (actions.insert owner code.erase.requiredActions)
            (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
            (bodies owner) (.live (owner := owner) saved waiting) ∧
          SourceAnnotatedSources.Body operations policy
            (contracts.insert owner (SourcePlannedSources.refineContract contract input refinedAnswer)) world residual
            (.ticket binder owner) (fun _ => none) (code.subst parameter operand) refinedAnswer
            ⟨owner, contract.erase, offered.dispose, row⟩ (SourcePlanSignatures.signature (bodies owner)) ∧
          SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy
            (contracts.insert owner (SourcePlannedSources.refineContract contract input refinedAnswer)) tables families required
            (actions.insert owner code.erase.requiredActions) outward
            (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
            (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
            refinedAnswer output tailDemand (.sequence (.spent owner) tailReq)
            ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live (owner := owner) saved waiting) .nil residual outgoing (.live (stored.atCut cut).1 (stored.atCut cut).2) ∧
          SourceAnnotatedClosingData.Certificate operations policy
            (contracts.insert owner (SourcePlannedSources.refineContract contract input refinedAnswer))
            tables world capture plan saved raw closingRequirements ∧
          Certificate operations policy (contracts.insert owner (SourcePlannedSources.refineContract contract input refinedAnswer))
            tables world plan capScope raw closingRequirements ∧
          SourceAnnotatedClosingRecords.Records operations policy
            (contracts.insert owner (SourcePlannedSources.refineContract contract input refinedAnswer)) tables
            (annotations.insert owner ⟨capScope, savedHints, saved⟩) world
            (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          currentEvidence (bodies owner) (.live (owner := owner) saved waiting)) ∧
        SourceDependencyAnnotations.Body operations.erase policy (contracts.erase.insert owner contract) world residual (.ticket binder owner)
          SourceDependencyAnnotations.Environment.empty (code.erase.subst parameter operand.erase) answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) ∧
        SourceDependencyFrames.Segment operations.erase policy (contracts.erase.insert owner contract) tables families
          (actions.insert owner code.erase.requiredActions) world
          (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)
          answer output.erase tailDemand (.sequence (.spent owner) tailReq)
          ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live owner capScope tailScope) residual outgoing ∧
        let nextAnnotations := fun other => if other = owner then some capScope else annotations.scopes other;
        Closing.Bound nextAnnotations (.live owner capScope tailScope) ∧
          Closing.Template operations.erase policy (contracts.erase.insert owner contract) tables world .none
            plan raw closingRequirements capScope.forClosing ∧
        DeclaredSourceClosing.Records operations.erase.erase policy (contracts.erase.insert owner contract).erase tables world
          (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          Closing.Records operations.erase policy (contracts.erase.insert owner contract) tables nextAnnotations world
            (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          let store := ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals);
          RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail.erase)
            (OwnerPhaseTransitions.available (ownedTickets whole.erase)) capReq captureRow ∧
          RecursiveRequirements.Checked store []
            (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole.erase)) capDemand) tailReq tailRow ∧
          RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)))
            (.invoke ⟨owner, .resume⟩ capDemand []) captureRow ∧
          (∀ closingRow, closeRow = some closingRow → RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)))
            (.invoke ⟨owner, .dispose⟩ (OwnerClosingSource.retirements plan) []) closingRow) ∧
          ((offered.dispose = true → DeclaredCallbackAdmission.checkClosing (CallableProtectionFrames.contextOf tables tail.erase) outside
            raw (requestRow ++ captureRow) = true) →
            ∃ (clauseDemand : List Nat) (clauseRequirements : RecursiveRequirements.Requirements clauseDemand) (clauseRow : Footprint),
              SourceDependencyAnnotations.Expression operations.erase policy (contracts.erase.insert owner contract) world residual
                (.ticket binder owner) SourceDependencyAnnotations.Environment.empty (code.erase.subst parameter operand.erase)
                answer clauseDemand clauseRequirements (family owner) ∧
              RecursiveRequirements.Checked store
                (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase))
                (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)))
                clauseRequirements clauseRow ∧
              EffectBounds.Covers (requestRow ++ captureRow) clauseRow) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    resumeEffects, closeEffects, family, savedHints, waitingHints, savedForest, waitingForest, packet, packetAt, annotation, scopeKnown, declaration, saved, waiting,
    scopeSame, hintsSame, forestSame, demandSame, recordsSame, resume, close, located, bodies, typed, clauseKept, evaluation⟩ :=
    SourceAnnotatedStoredCaptureInterfaces.capture_interfaces_retaining currentEvidence cut source request selected found available operationKnown freshContract freshAction requirementsAtCapture
  obtain ⟨savedMatched, waitingMatched⟩ := (SourceScheduledSavedPlans.matches_append _ _).mp
    (matched.congr scopeSame hintsSame forestSame)
  have data := CaptureData.checked (savedEvidence := fun _ => True) annotation scopeKnown saved waiting recordsSame resume close typed trivial savedMatched waitingMatched (currentEvidence := currentEvidence) clauseKept
  have freshScope : annotations.scopes owner = none := by simp [Annotations.scopes, freshAnnotation]
  obtain ⟨checked, retained⟩ := data.forget.clause.erase_checks
  have oldFresh : contracts.erase owner = none := by simp [SourcePlannedTyping.Contracts.erase, freshContract]
  have oldPayload : SourceDependencyAnnotations.ValueSummary operations.erase policy contracts.erase world
      SourceDependencyAnnotations.Environment.empty payloadAllowed operand.erase argument.erase := by
    have erased := SourcePlannedSources.expression_erase payload.erase
    have emptyErasure : SourcePlannedTyping.Environment.erase (fun _ => none) = SourceDependencyAnnotations.Environment.empty := rfl
    rw [emptyErasure] at erased
    exact erased
  have result := SourceDependencySchemes.allocate_capture_source_from_closing_interfaces
    (outside := outside) (caller := caller)
    (closingCertificate := fun answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq raw closingRequirements =>
      CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing annotations
        (fun saved => SourceAnnotatedClosingData.Certificate operations policy contracts tables world capture plan saved raw closingRequirements) (stored.atCut cut).1 (stored.atCut cut).2
        answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    (certificate := fun answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq =>
      CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing annotations (fun _ => True) (stored.atCut cut).1 (stored.atCut cut).2
        answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    cut.erase source.forget.erase.source.source.erase
    ⟨answer.erase, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
      resumeEffects, closeEffects, family, annotation, scopeKnown, declaration.forget.erase.source.source.erase.erase.source, saved.forget.erase.source.source.erase, waiting.forget.erase.source.source.erase, scopeSame, demandSame,
      recordsSame, resume, close, located, checked, retained, data, evaluation,
      fun contract fresh inputSame answerSame resumeSame closeSame heldSame balance =>
        data.forget.clause.erase_body contract fresh inputSame answerSame resumeSame closeSame heldSame balance⟩
    (by
      intro answer residual capDemand capReq capRecords capScope saved family tailScope resumeEffects closeEffects tailDemand tailReq data
      exact SourceAnnotatedStoredClosingData.capture_closing data built)
    selected.erase found available (SourcePlannedSources.operation_erase operationKnown) oldPayload closed oldFresh freshAction layout closingRecords.erase.erase.erase
    matched.erase freshScope built internal pendingCheck unique requestCheck
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, captureRow, tailRow, raw, closingRequirements,
    step, owners, uniqueAfter, scopeSame, demandSame, checked, retained, kept, closingEvidence, rowSame,
    savedCheck, tailCheck, balance, rest⟩ := result
  have legacyClosing := SourceAnnotatedStoredClosingData.erase_capture_certificate closingEvidence
  refine ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, captureRow, tailRow, raw, closingRequirements,
    step, owners, uniqueAfter, scopeSame, demandSame, checked, retained, kept.forget_clause_evidence, legacyClosing, rowSame,
    savedCheck, tailCheck, balance, ?_, rest⟩
  let allocated : SourceDependencyAnnotations.Contract := ⟨input.erase, answer, capScope.held,
    capDemand, captureRow, OwnerClosingSource.retirements plan,
    RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail.erase)
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) closingRequirements,
    resumeEffects, closeEffects⟩
  obtain ⟨refinedAnswer, bodies, savedHints, waitingHints, savedForest, waitingForest, answerSame, exactErasure, closingAtSaved, matchedAfter, localCheck, body, joint, clauseKept⟩ :=
    closingEvidence.allocated_retaining allocated freshContract freshAction freshAnnotation rfl rfl rfl rfl rfl rfl balance payload closed
  exact ⟨refinedAnswer, bodies, savedHints, waitingHints, savedForest, waitingForest, answerSame, exactErasure, matchedAfter, localCheck, body, joint,
    closingAtSaved.transport (SourcePlannedTyping.insert_extends contracts freshContract),
    legacyClosing.transport (SourcePlannedTyping.insert_extends contracts freshContract),
    closingRecords.capture cut.reconstructs built freshAnnotation closingAtSaved (SourcePlannedTyping.insert_extends contracts freshContract), clauseKept⟩

theorem allocate_without_closing_retaining (currentEvidence : ClauseEvidence) {hints : SourceContextualHints.Hints wholeScope} {forest : Forest hints}
    (operations : SourcePlannedTyping.Operations) (contracts : SourcePlannedTyping.Contracts)
    (argument input : SourcePlannedTyping.Value)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (source : SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      whole input output demand requirements records forest .nil incoming outgoing stored)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (request : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourceAnnotatedSources.ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand.erase)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (layout : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world whole.erase disposals)
    (closingRecords : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world whole disposals)
    (freshAnnotation : annotations owner = none)
    (unavailable : makePlan capture.erase = none ∨ ¬ InternalUses capture.erase.erase.liveTickets capture.erase.erase.pending)
    (pendingCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) requirements pendingRow)
    (unique : (ownedTickets whole.erase).Nodup)
    (requestCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables whole.erase)
      (OwnerPhaseTransitions.available (ownedTickets whole.erase))
      (.request [] [⟨requested, operation, false⟩]) requestRow)
    (requirementsAtCapture : ∀ (packet : SourceConsumingStoredBounds.HandlerBounds families handler),
      stored.handlerAt requested = some ⟨handler, packet⟩ →
      evidence (required handler.erase) packet.plans →
      ∀ {modes}, lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held packet.plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
        currentEvidence (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capScope tailScope : Receiving) (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies)
      (captureRow tailRow : Footprint),
      offered.dispose = false ∧ code.erase.requiredActions.dispose = false ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, caller, whole.erase⟩
        ⟨code.erase.subst parameter operand.erase, .ticket binder owner,
          .live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase⟩ [.ticket owner] [] ∧
      ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase) =
        owner :: ownedTickets whole.erase ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)).Nodup ∧
      demand = capDemand ++ tailDemand ∧ pendingRow = captureRow ++ tailRow ∧
      let allocated : SourceDependencyAnnotations.Contract :=
        ⟨input.erase, answer, capScope.held, capDemand, captureRow, capDemand, none, resumeEffects, closeEffects⟩;
      ∃ refinedAnswer : SourcePlannedTyping.Value, ∃ bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner),
      ∃ (savedHints : SourceContextualHints.Hints capScope) (waitingHints : SourceContextualHints.Hints tailScope),
      ∃ (saved : Forest savedHints) (waiting : Forest waitingHints),
        refinedAnswer.erase = answer ∧ (SourcePlannedSources.refineContract allocated input refinedAnswer).erase = allocated ∧
        SourceScheduledSavedPlans.Matches (annotations.insert owner ⟨capScope, savedHints, saved⟩)
          (.live (owner := owner) saved waiting) ∧
        SourceScheduledChecks.Local outward (actions.insert owner code.erase.requiredActions)
          (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
          (bodies owner) (.live (owner := owner) saved waiting) ∧
        SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy
          (contracts.insert owner (SourcePlannedSources.refineContract allocated input refinedAnswer)) tables families required
          (actions.insert owner code.erase.requiredActions) outward
          (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
          (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
          refinedAnswer output tailDemand (.sequence (.spent owner) tailReq)
          ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live (owner := owner) saved waiting) .nil residual outgoing (.live (stored.atCut cut).1 (stored.atCut cut).2) ∧
        SourceAnnotatedClosingRecords.Records operations policy
          (contracts.insert owner (SourcePlannedSources.refineContract allocated input refinedAnswer)) tables
          (annotations.insert owner ⟨capScope, savedHints, saved⟩) world
          (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) disposals ∧
        DeclaredSourceClosing.Records operations.erase.erase policy
          (contracts.insert owner (SourcePlannedSources.refineContract allocated input refinedAnswer)).erase.erase tables world
          (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase) disposals ∧
        let store := ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++ disposals;
        let afterPhases := OwnerPhaseTransitions.available (ownedTickets
          (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase));
        RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail.erase)
          (OwnerPhaseTransitions.available (ownedTickets whole.erase)) capReq captureRow ∧
        RecursiveRequirements.Checked store []
          (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole.erase)) capDemand) tailReq tailRow ∧
        RecursiveRequirements.Checked store
          (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase))
          afterPhases (.invoke ⟨owner, .resume⟩ capDemand []) captureRow ∧
        ∃ clauseDemand, ∃ clauseRequirements : RecursiveRequirements.Requirements clauseDemand, ∃ clauseRow,
          SourceAnnotatedSources.Expression operations policy
            (contracts.insert owner (SourcePlannedSources.refineContract allocated input refinedAnswer)) world residual
            (.ticket binder owner) (fun _ => none) (code.subst parameter operand) refinedAnswer clauseDemand clauseRequirements
            (SourcePlanSignatures.signature (bodies owner)) ∧
          RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase))
            afterPhases clauseRequirements clauseRow ∧ EffectBounds.Covers (requestRow ++ captureRow) clauseRow ∧
          currentEvidence (bodies owner) (.live (owner := owner) saved waiting) := by
  have noDispose : offered.dispose = false := by
    cases disposes : offered.dispose with
    | false => rfl
    | true =>
        obtain ⟨a, b, modes, plan, ca, cb, same, picked, realized, route, held, built, owners⟩ :=
          SourceDependencyCapture.checked_cut cut.erase source.forget.erase.source.source.matches.realizes
            (SourceDependencySchemes.checked_request request.erase.erase) found disposes
        rcases unavailable with blocked | external
        · rw [blocked] at built; cases built
        · exact False.elim (external (SourceDependencySchemes.capture_internal_uses cut.erase
            source.forget.erase.source.source.erase request.erase.erase found disposes))
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    resumeEffects, closeEffects, family, savedHints, waitingHints, savedForest, waitingForest, packet, packetAt, annotation, scopeKnown,
    declaration, saved, waiting, scopeSame, hintsSame, forestSame, demandSame, recordsSame,
    resume, close, located, bodies, typed, clauseKept, evaluation⟩ :=
    SourceAnnotatedStoredCaptureInterfaces.capture_interfaces_retaining currentEvidence cut source request selected found available operationKnown freshContract freshAction requirementsAtCapture
  have clauseModes : SourceTemplates.ClauseModes handler.erase.clauses (tables handler.erase) := by cases declaration.forget; assumption
  obtain ⟨actual, actualFound, permission⟩ := SourceTemplates.selected_clause_mode selected.erase clauseModes
  cases Option.some.inj (found.symm.trans actualFound)
  have codeNoDispose : code.erase.requiredActions.dispose = false := by
    cases used : code.erase.requiredActions.dispose with
    | false => rfl
    | true => have impossible := permission used; rw [noDispose] at impossible; cases impossible
  obtain ⟨savedMatched, waitingMatched⟩ := (SourceScheduledSavedPlans.matches_append _ _).mp
    (matched.congr scopeSame hintsSame forestSame)
  have data := CaptureData.checked (savedEvidence := fun _ => True) annotation scopeKnown saved waiting
    recordsSame resume close typed trivial savedMatched waitingMatched (currentEvidence := currentEvidence) clauseKept
  have evaluated := RecursiveRequirements.checked_complete pendingCheck
  rw [evaluation] at evaluated
  obtain ⟨captureRow, tailRow, inside, outside, rowSame⟩ := PhaseRechecking.merge_split evaluated
  have savedCheck := RecursiveRequirements.evaluate_sound inside
  have tailCheck := RecursiveRequirements.evaluate_sound outside
  have freshErased : contracts.erase.erase owner = none := by
    simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
  have absent := RecursiveCapture.fresh_unowned source.forget.erase.source.source.erase.erase.source.erase freshErased
  have consumed : OwnerPhaseTransitions.available (ownedTickets whole.erase) owner = .consumed := by
    simp [OwnerPhaseTransitions.available, absent]
  let allocated : SourceDependencyAnnotations.Contract :=
    ⟨input.erase, answer.erase, capScope.held, capDemand, captureRow, capDemand, none, resumeEffects, closeEffects⟩
  obtain ⟨refinedAnswer, bodies, actualSavedHints, actualWaitingHints, actualSaved, actualWaiting, answerSame,
    exactErasure, kept, matchedAfter, localCheck, body, joint, clauseKept⟩ :=
    data.allocated_retaining allocated freshContract freshAction freshAnnotation rfl rfl rfl rfl rfl rfl (List.Perm.refl _) payload closed
  have extension := SourcePlannedTyping.insert_extends
    (contract := SourcePlannedSources.refineContract allocated input refinedAnswer) contracts freshContract
  have oldExtension := SourceDependencyFrames.erased_contract_extension (SourcePlannedCheckedFrames.erased_extension extension)
  have recordsAfter := closingRecords.capture_existing (saved := actualSaved)
    (inputType := ScopedPorts.embedPort input.erase.erase.port) (answerType := handler.erase.answer)
    (caller := handler.scope) cut.reconstructs freshAnnotation extension
  have layoutAtOld : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world
      (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase) disposals := by
    obtain ⟨nested, remaining, savedClosing, tailClosing, sameClosings⟩ :=
      DeclaredSourceClosing.split_append (handler_cut_reconstructs cut.erase ▸ layout)
    rw [sameClosings]
    rcases unavailable with blocked | external
    · exact .unclosable blocked savedClosing tailClosing
    · exact .external external savedClosing tailClosing
  have layoutAfter := DeclaredSourceClosing.records_extension layoutAtOld oldExtension
  have ready : ClosedExcept parameter code.erase := by
    obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut.erase
      (SourceTemplates.segment_ports source.forget.erase.source.source.erase.erase.source.erase)
    cases handlerTyped with
    | handler scopeKnown clauses coverage unique =>
        obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed selected.erase clauses
        exact ScopedPorts.typed_suffix_ready bodyTyped
  have raw := RawStep.capture requested operation parameter binder owner operand.erase code.erase caller whole.erase capture.erase tail.erase handler.erase
    (ScopedPorts.embedPort input.erase.erase.port) cut.erase selected.erase closed ready
  have afterUnique := RecursiveCapture.capture_unique (inputType := ScopedPorts.embedPort input.erase.erase.port)
    cut.erase source.forget.erase.source.source.erase.erase.source.erase unique freshErased
  refine ⟨answer.erase, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, captureRow, tailRow, noDispose, codeNoDispose, raw,
    RecursiveCapture.capture_owned cut.erase, afterUnique, demandSame, rowSame,
    refinedAnswer, bodies, actualSavedHints, actualWaitingHints, actualSaved, actualWaiting,
    answerSame, exactErasure, matchedAfter, localCheck, joint, recordsAfter, layoutAfter, ?_⟩
  have savedAfter := RecursiveCapture.checked_insert_consumed savedCheck consumed
    (mode := .resume) (body := ⟨capDemand, capReq⟩)
  have laterConsumed := RecursiveTransport.phases_spendAll_later (owners := capDemand) owner consumed
  have tailAfter := RecursiveCapture.checked_insert_consumed tailCheck laterConsumed
    (mode := .resume) (body := ⟨capDemand, capReq⟩)
  have phaseSame := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.erase.erase.port) cut.erase absent
  have resumeChecked := RecursiveClauses.fresh_resume_check
    (by simpa only [List.append_nil] using savedAfter) phaseSame
  refine ⟨by simpa only [List.cons_append, List.append_nil] using savedAfter,
    by simpa only [List.cons_append] using tailAfter, ?_, ?_⟩
  · simpa only [List.cons_append] using resumeChecked
  · have requestExport := RecursiveRequirements.checked_complete requestCheck
    simp only [RecursiveContexts.evaluate_request, OwnerSource.exportAt,
      OwnerPhaseTransitions.project_actual] at requestExport
    obtain ⟨actualOffer, advertised, offerKnown, mode, rowKnown, advertisedExport⟩ :=
      RecursiveDispatch.cut_residual cut.erase requestExport
    cases Option.some.inj (offerKnown.symm.trans found)
    simp only [Bool.false_or] at rowKnown
    cases Option.some.inj (rowKnown.symm.trans available)
    let afterPhases := OwnerPhaseTransitions.available (ownedTickets
      (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase))
    have callerReady : ∀ other ∈ activeTickets tail.erase, afterPhases other = .available := by
      intro other member
      apply if_pos
      exact List.mem_cons.mpr (Or.inr (List.mem_append_right _ (active_tickets_owned tail.erase member)))
    have exported : OwnerSource.exportAt (OwnerPhases.ofStack tables tail.erase) afterPhases row = some requestRow :=
      (RecursivePlanAdmission.caller_export callerReady).trans advertisedExport
    have interface : ClauseRowAdmission.Interface owner allocated.erase offered.dispose
        (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++ disposals)
        (OwnerPhases.ofStack tables tail.erase) afterPhases requestRow := by
      apply ClauseRowAdmission.Interface.of_resume _ noDispose (OwnerPhaseTransitions.capture_tail_fresh cut.erase absent)
      simpa only [List.cons_append, afterPhases, OwnerPhases.ofStack, allocated,
        SourceDependencyAnnotations.Contract.erase, saved.forget.erase.source.source.matches.realizes.held] using resumeChecked
    cases body with
    | typed expression rows closingRows =>
        obtain ⟨clauseRow, checkedClause, covered⟩ := rows.instantiate interface exported
              (ClauseRowAdmission.SourceStore.of_source joint.forget.erase.source.source.erase.erase.source.erase
                (DeclaredSourceClosing.records_erase layoutAfter) (by simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, SourcePlannedTyping.Contracts.insert, exactErasure]))
        refine ⟨_, _, clauseRow, expression, ?_, covered, clauseKept⟩
        simpa only [OwnerPhases.ofStack, allocated, SourceDependencyAnnotations.Contract.erase,
          saved.forget.erase.source.source.matches.realizes.held] using checkedClause

end Ash.OneShot.SourceAnnotatedStoredAllocation

#print axioms Ash.OneShot.SourceAnnotatedStoredAllocation.allocate_retaining
#print axioms Ash.OneShot.SourceAnnotatedStoredAllocation.allocate_without_closing_retaining
