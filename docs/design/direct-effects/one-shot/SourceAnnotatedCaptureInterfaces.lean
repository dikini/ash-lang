import SourceAnnotatedAllocationData

/-! Derive allocation interfaces from the synchronized retained source stack.
The selected installed handler supplies its actual typed declarations and
separate declaration evidence. Contextual site checks apply to that actual plan;
exact dispatch aligns its capture data with the typed stack split. -/
namespace Ash.OneShot.SourceAnnotatedCaptureInterfaces

variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (lookupDependencies modeDependencies chosen)
open SourceAnnotatedAllocationData (TypedClauseData TypedClauseDataAtPlan ClauseEvidence noClauseEvidence)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open SourceContextualHintChecking (Compatible)
open SourceScheduledChecks (Local)
abbrev Receiving := SourceDependencyCapture.Scope

theorem capture_interfaces_retaining (currentEvidence : ClauseEvidence) {hints : Hints wholeScope} {forest : Forest hints}
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (source : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      whole input output demand requirements records forest .nil incoming outgoing)
    (checked : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      evidence (required handler.erase) plans →
      ∀ {modes}, lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
        currentEvidence (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (answer : SourcePlannedTyping.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capRecords tailRecords : RecursiveRequirements.Store) (capScope tailScope : Receiving)
      (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      ∃ (savedHints : Hints capScope) (waitingHints : Hints tailScope),
      ∃ (savedForest : Forest savedHints) (waitingForest : Forest waitingHints),
      answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope ∧
      SourceAnnotatedRuntimeTyping.Frame (evidence := evidence) operations policy contracts tables families required outward actions
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world (waitingForest.append .nil) (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler.erase) (families handler.erase))
        (fun rest => .handler (required handler.erase) rest) (fun rest => .handler rest) (handler.effectInst :: residual) residual ∧
      SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
        capture input answer capDemand capReq capRecords savedForest (waitingForest.append .nil) incoming residual ∧
      SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
        tail answer output tailDemand tailReq tailRecords waitingForest .nil residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ HEq forest (savedForest.append waitingForest) ∧ demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (code.erase.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler.erase)).bind (modeDependencies capScope.held) = some family ∧
      ∃ bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner),
      TypedClauseDataAtPlan operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer residual family savedForest waitingForest resumeEffects closeEffects bodies ∧
      currentEvidence (bodies owner) (.live (owner := owner) savedForest waitingForest) ∧
      (∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables tail.erase ++ receiving) before capReq)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    savedHints, waitingHints, savedForest, waitingForest, annotation, frame, saved, waiting, scopeSame, hintsSame, forestSame, demandSame, recordsSame, selection, evaluation⟩ :=
    SourceAnnotatedRuntimeCaptureSplitting.capture_segments cut source
  have freshErased : contracts.erase.erase owner = none := by
    simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
  have absent := RecursiveCapture.fresh_unowned source.erase.source.source.erase.erase.source.erase freshErased
  cases declared : lookupDependencies operation (families handler.erase) with
  | none =>
      have missing : SourceDependencyCapture.select requested operation wholeScope = none := by
        simpa only [chosen, found, declared] using selection operation
      have guard := SourceDependencySchemes.checked_request checked.erase.erase
      simp only [SourceDependencyCapture.checkCapture, missing] at guard
      cases guard
  | some modes =>
      have chosenScope : SourceDependencyCapture.select requested operation wholeScope =
          some (.handler capScope tailScope offered modes) := by
        simpa only [chosen, found, declared] using selection operation
      have handlerFrame := frame
      cases frame with
      | handler scopeKnown annotation clauses coverage unique declarations recipes supplied capabilities clauseModes =>
          have instanceSame : handler.effectInst = requested := ScopedTyping.handler_cut_instance cut.erase
          have declarationsAtRequest := instanceSame ▸ declarations
          obtain ⟨actualCap, actualTail, resumeEffects, closeEffects, family, actualSavedHints, actualWaitingHints, actualSaved, actualWaiting, actualScope, actualHints, actualForest, actualSelection,
            resume, close, located, actualCut, bodies, actualSelected, data⟩ :=
            SourceAnnotatedAllocationData.capture_typed_data_exact cut source.erase.source.source.matches declarationsAtRequest
              selected found available declared checked source.erase.pending freshAction absent operationKnown
              (by
                intro capturedScope tailScope savedHints waitingHints saved waiting cut family bodies chosen
                exact (requirementsAtCapture recipes declared saved waiting cut chosen).1)
          have clauseKept := (requirementsAtCapture recipes declared actualSaved actualWaiting actualCut actualSelected).2
          cases Option.some.inj (chosenScope.symm.trans actualSelection)
          obtain ⟨rfl, rfl⟩ := SourcePlannedCuts.append_injective (eq_of_heq (hintsSame.symm.trans actualHints))
          obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (forestSame.symm.trans actualForest))
          exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
            resumeEffects, closeEffects, family, _, _, _, _, annotation, scopeKnown, handlerFrame, saved, waiting,
            scopeSame, hintsSame, forestSame, demandSame, recordsSame, resume, close, by simpa only [declared] using located, bodies, data, clauseKept, evaluation⟩

theorem capture_interfaces {hints : Hints wholeScope} {forest : Forest hints}
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (source : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      whole input output demand requirements records forest .nil incoming outgoing)
    (checked : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      evidence (required handler.erase) plans →
      ∀ {modes}, lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (answer : SourcePlannedTyping.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capRecords tailRecords : RecursiveRequirements.Store) (capScope tailScope : Receiving)
      (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      ∃ (savedHints : Hints capScope) (waitingHints : Hints tailScope),
      ∃ (savedForest : Forest savedHints) (waitingForest : Forest waitingHints),
      answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope ∧
      SourceAnnotatedRuntimeTyping.Frame (evidence := evidence) operations policy contracts tables families required outward actions
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world (waitingForest.append .nil) (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler.erase) (families handler.erase))
        (fun rest => .handler (required handler.erase) rest) (fun rest => .handler rest) (handler.effectInst :: residual) residual ∧
      SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
        capture input answer capDemand capReq capRecords savedForest (waitingForest.append .nil) incoming residual ∧
      SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
        tail answer output tailDemand tailReq tailRecords waitingForest .nil residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ HEq forest (savedForest.append waitingForest) ∧ demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (code.erase.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler.erase)).bind (modeDependencies capScope.held) = some family ∧
      TypedClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer residual family savedForest waitingForest resumeEffects closeEffects ∧
      (∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables tail.erase ++ receiving) before capReq)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    resumeEffects, closeEffects, family, savedHints, waitingHints, saved, waiting,
    annotation, scopeKnown, handlerFrame, inside, outside, scopeSame, hintsSame, forestSame, demandSame, recordsSame,
    resume, close, located, bodies, data, _, evaluation⟩ :=
    capture_interfaces_retaining noClauseEvidence cut source checked selected found available operationKnown freshContract freshAction
      (by
        intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting cut family bodies chosen
        exact ⟨requirementsAtCapture recipes declared saved waiting cut chosen, trivial⟩)
  exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    resumeEffects, closeEffects, family, savedHints, waitingHints, saved, waiting,
    annotation, scopeKnown, handlerFrame, inside, outside, scopeSame, hintsSame, forestSame, demandSame, recordsSame,
    resume, close, located, data.forget, evaluation⟩

end Ash.OneShot.SourceAnnotatedCaptureInterfaces

#print axioms Ash.OneShot.SourceAnnotatedCaptureInterfaces.capture_interfaces

#print axioms Ash.OneShot.SourceAnnotatedCaptureInterfaces.capture_interfaces_retaining
