import SourceScheduledAllocationData

/-! Derive allocation interfaces from the synchronized retained source stack.
The selected installed handler supplies its actual typed declarations and
separate declaration evidence. Contextual site checks apply to that actual plan;
exact dispatch aligns its capture data with the typed stack split. -/
namespace Ash.OneShot.SourceScheduledInterfaces
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (lookupDependencies modeDependencies chosen)
open SourceScheduledAllocationData (TypedClauseData)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open SourceContextualHintChecking (Compatible)
open SourceScheduledChecks (Local)
abbrev Receiving := SourceDependencyCapture.Scope

theorem capture_interfaces {hints : Hints wholeScope} {forest : Forest hints}
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets whole)) world
      whole input output demand requirements records forest .nil incoming outgoing)
    (checked : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world
      (.request (effect := requested) (operation := operation)) forest)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses (families handler)},
      evidence (required handler) plans →
      ∀ {modes}, lookupDependencies operation (families handler) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (answer : SourcePlannedTyping.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capRecords tailRecords : RecursiveRequirements.Store) (capScope tailScope : Receiving)
      (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      ∃ (savedHints : Hints capScope) (waitingHints : Hints tailScope),
      ∃ (savedForest : Forest savedHints) (waitingForest : Forest waitingHints),
      answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope ∧
      SourcePlannedFrames.Frame (evidence := evidence) operations policy contracts tables families required world
        (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler))
        (fun rest => .handler (required handler) rest) (handler.effectInst :: residual) residual ∧
      SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole)) world
        capture input answer capDemand capReq capRecords savedForest (waitingForest.append .nil) incoming residual ∧
      SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole)) world
        tail answer output tailDemand tailReq tailRecords waitingForest .nil residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ HEq forest (savedForest.append waitingForest) ∧ demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies capScope.held) = some family ∧
      TypedClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) world outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        owner parameter binder code argument input offered row answer residual family savedForest waitingForest resumeEffects closeEffects ∧
      (∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capReq)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    savedHints, waitingHints, savedForest, waitingForest, annotation, frame, saved, waiting, scopeSame, hintsSame, forestSame, demandSame, recordsSame, selection, evaluation⟩ :=
    SourceScheduledCuts.capture_segments cut source
  have freshErased : contracts.erase.erase owner = none := by
    simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
  have absent := RecursiveCapture.fresh_unowned source.source.source.erase.erase.source.erase freshErased
  cases declared : lookupDependencies operation (families handler) with
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
      cases frame with
      | handler scopeKnown annotation clauses coverage unique declarations recipes capabilities clauseModes =>
          have handlerFrame := SourcePlannedFrames.Frame.handler (evidence := evidence) scopeKnown annotation clauses coverage unique declarations recipes capabilities clauseModes
          have declarationsAtRequest := (ScopedTyping.handler_cut_instance cut) ▸ declarations
          obtain ⟨actualCap, actualTail, resumeEffects, closeEffects, family, actualSavedHints, actualWaitingHints, actualSaved, actualWaiting, actualScope, actualHints, actualForest, actualSelection,
            resume, close, located, data⟩ :=
            SourceScheduledAllocationData.capture_typed_data cut source.source.source.matches declarationsAtRequest
              selected found available declared checked source.pending freshAction absent operationKnown
              (requirementsAtCapture recipes declared)
          cases Option.some.inj (chosenScope.symm.trans actualSelection)
          obtain ⟨rfl, rfl⟩ := SourcePlannedCuts.append_injective (eq_of_heq (hintsSame.symm.trans actualHints))
          obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (forestSame.symm.trans actualForest))
          exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
            resumeEffects, closeEffects, family, _, _, _, _, annotation, scopeKnown, handlerFrame, saved, waiting,
            scopeSame, hintsSame, forestSame, demandSame, recordsSame, resume, close, by simpa only [declared] using located, data, evaluation⟩

end Ash.OneShot.SourceScheduledInterfaces

#print axioms Ash.OneShot.SourceScheduledInterfaces.capture_interfaces
