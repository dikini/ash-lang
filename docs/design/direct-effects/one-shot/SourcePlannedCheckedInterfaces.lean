import SourcePlannedCheckedCuts

/-! Derive allocation interfaces from the synchronized retained source stack.
The selected installed handler supplies its actual declarations and structural
recipes; exact dispatch aligns their capture data with the typed stack split. -/
namespace Ash.OneShot.SourcePlannedCheckedInterfaces
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (lookupDependencies modeDependencies chosen)
open SourcePlannedAllocationData (TypedClauseData)
open SourceContextualHints (Hints)
open SourceContextualHintChecking (Compatible)
open SourcePlannedChecks (Local)
abbrev Receiving := SourceDependencyCapture.Scope

theorem capture_interfaces {hints : Hints wholeScope}
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourcePlannedCheckedFrames.Segment operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets whole)) world
      whole input output demand requirements records hints .nil incoming outgoing)
    (checked : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world
      (.request (effect := requested) (operation := operation)) hints)
    (compatible : Compatible hints .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (freshContract : contracts owner = none) (freshAction : actions owner = none) :
    ∃ (answer : SourcePlannedTyping.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capRecords tailRecords : RecursiveRequirements.Store) (capScope tailScope : Receiving)
      (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      ∃ (savedHints : Hints capScope) (waitingHints : Hints tailScope),
      answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope ∧
      SourcePlannedFrames.Frame operations policy contracts tables families required world
        (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler))
        (fun rest => .handler (required handler) rest) (handler.effectInst :: residual) residual ∧
      SourcePlannedCheckedFrames.Segment operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole)) world
        capture input answer capDemand capReq capRecords savedHints (waitingHints.append .nil) incoming residual ∧
      SourcePlannedCheckedFrames.Segment operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole)) world
        tail answer output tailDemand tailReq tailRecords waitingHints .nil residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies capScope.held) = some family ∧
      TypedClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) world outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        owner parameter binder code argument input offered row answer residual family capScope tailScope resumeEffects closeEffects ∧
      (∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capReq)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    savedHints, waitingHints, annotation, frame, saved, waiting, scopeSame, hintsSame, demandSame, recordsSame, selection, evaluation⟩ :=
    SourcePlannedCheckedCuts.capture_segments cut source
  have freshErased : contracts.erase.erase owner = none := by
    simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
  have absent := RecursiveCapture.fresh_unowned source.source.erase.erase.source.erase freshErased
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
            SourcePlannedAllocationData.capture_typed_data cut source.source.matches declarationsAtRequest recipes clauseModes
              selected found available declared checked source.pending compatible freshAction absent operationKnown
          cases Option.some.inj (chosenScope.symm.trans actualSelection)
          exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
            resumeEffects, closeEffects, family, savedHints, waitingHints, annotation, scopeKnown, handlerFrame, saved, waiting,
            scopeSame, hintsSame, demandSame, recordsSame, resume, close, by simpa only [declared] using located, data, evaluation⟩

end Ash.OneShot.SourcePlannedCheckedInterfaces

#print axioms Ash.OneShot.SourcePlannedCheckedInterfaces.capture_interfaces
