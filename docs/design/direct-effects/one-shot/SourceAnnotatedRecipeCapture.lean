import SourceAnnotatedRuntimeCapture

/-! Existing structural clause recipes discharge capture-site requirements
using the actual request and pending schedule. This specialization does not
extend the recipe grammar or assume a successful future body. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeState
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceRetainedPlans (Forest)
open SourcePlanSignatures (signature)

variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

theorem capture_from_recipes_retaining (currentEvidence : SourceAnnotatedAllocationData.ClauseEvidence) {hints : SourceContextualHints.Hints receiving} {forest : Forest hints}
    (state : State operations policy contracts tables families required actions annotations world [] outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole forest output demand row)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase.erase (Admission.outsideResources capture.erase.erase))
    (evidenceAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      SourcePlannedFrames.recipeEvidence (required handler.erase) plans →
      ∀ {modes}, SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → SourceDependencyAnnotations.Dependencies}
        {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      currentEvidence (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      (∃ dependencies, ∃ nextPlan : SourceDeclarationPlans.Plan dependencies,
      AtPlan operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack nextPlan
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow ∧
      currentEvidence nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  apply capture_preserves_retaining currentEvidence state cut isValue selected found freshContract freshAction freshAnnotation supported
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals sourcePlan
    generalize frozen : Instantiation.freezeEffect requested = actualEffect at current
    generalize planSignature : signature sourcePlan = checking at current
    cases current with
    | checked checkedHint metadata node => cases node with
      | perform operationKnown admitted operandSource formed =>
        cases freeze_effect_injective frozen
        cases sourcePlan with
        | sequence operandPlan requestPlan =>
          cases requestPlan
          cases contextual with
          | sequence operandCheck requestCheck =>
            have clauseModes : SourceTemplates.ClauseModes handler.erase.clauses (tables handler.erase) := by
              obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
                capScope, tailScope, annotation, frame, saved, waiting, rest⟩ :=
                SourceDependencyFrames.capture_segments cut.erase pending.erase.source.source.erase
              cases frame with
              | handler scope annotation clauses coverage unique declarations capabilities modes => exact modes
            have freshErased : contracts.erase.erase owner = none := by
              simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
            have absent := RecursiveCapture.fresh_unowned pending.erase.source.source.erase.erase.source.erase freshErased
            intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting plannedCut family bodies chosen
            refine ⟨?_, evidenceAtCapture recipes declared saved waiting plannedCut chosen⟩
            exact SourceScheduledAllocationData.capture_requirements_from_recipe cut.erase pending.erase.source.source.matches
              recipes clauseModes selected.erase found declared requestCheck pending.erase.pending pending.erase.pending.compatible freshAction absent plannedCut chosen

theorem capture_from_recipes {hints : SourceContextualHints.Hints receiving} {forest : Forest hints}
    (state : State operations policy contracts tables families required actions annotations world [] outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole forest output demand row)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase.erase (Admission.outsideResources capture.erase.erase)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      State operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨contract, captured, waiting, after, nextDemand, nextRow, step,
    ⟨dependencies, nextPlan, next, _⟩, balanced, bounded, owned, same, sourceInput⟩ :=
    capture_from_recipes_retaining SourceAnnotatedAllocationData.noClauseEvidence state cut isValue selected found
      freshContract freshAction freshAnnotation supported (by
        intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting plannedCut family bodies chosen
        trivial)
  exact ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next.state,
    balanced, bounded, owned, same, sourceInput⟩

end Ash.OneShot.SourceAnnotatedRuntimeState

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.capture_from_recipes

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.capture_from_recipes_retaining
