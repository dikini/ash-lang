import SourceAnnotatedStoredRuntimeCapture

/-! Existing structural clause recipes discharge capture-site requirements
using the actual request and pending schedule. This specialization does not
extend the recipe grammar or assume a successful future body. -/
namespace Ash.OneShot.SourceAnnotatedStoredRuntimeCapture
open SourceAnnotatedRuntimeState (AtPackets)
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceRetainedPlans (Forest)
open SourcePlanSignatures (signature)

variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

section
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

theorem capture_from_recipes_retaining_with
    (admitRecipe : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts [] required plans)
    (certifyRecipe : ∀ {world clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) [] world plans)
    (currentEvidence : SourceAnnotatedAllocationData.ClauseEvidence) {hints : SourceContextualHints.Hints receiving} {forest : Forest hints}
    (state : AtPackets operations policy contracts tables families required actions annotations world [] outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole sourcePlan forest output demand row stored evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase.erase (Admission.outsideResources capture.erase.erase))
    (recipesAtCapture : ∀ (packet : SourceConsumingStoredBounds.HandlerBounds families handler),
      stored.handlerAt requested = some ⟨handler, packet⟩ →
      evidence (required handler.erase) packet.plans →
      SourcePlannedRecipeDeclarations.Declarations (required handler.erase) packet.plans)
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
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer handler.scope) ∧
      AtPackets operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack nextPlan
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow nextStored evidence ∧
      currentEvidence nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  apply capture_preserves_retaining currentEvidence state cut isValue selected found freshContract freshAction freshAnnotation supported
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
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
                SourceDependencyFrames.capture_segments cut.erase pending.forget.erase.source.source.erase
              cases frame with
              | handler scope annotation clauses coverage unique declarations capabilities modes => exact modes
            have freshErased : contracts.erase.erase owner = none := by
              simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
            have absent := RecursiveCapture.fresh_unowned pending.forget.erase.source.source.erase.erase.source.erase freshErased
            intro packet packetAt declarationEvidence modes declared capturedScope tailScope savedHints waitingHints saved waiting plannedCut family bodies chosen
            have recipes := recipesAtCapture packet packetAt declarationEvidence
            refine ⟨?_, evidenceAtCapture recipes declared saved waiting plannedCut chosen⟩
            exact SourceScheduledAllocationData.capture_requirements_from_recipe_with admitRecipe certifyRecipe cut.erase pending.forget.erase.source.source.matches
              recipes clauseModes selected.erase found declared requestCheck pending.forget.erase.pending pending.forget.erase.pending.compatible freshAction absent plannedCut chosen

end

/-- Original recipe-only specialization of the shared capture proof. -/
theorem capture_from_recipes_retaining (currentEvidence : SourceAnnotatedAllocationData.ClauseEvidence) {hints : SourceContextualHints.Hints receiving} {forest : Forest hints}
    (state : AtPackets operations policy contracts tables families required actions annotations world [] outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole sourcePlan forest output demand row stored)
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
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer handler.scope) ∧
      AtPackets operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack nextPlan
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow nextStored ∧
      currentEvidence nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) :=
  capture_from_recipes_retaining_with (fun checked => checked) (fun checked => checked.certified)
    currentEvidence state cut isValue selected found freshContract freshAction freshAnnotation supported
    (fun _ _ recipes => recipes) evidenceAtCapture

end Ash.OneShot.SourceAnnotatedStoredRuntimeCapture

#print axioms Ash.OneShot.SourceAnnotatedStoredRuntimeCapture.capture_from_recipes_retaining

#print axioms Ash.OneShot.SourceAnnotatedStoredRuntimeCapture.capture_from_recipes_retaining_with
