import SourceAnnotatedStoredRecipeCapture
import SourceAnnotatedStoredCaptureAssembly

/-! Capture derives resource support and registry freshness from the shared
runtime invariant. The successor keeps the actual annotated clause and saved
continuation, with the existing ledger and completion proofs. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledSavedPlans (Saved)

variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

section
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

theorem AtPackets.capture_preserves_retaining_with
    (admitRecipe : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts [] required plans)
    (certifyRecipe : ∀ {world clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) [] world plans)
    (currentEvidence : SourceAnnotatedAllocationData.ClauseEvidence)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ sourcePlan forest output demand row resultBound stored evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler) (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup)
    (recipesAtCapture : ∀ (packet : SourceConsumingStoredBounds.HandlerBounds families handler),
      stored.handlerAt requested = some ⟨handler, packet⟩ →
      evidence (required handler.erase) packet.plans →
      SourcePlannedRecipeDeclarations.Declarations (required handler.erase) packet.plans)
    (evidenceAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      SourcePlannedFrames.recipeEvidence (required handler.erase) plans →
      ∀ {modes}, SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : SourceRetainedPlans.Forest savedHints) → (waiting : SourceRetainedPlans.Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → SourceDependencyAnnotations.Dependencies}
        {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      currentEvidence (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (record : CoherentSourceTypes.Owners.Record)
      (captured waiting : Saved) (after : SourceAnnotatedRuntime.Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
      record.annotation = contract.erase.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
            issued, completed⟩, activations⟩ after.erase [.ticket owner] []) ∧
      (∃ dependencies, ∃ nextPlan : SourceDeclarationPlans.Plan dependencies,
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer handler.scope) ∧
      AtPackets operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        nextPlan (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow resultBound nextStored evidence ∧
      currentEvidence nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  have supported := SourceDependencyState.capture_resource_support cut.erase run.current.support.control (ledger_unique_live run.current.ledger)
  have checks := DeclaredExecution.request_access_checks run.current
  have usageChecks := usage_checks_from_allocation_and_access history freshOwners checks
  have freshAnnotation : annotations owner = none := by
    cases known : annotations owner with
    | none => rfl
    | some captured =>
        have used := run.annotationHistory owner captured known
        exact False.elim ((List.nodup_append.mp freshOwners).2.2 (.ticket owner) used
          (.ticket owner) (by simp) rfl)
  have fresh : registry owner = none := by
    have absent := ScopedPortJoint.registry_fresh run.current.registry freshOwners
    cases known : registry owner <;>
      simp_all [CoherentSourceTypes.Owners.Registry.runtime, CallableJoint.Registry.joint]
  have freshContract : contracts owner = none := by
    have erased : contracts.erase.erase owner = none := by
      rw [run.coherent]
      simp [CoherentSourceTypes.Owners.Registry.contracts, fresh]
    simpa only [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, Option.map_eq_none_iff] using erased
  obtain ⟨contract, captured, waiting, after, nextDemand, nextRow,
    raw, ⟨dependencies, nextPlan, nextStored, packetsSame, nextSource, clauseKept⟩, balance, included, owners, shape, sourceInput⟩ :=
    SourceAnnotatedStoredRuntimeCapture.capture_from_recipes_retaining_with admitRecipe certifyRecipe currentEvidence source cut isValue selected found freshContract
      (usageChecks.allocation owner (by simp)) freshAnnotation supported recipesAtCapture evidenceAtCapture
  obtain ⟨record, annotation, step, next⟩ :=
    run.assemble_capture usage history source retained cut isValue selected found freshOwners raw nextSource shape sourceInput
  exact ⟨contract, record, captured, waiting, after, nextDemand, nextRow, annotation, step,
    ⟨_, nextPlan, nextStored, packetsSame, next, clauseKept⟩, balance, included, owners, shape, sourceInput⟩

end

/-- Original recipe-only specialization of the shared capture proof. -/
theorem AtPackets.capture_preserves_retaining (currentEvidence : SourceAnnotatedAllocationData.ClauseEvidence)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ sourcePlan forest output demand row resultBound stored)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler) (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup)
    (evidenceAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      SourcePlannedFrames.recipeEvidence (required handler.erase) plans →
      ∀ {modes}, SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : SourceRetainedPlans.Forest savedHints) → (waiting : SourceRetainedPlans.Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → SourceDependencyAnnotations.Dependencies}
        {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      currentEvidence (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (record : CoherentSourceTypes.Owners.Record)
      (captured waiting : Saved) (after : SourceAnnotatedRuntime.Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
      record.annotation = contract.erase.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
            issued, completed⟩, activations⟩ after.erase [.ticket owner] []) ∧
      (∃ dependencies, ∃ nextPlan : SourceDeclarationPlans.Plan dependencies,
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer handler.scope) ∧
      AtPackets operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        nextPlan (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow resultBound nextStored ∧
      currentEvidence nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) :=
  AtPackets.capture_preserves_retaining_with (fun checked => checked) (fun checked => checked.certified)
    currentEvidence run cut isValue selected found freshOwners
    (fun _ _ recipes => recipes) evidenceAtCapture

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.capture_preserves_retaining

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.capture_preserves_retaining_with
