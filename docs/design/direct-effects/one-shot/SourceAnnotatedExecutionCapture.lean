import SourceAnnotatedRuntimeDisposal
import SourceScheduledRuntimeCapture

/-! Capture derives resource support and registry freshness from the shared
runtime invariant. The successor keeps the actual annotated clause and saved
continuation, with the existing ledger and completion proofs. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledSavedPlans (Saved)

variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

theorem Run.capture_preserves_retaining (currentEvidence : SourceAnnotatedAllocationData.ClauseEvidence)
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ forest output demand row resultBound)
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
      AtPlan operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        nextPlan (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow resultBound ∧
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
    raw, ⟨dependencies, nextPlan, nextSource, clauseKept⟩, balance, included, owners, shape, sourceInput⟩ :=
    SourceAnnotatedRuntimeState.capture_from_recipes_retaining currentEvidence source cut isValue selected found freshContract
      (usageChecks.allocation owner (by simp)) freshAnnotation supported evidenceAtCapture
  obtain ⟨record, resultBinder, annotation, actualScope, permissions, results, sourceExtension, runtimeExtension⟩ :=
    DeclaredCompletionAdmission.coherent_capture_record (contract := contract.erase.erase)
      run.current.source run.current.results run.current.signature fresh raw
      (by obtain ⟨argument, known⟩ := sourceInput; exact ⟨argument.erase.erase, SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known)⟩)
  have coherent : (contracts.insert owner contract).erase.erase = (registry.insert owner record).contracts := by
    rw [SourcePlannedTyping.contracts_erase_insert, SourceDependencyAnnotations.contracts_erase_insert, CoherentSourceTypes.Owners.registry_insert_contracts,
      annotation, run.coherent]
  have freshHandlers : (activations ++ enteredActivations
      ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase).Nodup := by
    simpa [enteredActivations, SourceAnnotatedRuntime.NamedState.erase] using run.current.names.unique
  have update : (registry.insert owner record).runtime.joint.usage =
      advanceUsageTickets policy registry.runtime.joint.usage after.erase [.ticket owner] := by
    rw [CoherentSourceTypes.Owners.registry_insert_runtime, CallableJoint.joint_insert, ScopedPortJoint.usage_insert]
    simp only [advanceUsageTickets, actualScope, permissions]
  have current := DeclaredExecution.assemble_event run.current raw freshOwners freshHandlers checks
    (by simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld, coherent,
        SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase]
          using DeclaredSourceInterfaces.source nextSource.state.erase.erase.shared)
    (by simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results) update
  have unique : (ownedTickets after.stack.erase).Nodup := by
    cases nextSource with
    | checked _ _ _ _ _ _ _ unique _ _ _ => exact unique
  have allocation : DeclaredClosingInvariant.Allocation operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
      (registry.insert owner record) (ScopedActionUsage.advance actions after.erase [.ticket owner]) [.ticket owner] after.stack.erase := by
    rw [shape]
    simp only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedCode.Term.erase_subst]
    exact DeclaredClosingInvariant.capture_allocation
      (by simp [CoherentSourceTypes.Owners.Registry.insert]) isValue
      (fun disposes => SourceScheduledState.capture_certificate_from_source source.erase cut.erase selected.erase found supported disposes record)
  have nextRetained := DeclaredClosingInvariant.raw_step_preserves_retained raw retained
    (nextRegistry := registry.insert owner record)
    (by
      intro old previous known
      by_cases same : old = owner
      · subst old; rw [fresh] at known; cases known
      · simp [CoherentSourceTypes.Owners.Registry.insert, same, known])
    (ScopedActionUsage.advance_extends usageChecks.allocation) (List.Subset.refl _) allocation unique
  refine ⟨contract, record, captured, waiting, after, nextDemand, nextRow, annotation,
    ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
    ⟨_, nextPlan, ⟨coherent, current, ?_, _, ScopedActionUsage.raw_step_preserves raw usageChecks usage,
      ScopedActionUsage.raw_step_preserves_history raw history, ?_, ?_⟩, clauseKept⟩, balance, included, owners, shape, sourceInput⟩
  · intro other saved known
    by_cases same : other = owner
    · subst other; simp [SourceAnnotatedRuntime.advanceState]
    · have old : annotations other = some saved := by simpa only [SourceScheduledSavedPlans.Annotations.insert, if_neg same] using known
      exact List.mem_append_left _ (run.annotationHistory other saved old)
  · simpa [SourceAnnotatedRuntime.advanceState, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld,
      List.append_nil, ScopedActionUsage.advance, shape, SourceAnnotatedRuntime.Configuration.erase,
      SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedCode.Term.erase_subst,
      Code.substitution_required_actions code.erase parameter isValue] using nextSource
  · simpa [SourceAnnotatedRuntime.advanceState, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld,
      List.append_nil, SourceAnnotatedRuntime.Configuration.erase] using nextRetained

theorem Run.capture_preserves
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ forest output demand row resultBound)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler) (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup) :
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
      Run operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow resultBound ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨contract, record, captured, waiting, after, nextDemand, nextRow, annotation,
    step, ⟨dependencies, nextPlan, next, _⟩, balance, included, owners, shape, sourceInput⟩ :=
    run.capture_preserves_retaining SourceAnnotatedAllocationData.noClauseEvidence cut isValue selected found freshOwners (by
      intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting plannedCut family bodies chosen
      trivial)
  exact ⟨contract, record, captured, waiting, after, nextDemand, nextRow, annotation,
    step, next.run, balance, included, owners, shape, sourceInput⟩

/-- Choose the fresh continuation owner from the existing finite ledger. -/
theorem Run.capture_progress
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ forest output demand row resultBound)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler) (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered) :
    ∃ (owner : Nat) (contract : SourcePlannedTyping.Contract) (record : CoherentSourceTypes.Owners.Record)
      (captured waiting : Saved) (after : SourceAnnotatedRuntime.Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
      record.annotation = contract.erase.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
            issued, completed⟩, activations⟩ after.erase [.ticket owner] []) ∧
      Run operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow resultBound ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase := by
  obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) run.current.ledger.2
  obtain ⟨contract, record, captured, waiting, after, nextDemand, nextRow, annotation,
    step, next, balance, included, owners, _, _⟩ := run.capture_preserves cut isValue selected found fresh
  exact ⟨owner, contract, record, captured, waiting, after, nextDemand, nextRow,
    annotation, step, next, balance, included, owners⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.capture_preserves

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.capture_progress

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.capture_preserves_retaining
