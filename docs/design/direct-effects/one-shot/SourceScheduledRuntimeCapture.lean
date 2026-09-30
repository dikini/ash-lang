import SourceScheduledRecipeCapture
import SourceDependencyState

/-! The existing runtime allocation proofs now retain the actual scheduled
source forest. The ledger supplies freshness and resource support; the selected
source clause supplies disposal certificates and the operation input type. -/
namespace Ash.OneShot.SourceScheduledExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Saved Annotations)

theorem Run.capture_preserves
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ forest output demand row resultBound)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (contract : SourcePlannedTyping.Contract) (record : CoherentSourceTypes.Owners.Record)
      (captured waiting : SourceScheduledSavedPlans.Saved) (after : Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
      record.annotation = contract.erase.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] []) ∧
      Run operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow resultBound ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  have supported := SourceDependencyState.capture_resource_support cut run.current.support.control (ledger_unique_live run.current.ledger)
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
    raw, nextSource, balance, included, owners, shape, sourceInput⟩ :=
    SourceScheduledState.capture_from_recipes source cut isValue selected found freshContract
      (usageChecks.allocation owner (by simp)) freshAnnotation supported
  obtain ⟨record, resultBinder, annotation, actualScope, permissions, results, sourceExtension, runtimeExtension⟩ :=
    DeclaredCompletionAdmission.coherent_capture_record (contract := contract.erase.erase)
      run.current.source run.current.results run.current.signature fresh raw
      (by obtain ⟨argument, known⟩ := sourceInput; exact ⟨argument.erase.erase, SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known)⟩)
  have coherent : (contracts.insert owner contract).erase.erase = (registry.insert owner record).contracts := by
    rw [SourcePlannedTyping.contracts_erase_insert, SourceDependencyAnnotations.contracts_erase_insert, CoherentSourceTypes.Owners.registry_insert_contracts,
      annotation, run.coherent]
  have freshHandlers : (activations ++ enteredActivations
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after).Nodup := by
    simpa [enteredActivations] using run.current.names.unique
  have update : (registry.insert owner record).runtime.joint.usage =
      advanceUsageTickets policy registry.runtime.joint.usage after [.ticket owner] := by
    rw [CoherentSourceTypes.Owners.registry_insert_runtime, CallableJoint.joint_insert, ScopedPortJoint.usage_insert]
    simp only [advanceUsageTickets, actualScope, permissions]
  have current := DeclaredExecution.assemble_event run.current raw freshOwners freshHandlers checks
    (by simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld, coherent]
          using DeclaredSourceInterfaces.source nextSource.erase.shared)
    (by simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results) update
  have unique : (ownedTickets after.stack).Nodup := by
    cases nextSource with
    | checked _ _ _ _ _ _ _ unique _ _ _ => exact unique
  have allocation : DeclaredClosingInvariant.Allocation operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
      (registry.insert owner record) (ScopedActionUsage.advance actions after [.ticket owner]) [.ticket owner] after.stack := by
    rw [shape]
    exact DeclaredClosingInvariant.capture_allocation
      (by simp [CoherentSourceTypes.Owners.Registry.insert]) isValue (fun disposes => SourceScheduledState.capture_certificate_from_source source cut selected found supported disposes record)
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
    ⟨coherent, current, ?_, _, ScopedActionUsage.raw_step_preserves raw usageChecks usage,
      ScopedActionUsage.raw_step_preserves_history raw history, ?_, ?_⟩, balance, included, owners⟩
  · intro other saved known
    by_cases same : other = owner
    · subst other; simp [ScopedPortJoint.advanceState]
    · have old : annotations other = some saved := by simpa only [SourceScheduledSavedPlans.Annotations.insert, if_neg same] using known
      exact List.mem_append_left _ (run.annotationHistory other saved old)
  · simpa [ScopedPortJoint.advanceState, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld,
      List.append_nil, ScopedActionUsage.advance, shape, Code.substitution_required_actions code parameter isValue] using nextSource
  · simpa [ScopedPortJoint.advanceState, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld,
      List.append_nil] using nextRetained

/-- The existing finite name ledger chooses an owner. The strengthened runtime
invariant supplies annotation freshness for that same choice. -/
theorem Run.capture_progress
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ forest output demand row resultBound)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered) :
    ∃ (owner : Nat) (contract : SourcePlannedTyping.Contract) (record : CoherentSourceTypes.Owners.Record)
      (captured waiting : SourceScheduledSavedPlans.Saved) (after : Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
      record.annotation = contract.erase.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] []) ∧
      Run operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow resultBound ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) run.current.ledger.2
  exact ⟨owner, run.capture_preserves cut isValue selected found fresh⟩

end Ash.OneShot.SourceScheduledExecution

#print axioms Ash.OneShot.SourceScheduledExecution.Run.capture_preserves
#print axioms Ash.OneShot.SourceScheduledExecution.Run.capture_progress
