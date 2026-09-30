import SourceAnnotatedStoredExecution
import SourceScheduledRuntimeCapture

/-! Shared capture-event assembly. An actual raw transition and its typed
successor are combined with the same current usage/source witness. This reuses
completion and ownership preservation; it is not a source-admission rule. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledSavedPlans (Saved)
open SourceRetainedPlans (Forest)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

/-- Reuse the existing completion, ledger and usage proofs for a capture whose
source successor was established independently. Every action-dependent premise
uses the same action map; packet data remain the actual successor data. -/
theorem AtPackets.assemble_capture {actions : Syntax.UsageTickets}
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ sourcePlan forest output demand row resultBound stored evidence)
    (usage : ConfigurationUsage policy actions
      ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩)
    (history : UsageRegistryHistory actions issued)
    (source : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
      (ScopedTyping.resourceWorld issued) [] [] scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole sourcePlan forest output demand row stored evidence)
    (retained : DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued)
      registry actions whole.erase)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler) (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup)
    {contract : SourcePlannedTyping.Contract} {captured waiting : Saved}
    {after : SourceAnnotatedRuntime.Configuration}
    {nextPlan : SourceDeclarationPlans.Plan dependencies}
    {nextStored : SourceConsumingStoredBounds.StackBounds families after.stack}
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩
      after.erase [.ticket owner] [])
    (nextSource : SourceAnnotatedRuntimeState.AtPackets operations policy (contracts.insert owner contract) tables families required
      (actions.insert owner code.erase.requiredActions) (annotations.insert owner captured) (ScopedTyping.resourceWorld issued)
      [] [] after.scope after.expression after.stack nextPlan
      (Forest.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow nextStored evidence)
    (shape : after = ⟨code.subst parameter operand, .ticket binder owner,
      .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩)
    (sourceInput : ∃ argument, operations requested operation = some (argument, contract.input)) :
    ∃ record : CoherentSourceTypes.Owners.Record,
      record.annotation = contract.erase.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
            issued, completed⟩, activations⟩ after.erase [.ticket owner] []) ∧
      AtPackets operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        nextPlan (Forest.live (owner := owner) captured.forest waiting.forest)
        output nextDemand nextRow resultBound nextStored evidence := by
  have supported := SourceDependencyState.capture_resource_support cut.erase run.current.support.control (ledger_unique_live run.current.ledger)
  have checks := DeclaredExecution.request_access_checks run.current
  have usageChecks := usage_checks_from_allocation_and_access history freshOwners checks
  have fresh : registry owner = none := by
    have absent := ScopedPortJoint.registry_fresh run.current.registry freshOwners
    cases known : registry owner <;>
      simp_all [CoherentSourceTypes.Owners.Registry.runtime, CallableJoint.Registry.joint]
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
          using DeclaredSourceInterfaces.source nextSource.atPlan.state.erase.erase.shared)
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
      (fun disposes => SourceScheduledState.capture_certificate_from_source source.atPlan.state.erase cut.erase selected.erase found supported disposes record)
  have nextRetained := DeclaredClosingInvariant.raw_step_preserves_retained raw retained
    (nextRegistry := registry.insert owner record)
    (by
      intro old previous known
      by_cases same : old = owner
      · subst old; rw [fresh] at known; cases known
      · simp [CoherentSourceTypes.Owners.Registry.insert, same, known])
    (ScopedActionUsage.advance_extends usageChecks.allocation) (List.Subset.refl _) allocation unique
  refine ⟨record, annotation, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
    ⟨coherent, current, ?_, _, ScopedActionUsage.raw_step_preserves raw usageChecks usage,
      ScopedActionUsage.raw_step_preserves_history raw history, ?_, ?_⟩⟩
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

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.assemble_capture
