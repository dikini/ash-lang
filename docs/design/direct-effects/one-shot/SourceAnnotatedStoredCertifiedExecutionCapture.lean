import SourceAnnotatedStoredCaptureAssembly
import SourceAnnotatedStoredCertifiedCapture

/-! Structural capture certificates reach the combined execution invariant.
The certificate check is paired with the same current action/source witness;
shared capture assembly supplies completion, ledger and ownership preservation.
Deriving the certificate check from initial source remains a separate obligation. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceScheduledSavedPlans (Saved)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

theorem AtPackets.capture_certificate_retaining
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification [])
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (snapshotAdmitted : snapshot.Admitted)
    (stored : SourceConsumingStoredBounds.StackBounds families whole)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (packet : SourceConsumingStoredBounds.HandlerBounds families handler)
    (packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (bounded : packet.admission = .bounded)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler) (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (certificate : SourceScheduledCaptureAnnotations.Capture (ScopedTyping.resourceWorld issued) owner requested operation offered modes
      packet.plans parameter binder code.erase snapshot.forest)
    (checked : ∃ actions,
      ConfigurationUsage policy actions ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope
        (.perform hint (Instantiation.freezeEffect requested) operation operand) whole snapshot.plan snapshot.forest output demand row stored evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued) registry actions whole.erase ∧
      certificate.Valid [] actions (OwnerPhaseTransitions.available (ownedTickets whole.erase))) :
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
      SourceBoundSnapshots.CapturedBounds snapshot owner nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨actions, usage, history, source, retained, sourceChecked⟩ := checked
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
    SourceAnnotatedStoredRuntimeCapture.capture_from_certificate_retaining laws snapshot snapshotAdmitted stored storedAdmitted packet packetAt bounded source
      cut isValue selected found freshContract (usageChecks.allocation owner (by simp)) freshAnnotation supported declared certificate sourceChecked
  obtain ⟨record, annotation, step, next⟩ :=
    run.assemble_capture usage history source retained cut isValue selected found freshOwners raw nextSource shape sourceInput
  exact ⟨contract, record, captured, waiting, after, nextDemand, nextRow, annotation, step,
    ⟨_, nextPlan, nextStored, packetsSame, next, clauseKept⟩, balance, included, owners, shape, sourceInput⟩

/-- The same combined successor carries admitted independent bound metadata and
actual installed packets. No reconstructed annotation supplies replacement bounds. -/
theorem AtPackets.capture_certificate_snapshot_admitted
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification [])
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (snapshotAdmitted : snapshot.Admitted)
    (stored : SourceConsumingStoredBounds.StackBounds families whole)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (packet : SourceConsumingStoredBounds.HandlerBounds families handler)
    (packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (bounded : packet.admission = .bounded)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler) (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (certificate : SourceScheduledCaptureAnnotations.Capture (ScopedTyping.resourceWorld issued) owner requested operation offered modes
      packet.plans parameter binder code.erase snapshot.forest)
    (checked : ∃ actions,
      ConfigurationUsage policy actions ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ ∧
      UsageRegistryHistory actions issued ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations
        (ScopedTyping.resourceWorld issued) [] [] scope
        (.perform hint (Instantiation.freezeEffect requested) operation operand) whole snapshot.plan snapshot.forest output demand row stored evidence ∧
      DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld issued) registry actions whole.erase ∧
      certificate.Valid [] actions (OwnerPhaseTransitions.available (ownedTickets whole.erase))) :
    ∃ (contract : SourcePlannedTyping.Contract) (record : CoherentSourceTypes.Owners.Record)
      (captured waiting : Saved) (after : SourceAnnotatedRuntime.Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
      ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
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
        nextSnapshot.plan nextSnapshot.forest output nextDemand nextRow resultBound nextStored evidence ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      SourceBoundSnapshots.Captured owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧ nextStored.Admitted (ScopedTyping.resourceWorld issued) required ∧
      HEq nextSnapshot.forest (SourceRetainedPlans.Forest.live (owner := owner) captured.forest waiting.forest) ∧
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port)
        handler.answer handler.scope) ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨contract, record, captured, waiting, after, nextDemand, nextRow, annotation,
    step, ⟨dependencies, nextPlan, nextStored, packetsSame, next, capturedBounds⟩,
    balance, included, owners, shape, sourceInput⟩ :=
    run.capture_certificate_retaining laws snapshot snapshotAdmitted stored storedAdmitted packet packetAt bounded
      cut isValue selected found freshOwners declared certificate checked
  obtain ⟨current, pending, moved, admitted⟩ := capturedBounds
  let nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, nextPlan, current, _, _, .live (owner := owner) captured.forest waiting.forest, pending⟩
  have packets : nextStored.Admitted (ScopedTyping.resourceWorld issued) required := by
    cases shape
    cases eq_of_heq packetsSame
    exact storedAdmitted.capture cut
  exact ⟨contract, record, captured, waiting, after, nextDemand, nextRow, nextSnapshot, nextStored,
    annotation, step, next, balance, included, owners, moved, admitted, packets, HEq.rfl, packetsSame, shape, sourceInput⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.capture_certificate_retaining

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.capture_certificate_snapshot_admitted
