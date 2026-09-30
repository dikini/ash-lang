import SourceAnnotatedExecutionCapture
import SourceBoundCapture
import SourceConsumingStoredBounds

/-! Capture under the inherited recipe route keeps the exact source snapshot
and installed packets on the combined runtime successor. The selected body has
recipe declarations, so its absent bound annotation is justified by its actual
source check. Explicitly bounded capture remains a separate integration case. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceConsumingStoredBounds (StackBounds HandlerBounds)
open SourceScheduledSavedPlans (Saved)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

/-- The route premise prevents a bounded installed declaration from being
silently treated as inherited. The original recipe source derives the selected
body's declaration check; no future source check or successor is assumed. -/
theorem AtPlan.capture_recipe_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families whole)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (packet : HandlerBounds families handler)
    (_packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (_inherited : packet.admission = .inherited)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshOwners : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (contract : SourcePlannedTyping.Contract) (record : CoherentSourceTypes.Owners.Record)
      (captured : Saved) (after : SourceAnnotatedRuntime.Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ nextStored : StackBounds families after.stack,
      record.annotation = contract.erase.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
            issued, completed⟩, activations⟩ after.erase [.ticket owner] []) ∧
      AtPlan operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        nextSnapshot.plan nextSnapshot.forest output nextDemand nextRow resultBound ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      SourceBoundSnapshots.Captured owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧ nextStored.Admitted (ScopedTyping.resourceWorld issued) required ∧
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port)
        handler.answer handler.scope) := by
  let kept : SourceAnnotatedAllocationData.ClauseEvidence := fun plan forest =>
    ∃ pending : SourceBoundSnapshots.Retained (ScopedTyping.resourceWorld issued) forest,
      SourceBoundSnapshots.Captured owner snapshot ⟨_, plan, .absent, _, _, forest, pending⟩
  obtain ⟨contract, record, captured, waiting, after, nextDemand, nextRow, annotation,
    step, ⟨dependencies, nextPlan, next, clauseKept⟩, balance, included, owners, shape, sourceInput⟩ :=
    run.run.capture_preserves_retaining kept cut isValue selected found freshOwners (by
      intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting plannedCut family bodies chosen
      exact SourceBoundSnapshots.capture_snapshot snapshot plannedCut .absent)
  obtain ⟨pending, moved⟩ := clauseKept
  let nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, nextPlan, .absent, _, _, .live (owner := owner) captured.forest waiting.forest, pending⟩
  have currentAdmitted : nextSnapshot.current.Admitted := by
    obtain ⟨actions, usage, history, source, retained⟩ := next.actions
    cases source with
    | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      apply SourcePlanBounds.Annotation.Admitted.absent
      simpa [SourceAnnotatedRuntime.advanceState, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld]
        using SourceScheduledSourceInterfaces.declared_of_local contextual
  obtain ⟨nextStored, packets⟩ : ∃ nextStored : StackBounds families after.stack,
      nextStored.Admitted (ScopedTyping.resourceWorld issued) required ∧
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port)
        handler.answer handler.scope) := by
    rw [shape]
    exact ⟨stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer handler.scope,
      storedAdmitted.capture cut, HEq.rfl⟩
  exact ⟨contract, record, captured, after, nextDemand, nextRow, nextSnapshot, nextStored,
    annotation, step, next, balance, included, owners, moved, moved.admitted admitted currentAdmitted,
    packets⟩

/-- The existing finite ledger supplies a fresh one-shot owner. -/
theorem AtPlan.capture_recipe_progress_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families whole)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (packet : HandlerBounds families handler)
    (packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (inherited : packet.admission = .inherited)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered) :
    ∃ (owner : Nat) (contract : SourcePlannedTyping.Contract) (record : CoherentSourceTypes.Owners.Record)
      (captured : Saved) (after : SourceAnnotatedRuntime.Configuration)
      (nextDemand : List Nat) (nextRow : Footprint),
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
    ∃ nextStored : StackBounds families after.stack,
      record.annotation = contract.erase.erase ∧
      NamedAccessStep []
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩,
            issued, completed⟩, activations⟩ after.erase [.ticket owner] []) ∧
      AtPlan operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        nextSnapshot.plan nextSnapshot.forest output nextDemand nextRow resultBound ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      SourceBoundSnapshots.Captured owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧ nextStored.Admitted (ScopedTyping.resourceWorld issued) required ∧
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port)
        handler.answer handler.scope) := by
  obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) run.current.ledger.2
  exact ⟨owner, AtPlan.capture_recipe_snapshot_admitted snapshot admitted stored storedAdmitted packet
    packetAt inherited run cut isValue selected found fresh⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.capture_recipe_snapshot_admitted

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.capture_recipe_progress_snapshot_admitted
