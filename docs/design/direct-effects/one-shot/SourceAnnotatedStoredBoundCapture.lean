import SourceAnnotatedStoredExecutionCapture
import SourceBoundCapture
import SourceConsumingStoredBounds

/-! Capture under the inherited recipe route preserves the joint packet/source
invariant and admitted snapshot on the actual combined runtime successor. The selected body has
recipe declarations, so its absent bound annotation is justified by its actual
source check. Explicitly bounded capture remains a separate integration case. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceConsumingStoredBounds (StackBounds HandlerBounds)
open SourceScheduledSavedPlans (Saved)

open SourceScheduledSourceInterfaces (Declared declared_of_local)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)

private theorem recipe_declared
    (recipe : SourcePlannedClauseRecipes.Recipe rights required plans provided) :
    Declared world (signature (plans owner)) := by
  induction recipe generalizing world with
  | resume permission | dispose permission => exact .invoke
  | silent empty rest ih =>
      exact .sequence (declared_of_local (SourceScheduledClauses.silent
        (outward := []) (actions := fun _ => none) (phases := fun _ => .consumed)
        (forest := Forest.nil) empty)) ih
  | request rest ih | localRequest member rest ih => exact .sequence (.sequence .pure .request) ih
  | handledRequest shape rest ih =>
      exact .sequence (declared_of_local (SourceScheduledClauses.handled_request_local
        (outward := []) (actions := fun _ => none) (phases := fun _ => .consumed)
        (forest := Forest.nil) (shape owner))) ih
  | resource body ih => exact .resource (fun identity fresh => ih identity)
  | cleanup rest ih => exact .cleanup .pure ih
  | choice left right ihLeft ihRight => exact .choice ihLeft ihRight

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

/- The route premise prevents a bounded installed declaration from being
silently treated as inherited. The original recipe source derives the selected
body's declaration check; no future source check or successor is assumed. -/
section
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

theorem AtPackets.capture_recipe_snapshot_admitted_with
    (admitRecipe : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts [] required plans)
    (certifyRecipe : ∀ {world clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) [] world plans)
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families whole)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (packet : HandlerBounds families handler)
    (packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (inherited : packet.admission = .inherited)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored evidence)
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
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port)
        handler.answer handler.scope) ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  let kept : SourceAnnotatedAllocationData.ClauseEvidence := fun plan forest =>
    ∃ pending : SourceBoundSnapshots.Retained (ScopedTyping.resourceWorld issued) forest,
      SourceBoundSnapshots.Captured owner snapshot ⟨_, plan, .absent, _, _, forest, pending⟩ ∧
      (SourcePlanBounds.Annotation.absent (world := ScopedTyping.resourceWorld issued) (plan := plan)).Admitted
  obtain ⟨contract, record, captured, waiting, after, nextDemand, nextRow, annotation,
    step, ⟨dependencies, nextPlan, nextStored, packetsSame, next, clauseKept⟩, balance, included, owners, shape, sourceInput⟩ :=
    run.capture_preserves_retaining_with admitRecipe certifyRecipe kept cut isValue selected found freshOwners (by
      intro actual actualAt _
      have same : actual = packet := eq_of_heq (Sigma.mk.inj (Option.some.inj (actualAt.symm.trans packetAt))).2
      subst actual
      cases storedAdmitted.handlerAt packetAt with
      | inherited _ recipes => exact recipes
      | bounded route source checked => cases inherited.symm.trans route) (by
      intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting plannedCut family bodies chosen
      obtain ⟨pending, moved⟩ := SourceBoundSnapshots.capture_snapshot snapshot plannedCut .absent (owner := owner)
      obtain ⟨needed, recipe, included⟩ := recipes.selected chosen
      exact ⟨pending, moved, .absent (recipe_declared recipe)⟩)
  obtain ⟨pending, moved, currentAdmitted⟩ := clauseKept
  let nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, nextPlan, .absent, _, _, .live (owner := owner) captured.forest waiting.forest, pending⟩
  have packets : nextStored.Admitted (ScopedTyping.resourceWorld issued) required ∧
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port)
        handler.answer handler.scope) := by
    cases shape
    cases eq_of_heq packetsSame
    exact ⟨storedAdmitted.capture cut, HEq.rfl⟩
  exact ⟨contract, record, captured, after, nextDemand, nextRow, nextSnapshot, nextStored,
    annotation, step, next, balance, included, owners, moved, moved.admitted admitted currentAdmitted,
    packets.1, packets.2, shape, sourceInput⟩

end

/-- Original recipe-only specialization. -/
theorem AtPackets.capture_recipe_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families whole)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (packet : HandlerBounds families handler)
    (_packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (_inherited : packet.admission = .inherited)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored)
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
      AtPackets operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        nextSnapshot.plan nextSnapshot.forest output nextDemand nextRow resultBound nextStored ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      SourceBoundSnapshots.Captured owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧ nextStored.Admitted (ScopedTyping.resourceWorld issued) required ∧
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port)
        handler.answer handler.scope) := by
  obtain ⟨contract, record, captured, after, nextDemand, nextRow, nextSnapshot, nextStored,
    annotation, step, next, balance, included, owners, moved, nextAdmitted, packets, same, _, _⟩ :=
    AtPackets.capture_recipe_snapshot_admitted_with (fun checked => checked) (fun checked => checked.certified)
      snapshot admitted stored storedAdmitted packet _packetAt _inherited run cut isValue selected found freshOwners
  exact ⟨contract, record, captured, after, nextDemand, nextRow, nextSnapshot, nextStored,
    annotation, step, next, balance, included, owners, moved, nextAdmitted, packets, same⟩

/-- The existing finite ledger supplies a fresh one-shot owner. -/
theorem AtPackets.capture_recipe_progress_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (stored : StackBounds families whole)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (packet : HandlerBounds families handler)
    (packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (inherited : packet.admission = .inherited)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row resultBound stored)
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
      AtPackets operations declarations policy (contracts.insert owner contract) (registry.insert owner record)
        tables families required (annotations.insert owner captured)
        (SourceAnnotatedRuntime.advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩ after [.ticket owner] [])
        nextSnapshot.plan nextSnapshot.forest output nextDemand nextRow resultBound nextStored ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      SourceBoundSnapshots.Captured owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧ nextStored.Admitted (ScopedTyping.resourceWorld issued) required ∧
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port)
        handler.answer handler.scope) := by
  obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) run.current.ledger.2
  exact ⟨owner, AtPackets.capture_recipe_snapshot_admitted snapshot admitted stored storedAdmitted packet
    packetAt inherited run cut isValue selected found fresh⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.capture_recipe_snapshot_admitted

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.capture_recipe_progress_snapshot_admitted

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.capture_recipe_snapshot_admitted_with
