import SourceConsumingContextualCapture
import SourceBoundRecords

/-! The existing typed capture allocator now consumes contextual source
admission rather than a successful target-certificate premise. Its original
source, packet, support, ownership and bound-snapshot invariants are reused. -/
namespace Ash.OneShot.SourceAnnotatedStoredRuntimeCapture
open SourceAnnotatedRuntimeState (AtPackets)
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingStoredBounds (StackBounds HandlerBounds)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

/-- Structural source checking supplies the actual capture certificate; the
established allocator preserves the original snapshot and installed packets,
performs the actual raw step, and adds exactly the fresh owner to its inventory. -/
theorem capture_from_contextual_source
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification [])
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {Payload : SourceBoundSnapshots.RecordFamily world} (records : snapshot.pending.Records Payload)
    (stored : StackBounds families whole) (storedAdmitted : stored.Admitted world required)
    (packet : HandlerBounds families handler)
    (packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (bounded : packet.admission = .bounded)
    (state : AtPackets operations policy contracts tables families required actions annotations world [] outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole snapshot.plan snapshot.forest output demand row stored evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase.erase (Admission.outsideResources capture.erase.erase))
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts [] required plans → nested.accepts required plans)
    (declarationSource : SourceConsumingClauseAnnotations.Declarations world packet.plans)
    (declarationBounded : SourceConsumingClauseAnnotations.Bounded packet.bounds declarationSource (required handler.erase))
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (plannedCut : SourceScheduledNeutral.Cut requested operation offered modes snapshot.forest saved waiting)
    (plannedSelected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held packet.plans parameter binder code.erase bodies)
    {body : SourceConsumingClauseAnnotations.Body world owner (bodies owner)}
    (selectedSource : SourceConsumingClauseAnnotations.SelectedSource owner declarationSource plannedSelected body)
    (source : SourceScheduledCapabilityAnnotations.Retained world snapshot.forest .nil)
    (captureSource : SourceScheduledCapabilityAnnotations.CaptureSource [] actions
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) plannedCut source code.erase.requiredActions)
    (permits : code.erase.requiredActions.dispose = true → offered.dispose = true)
    (supplied : SourceContextualHints.checkRequirements waitingScope (required handler.erase) = true)
    (absent : owner ∉ SourceDependencyOwners.owners snapshot.scope)
    (contextual : SourceConsumingCleanupAdmission.At laws project body
      (SourceConsumingCleanupAdmission.Context.of_request laws project plannedCut source
        code.erase.requiredActions captureSource permits freshAction absent)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
    ∃ nextRecords : nextSnapshot.pending.Records Payload,
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      AtPackets operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack
        nextSnapshot.plan nextSnapshot.forest output nextDemand nextRow nextStored evidence ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      SourceBoundSnapshots.Captured owner snapshot nextSnapshot ∧
      SourceBoundSnapshots.RecordCapture owner Payload records nextRecords ∧
      nextSnapshot.Admitted ∧ nextStored.Admitted world required ∧
      HEq nextSnapshot.forest (Forest.live (owner := owner) captured.forest waiting.forest) ∧
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port)
        handler.answer handler.scope) ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨certificate, checked⟩ := SourceConsumingCleanupAdmission.SelectedSource.capture_certificate
    laws project snapshot snapshotAdmitted declarationBounded plannedCut plannedSelected selectedSource
    source captureSource permits supplied freshAction absent contextual
  obtain ⟨contract, captured, waiting, after, nextDemand, nextRow, nextSnapshot, nextStored,
    raw, next, balance, included, owners, moved, retained⟩ :=
    capture_from_certificate_snapshot laws snapshot snapshotAdmitted stored storedAdmitted packet packetAt bounded
      state cut isValue selected found freshContract freshAction freshAnnotation supported declared certificate checked
  obtain ⟨nextRecords, carried⟩ := moved.carry_records records
  exact ⟨contract, captured, waiting, after, nextDemand, nextRow, nextSnapshot, nextStored,
    nextRecords, raw, next, balance, included, owners, moved, carried, retained⟩

end Ash.OneShot.SourceAnnotatedStoredRuntimeCapture

#print axioms Ash.OneShot.SourceAnnotatedStoredRuntimeCapture.capture_from_contextual_source
