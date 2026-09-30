import SourceConsumingReceiverGeneration

/-! Reuse the typed capture allocator after a neutral receiver change. Original
contextual source admission and primitive finite checks generate the actual
certificate; runtime ownership, packets and snapshots use the existing proof. -/
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

/-- Original structural admission survives a neutral receiver expansion at
this capture boundary. The allocator supplies the same actual successor,
admitted packets and exact fresh-owner increment as its established theorem. -/
theorem capture_from_expanded_source
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification [])
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
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
    {originalWholeScope originalFrontScope originalSavedScope originalWaitingScope : SourceDependencyCapture.Scope}
    {originalWholeHints : Hints originalWholeScope} {originalFrontHints : Hints originalFrontScope}
    {originalSavedHints : Hints originalSavedScope} {originalWaitingHints : Hints originalWaitingScope}
    {originalWhole : Forest originalWholeHints} {originalFront : Forest originalFrontHints}
    {originalSaved : Forest originalSavedHints} {originalWaiting : Forest originalWaitingHints}
    {context : SourceConsumingCleanupAdmission.Context world owner [] (actions.insert owner code.erase.requiredActions)
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
      originalWhole originalFront originalSaved originalWaiting}
    (original : SourceConsumingCleanupAdmission.At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired (actions.insert owner code.erase.requiredActions)
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
      originalWholeScope originalWaitingScope context.before)
    (changed : SourceScheduledNeutral.Expansion originalWhole (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      AtPackets operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack
        nextSnapshot.plan nextSnapshot.forest output nextDemand nextRow nextStored evidence ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      SourceBoundSnapshots.Captured owner snapshot nextSnapshot ∧
      nextSnapshot.Admitted ∧ nextStored.Admitted world required ∧
      HEq nextSnapshot.forest (Forest.live (owner := owner) captured.forest waiting.forest) ∧
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port)
        handler.answer handler.scope) ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨annotation, valid, _⟩ := SourceConsumingCleanupAdmission.SelectedSource.capture_expanding
    snapshot snapshotAdmitted declarationBounded plannedCut plannedSelected selectedSource original checked changed
  exact capture_from_certificate_snapshot laws snapshot snapshotAdmitted stored storedAdmitted packet packetAt bounded
    state cut isValue selected found freshContract freshAction freshAnnotation supported declared
    (.site plannedCut plannedSelected annotation) valid

end Ash.OneShot.SourceAnnotatedStoredRuntimeCapture

#print axioms Ash.OneShot.SourceAnnotatedStoredRuntimeCapture.capture_from_expanded_source
