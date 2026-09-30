import SourceBoundCapture
import SourceConsumingTypedAllocation

/-! Join the source-generated current bounds, exact selected typed clause,
original retained metadata and installed packets at one actual capture cut.
This prepares the snapshot data; complete runtime-state preservation remains
separate from this typed allocation interface. -/
namespace Ash.OneShot.SourceAnnotatedAllocationData
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceContextualHintChecking (Matches)
open SourceScheduledChecks (Local Pending)

theorem capture_snapshot_data
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    (physical : SourceAnnotatedRuntime.HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required snapshot.hints whole.erase)
    (stored : SourceConsumingStoredBounds.StackBounds families whole)
    (storedAdmitted : stored.Admitted world required)
    (packet : SourceConsumingStoredBounds.HandlerBounds families handler)
    (storedKnown : stored.handlerAt requested = some ⟨handler, packet⟩)
    (clauseModes : SourceTemplates.ClauseModes handler.clauses.erase (tables handler.erase))
    (source : SourceAnnotatedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler.erase) packet.plans)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) snapshot.forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world snapshot.forest .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole.erase)
    (operationKnown : operations requested operation = some (argument, input))
    {actualSavedHints : Hints actualSavedScope} {actualWaitingHints : Hints actualWaitingScope}
    {actualSaved : Forest actualSavedHints} {actualWaiting : Forest actualWaitingHints}
    (actualCut : SourceScheduledNeutral.Cut requested operation offered modes snapshot.forest actualSaved actualWaiting)
    (actualSelected : SourcePlannedRecipeDeclarations.Selected operation actualSavedScope.held packet.plans
      parameter binder code.erase bodies)
    (captureSource : packet.admission = .bounded → SourceConsumingCaptureInput.Source world snapshot.forest actualSaved actualWaiting)
    (checked : ∀ bounded, (captureSource bounded).Check outward actions
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner packet.bounds code.erase.requiredActions actualCut closeOutside)
    (supplied : SourceContextualHints.checkRequirements actualWaitingScope (required handler.erase) = true) :
    ∃ resumeEffects closeEffects, ∃ currentBounds : SourcePlanBounds.Annotation world (bodies owner),
    ∃ pending : SourceBoundSnapshots.Retained world (.live (owner := owner) actualSaved actualWaiting),
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      TypedClauseDataAtPlan operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail)
        world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer allowed _ actualSaved actualWaiting
        resumeEffects closeEffects bodies ∧
      SourceBoundSnapshots.Captured owner snapshot (⟨_, bodies owner, currentBounds, _, _, .live (owner := owner) actualSaved actualWaiting, pending⟩ :
        SourceBoundSnapshots.Snapshot world) ∧
      (⟨_, bodies owner, currentBounds, _, _, .live (owner := owner) actualSaved actualWaiting, pending⟩ :
        SourceBoundSnapshots.Snapshot world).Admitted ∧
      (packet.admission = .bounded →
        ∃ annotation : SourceScheduledCapabilityAnnotations.Code world (bodies owner)
            (.live (owner := owner) actualSaved actualWaiting),
          SourcePlanBounds.ofCode annotation = currentBounds ∧ annotation.Valid outward
            (actions.insert owner code.erase.requiredActions)
            (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)) ∧
      (packet.admission = .inherited → currentBounds = .absent) ∧
      (stored.capture physical owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer handler.scope).Admitted
        world required := by
  obtain ⟨resumeEffects, closeEffects, currentBounds, resume, close, typed, currentAdmitted, generated, inherited, preserved⟩ :=
    capture_typed_data_from_bounds_at_selected physical matched stored storedAdmitted packet storedKnown clauseModes source
      selected found rowAvailable declared request retained fresh absent operationKnown actualCut actualSelected captureSource checked supplied
  obtain ⟨pending, captured⟩ := SourceBoundSnapshots.capture_snapshot snapshot actualCut currentBounds (owner := owner)
  exact ⟨resumeEffects, closeEffects, currentBounds, pending, resume, close, typed, captured,
    captured.admitted snapshotAdmitted currentAdmitted, generated, inherited, preserved⟩

end Ash.OneShot.SourceAnnotatedAllocationData

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.capture_snapshot_data
