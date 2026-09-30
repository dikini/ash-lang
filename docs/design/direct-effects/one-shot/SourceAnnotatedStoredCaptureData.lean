import SourceAnnotatedStoredCuts
import SourceAnnotatedBoundCaptureData

/-! A joint runtime source derives the selected packet's exact declaration
interface. Capture generation reuses that source and the established bounded
or inherited annotation proof; it no longer asks for an independent packet
source witness. Finite source checks remain explicit at this boundary. -/
namespace Ash.OneShot.SourceAnnotatedAllocationData
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceContextualHintChecking (Matches)
open SourceScheduledChecks (Local Pending)

theorem capture_snapshot_from_stored_source
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    (physical : SourceAnnotatedRuntime.HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required snapshot.hints whole.erase)
    (stored : SourceConsumingStoredBounds.StackBounds families whole)
    (storedAdmitted : stored.Admitted world required)
    (packet : SourceConsumingStoredBounds.HandlerBounds families handler)
    (storedKnown : stored.handlerAt requested = some ⟨handler, packet⟩)
    (runtime : SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world whole sourceInput sourceOutput sourceDemand
      sourceRequirements sourceRecords snapshot.forest outside incoming outgoing stored)
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
    ∃ (answer : SourcePlannedTyping.Value) (allowed : List Instance), ∃ resumeEffects closeEffects, ∃ currentBounds : SourcePlanBounds.Annotation world (bodies owner),
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
  obtain ⟨answer, residual, capturedDemand, waitingDemand, capturedRequirements, waitingRequirements,
    capturedRecords, waitingRecords, capturedScope, waitingScope, savedHints, waitingHints, savedForest, waitingForest,
    actualPacket, packetKnown, answerSame, frame, saved, waiting, scopeSame, hintsSame, forestSame,
    demandSame, recordsSame, selection, evaluation⟩ :=
    SourceAnnotatedStoredTyping.capture_segments physical runtime
  have packetSame := stored.handlerAt_unique packetKnown storedKnown
  cases packetSame
  have exactSource := frame.handler_source.1
  have instanceSame : handler.effectInst = requested := ScopedTyping.handler_cut_instance physical.erase
  rw [instanceSame] at exactSource
  have clauseModes : SourceTemplates.ClauseModes handler.clauses.erase (tables handler.erase) := by
    cases frame.forget with
    | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes => exact modes
  exact ⟨answer, residual, capture_snapshot_data snapshot snapshotAdmitted physical matched stored storedAdmitted
    packet storedKnown clauseModes exactSource selected found rowAvailable declared request retained fresh absent operationKnown
    actualCut actualSelected captureSource checked supplied⟩

end Ash.OneShot.SourceAnnotatedAllocationData

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.capture_snapshot_from_stored_source
