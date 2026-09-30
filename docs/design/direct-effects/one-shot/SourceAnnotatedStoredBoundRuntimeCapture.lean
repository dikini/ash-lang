import SourceAnnotatedStoredBoundEvidence

/-! Bounded capture generates the clause annotation from one finite source
check and carries it through the actual runtime successor. The existing runtime
capture theorem supplies substitution, recomposition and ownership preservation. -/
namespace Ash.OneShot.SourceAnnotatedStoredRuntimeCapture
open SourceAnnotatedRuntimeState (AtPackets)
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingStoredBounds (StackBounds HandlerBounds)

variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

theorem capture_from_bounds_retaining
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    (stored : StackBounds families whole) (storedAdmitted : stored.Admitted world required)
    (packet : HandlerBounds families handler)
    (packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
    (bounded : packet.admission = .bounded)
    (state : AtPackets operations policy contracts tables families required actions annotations world [] outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole snapshot.plan snapshot.forest output demand row stored)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase.erase (Admission.outsideResources capture.erase.erase))
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (captureSource : SourceConsumingCaptureInput.Source world snapshot.forest saved waiting)
    (sourceCut : SourceScheduledNeutral.Cut requested operation offered modes snapshot.forest saved waiting)
    (checked : captureSource.Check [] actions (OwnerPhaseTransitions.available (ownedTickets whole.erase))
      owner packet.bounds code.erase.requiredActions sourceCut closeOutside) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      (∃ dependencies, ∃ nextPlan : SourceDeclarationPlans.Plan dependencies,
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer handler.scope) ∧
      AtPackets operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack nextPlan
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow nextStored ∧
      SourceBoundSnapshots.GeneratedCapture snapshot owner nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  apply capture_preserves_retaining (SourceBoundSnapshots.GeneratedCapture snapshot owner) state cut isValue selected found
    freshContract freshAction freshAnnotation supported
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    obtain ⟨actualScope, actualTail, actualSaved, actualWaiting, actualCut, inside, outside, supplied⟩ :=
      SourcePlannedRuntimeCuts.matched_cut cut.erase pending.forget.erase.source.source.matches found declared
    cases Option.some.inj (actualCut.lookup.symm.trans sourceCut.erase.lookup)
    have suppliedSource := supplied pending.forget.erase.pending.compatible
    intro actualPacket actualPacketAt recipes actualModes actualDeclared capturedScope tailScope savedHints waitingHints saved waiting plannedCut family bodies chosen
    cases stored.handlerAt_unique actualPacketAt packetAt
    cases Option.some.inj (declared.symm.trans actualDeclared)
    cases storedAdmitted.handlerAt packetAt with
    | bounded route annotations admitted =>
        exact SourceBoundSnapshots.bounded_capture_requirements snapshot snapshotAdmitted admitted captureSource sourceCut checked
          suppliedSource plannedCut chosen
    | inherited route recipes => cases bounded.symm.trans route

end Ash.OneShot.SourceAnnotatedStoredRuntimeCapture

#print axioms Ash.OneShot.SourceAnnotatedStoredRuntimeCapture.capture_from_bounds_retaining
