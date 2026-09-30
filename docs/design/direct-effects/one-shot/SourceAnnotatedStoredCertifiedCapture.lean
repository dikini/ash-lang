import SourceAnnotatedStoredRuntimeCapture
import SourceConsumingCaptureSnapshots

/-! General structural capture certificates share the actual allocator with
independent bound snapshots. The certificate has an exact cut, selected clause
and recursive source data; its validation is explicit. Deriving that validation
from complete initial source admission remains a separate obligation. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Bound data for the actual selected plan and recomposed forest. This stores
no scheduling premise and does not project a capability annotation. -/
def CapturedBounds [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy] (before : Snapshot world) (owner : Nat) : SourceAnnotatedAllocationData.ClauseEvidence :=
  fun plan forest =>
    ∃ current : SourcePlanBounds.Annotation world plan, ∃ pending : Retained world forest,
      Captured owner before ⟨_, plan, current, _, _, forest, pending⟩ ∧
      (⟨_, plan, current, _, _, forest, pending⟩ : Snapshot world).Admitted

/-- Exact cut and clause uniqueness connect a single structural certificate
to the allocator's selected witness. Bound generation is independent. -/
theorem bounds_for_certified_capture
    [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification outward)
    (snapshot : Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : SourceConsumingClauseAnnotations.Declarations world plans}
    {bounds : SourceConsumingClauseAnnotations.ClauseBounds plans}
    (bounded : SourceConsumingClauseAnnotations.Bounded bounds annotations required)
    (certificate : SourceScheduledCaptureAnnotations.Capture world owner requested operation offered modes
      plans parameter binder code snapshot.forest)
    (checked : certificate.Valid outward actions phases)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut requested operation offered modes snapshot.forest saved waiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies) :
    SourceScheduledRequirements.Satisfied outward (actions.insert owner code.requiredActions)
      (OwnerPhaseTransitions.introduce phases owner) world (bodies owner) (.live (owner := owner) saved waiting) ∧
      CapturedBounds snapshot owner (bodies owner) (.live (owner := owner) saved waiting) :=
  ⟨certificate.requirements_with laws checked cut selected, bounded.capture_snapshot snapshot snapshotAdmitted cut selected⟩

end Ash.OneShot.SourceBoundSnapshots

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

/-- The existing allocator derives the exact successor, source/packet typing,
ownership balance and row inclusion. Neither a chain-shaped captured source nor
a supplied successor invariant is required. Certificate validation is explicit. -/
theorem capture_from_certificate_retaining
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
    (certificate : SourceScheduledCaptureAnnotations.Capture world owner requested operation offered modes
      packet.plans parameter binder code.erase snapshot.forest)
    (checked : certificate.Valid [] actions (OwnerPhaseTransitions.available (ownedTickets whole.erase))) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      (∃ dependencies, ∃ nextPlan : SourceDeclarationPlans.Plan dependencies,
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer handler.scope) ∧
      AtPackets operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack nextPlan
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow nextStored evidence ∧
      SourceBoundSnapshots.CapturedBounds snapshot owner nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  apply capture_preserves_retaining (SourceBoundSnapshots.CapturedBounds snapshot owner) state cut isValue selected found
    freshContract freshAction freshAnnotation supported
  intro actualPacket actualPacketAt recipes actualModes actualDeclared capturedScope tailScope savedHints waitingHints saved waiting plannedCut family bodies chosen
  cases stored.handlerAt_unique actualPacketAt packetAt
  cases Option.some.inj (declared.symm.trans actualDeclared)
  cases storedAdmitted.handlerAt packetAt with
  | bounded route annotations admitted =>
      exact SourceBoundSnapshots.bounds_for_certified_capture laws snapshot snapshotAdmitted admitted certificate checked plannedCut chosen
  | inherited route recipes => cases bounded.symm.trans route

/-- Bound admission and the exact physical packet movement accompany the same
actual source successor; no bound field is recovered from reconstructed code. -/
theorem capture_from_certificate_snapshot
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
    (certificate : SourceScheduledCaptureAnnotations.Capture world owner requested operation offered modes
      packet.plans parameter binder code.erase snapshot.forest)
    (checked : certificate.Valid [] actions (OwnerPhaseTransitions.available (ownedTickets whole.erase))) :
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
  obtain ⟨contract, captured, waiting, after, nextDemand, nextRow,
    step, ⟨dependencies, nextPlan, nextStored, packetsSame, next, capturedBounds⟩,
    balance, included, owners, shape, sourceInput⟩ :=
    capture_from_certificate_retaining laws snapshot snapshotAdmitted stored storedAdmitted packet packetAt bounded
      state cut isValue selected found freshContract freshAction freshAnnotation supported declared certificate checked
  obtain ⟨current, pending, moved, admitted⟩ := capturedBounds
  let nextSnapshot : SourceBoundSnapshots.Snapshot world :=
    ⟨_, nextPlan, current, _, _, .live (owner := owner) captured.forest waiting.forest, pending⟩
  have packets : nextStored.Admitted world required := by
    cases shape
    cases eq_of_heq packetsSame
    exact storedAdmitted.capture cut
  exact ⟨contract, captured, waiting, after, nextDemand, nextRow, nextSnapshot, nextStored,
    step, next, balance, included, owners, moved, admitted, packets, HEq.rfl, packetsSame, shape, sourceInput⟩

end Ash.OneShot.SourceAnnotatedStoredRuntimeCapture

#print axioms Ash.OneShot.SourceBoundSnapshots.bounds_for_certified_capture
#print axioms Ash.OneShot.SourceAnnotatedStoredRuntimeCapture.capture_from_certificate_retaining

#print axioms Ash.OneShot.SourceAnnotatedStoredRuntimeCapture.capture_from_certificate_snapshot
