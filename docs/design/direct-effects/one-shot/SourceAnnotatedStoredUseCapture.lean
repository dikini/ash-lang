import SourceConsumingUseAlignedSnapshots
import SourceAnnotatedStoredRuntimeCapture
import SourceCodeRecordCapture

/-! Carry the selected consuming source record through the existing generic
capture allocator. The payload stores concrete source/bound data and the exact
capture/disposal relations; it is not a new admissibility condition. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingCleanupAdmission (Context UseAlignedBody)

variable [SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- Source and pending bounds belong to the same actual successor snapshot.
The original resumption and closing metadata remain explicit in this payload. -/
def CapturedUseBounds (before : Snapshot world)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (context : Context world owner outward actions phases base baseFront saved waiting)
    (resumeRequired closeRequired : List SourceContextualHints.Requirement) :
    SourceAnnotatedAllocationData.ClauseEvidence := fun plan forest =>
  ∃ current : SourcePlanBounds.Annotation world plan, ∃ pending : Retained world forest,
  ∃ cut : SourceScheduledNeutral.OwnerCut owner forest Forest.nil saved waiting,
  ∃ _record : UseAlignedBody resumeRequired closeRequired context cut
    SourceScheduledRetainedInterfaces.Interfaces.nil current pending,
    let captured : Snapshot world := ⟨_, plan, current, _, _, forest, pending⟩
    Captured owner before captured ∧ captured.Admitted ∧
    (∃ records : pending.Records (CodeRecord outward actions phases),
      Retained.Records.AtReceivers outward actions phases records .nil) ∧
    ∃ savedBounds : Retained world saved,
      HEq pending (Retained.live (owner := owner) savedBounds
        (Retained.ofCapability context.after)) ∧
      (∀ permission, context.continuationBounds.resumption permission = savedBounds) ∧
      ∀ permission,
        let closed := Snapshot.value ((Retained.ofCapability (context.closing permission).val).append
          (.running (.spent (owner := owner) (Retained.ofCapability context.after))))
        Discarded owner captured closed ∧ closed.Admitted

end Ash.OneShot.SourceBoundSnapshots

namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body Declarations ClauseBounds Bounded SelectedSource)
open SourceScheduledCapabilityAnnotations (Code Retained CaptureSource DeclarationPolicy DeclarationLaws)
open SourceDependencyOwners (owners)
open SourcePlannedRecipeDeclarations (Selected)
open OwnerPhaseTransitions (introduce)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

theorem SelectedSource.capture_use_payload
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    {plans : ClausePlans clauses families} {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (bounded : Bounded bounds annotations required)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes snapshot.forest saved waiting)
    (selected : Selected operation savedScope.held plans parameter binder code bodies)
    {body : Body world owner (bodies owner)}
    (selectedSource : SelectedSource owner annotations selected body)
    (source : Retained world snapshot.forest .nil)
    (captureSource : CaptureSource outward actions phases cut source code.requiredActions)
    (permits : code.requiredActions.dispose = true → offered.dispose = true)
    (supplied : checkRequirements waitingScope required = true)
    (fresh : actions owner = none) (absent : owner ∉ owners snapshot.scope)
    (atUse : AtUse outward (actions.insert owner code.requiredActions) (introduce phases owner)
      (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent) body .nil)
    (aligned : SourceBoundSnapshots.Retained.ofCapability source = snapshot.pending) :
    let context := Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent
    ∃ contract : SourceConsumingClauseAnnotations.Bounds,
      bounds.lookup operation savedScope.held = some contract ∧
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.requiredActions)
        (introduce phases owner) world (bodies owner) (.live (owner := owner) saved waiting) ∧
      SourceBoundSnapshots.CapturedUseBounds snapshot context contract.resume contract.close
        (bodies owner) (.live (owner := owner) saved waiting) := by
  obtain ⟨contract, found, annotation, savedBounds, record, _, capturedSame, ready, _, moved, admitted⟩ :=
    SelectedSource.capture_aligned_at_use laws project snapshot snapshotAdmitted bounded cut selected selectedSource
      source captureSource permits supplied fresh absent atUse aligned
  obtain ⟨records, covered⟩ := source.code_records_at captureSource.sourceReady aligned
  obtain ⟨nextRecords, _, nextCovered⟩ := moved.carry_fresh_code_records
    (rights := code.requiredActions) records covered fresh
  refine ⟨contract, found, ?_, _, _, SourceScheduledNeutral.OwnerCut.hit, record, moved, admitted,
    ⟨nextRecords, nextCovered⟩,
    savedBounds, HEq.rfl, (fun permission => (record.metadata.resumption permission).trans capturedSame), ?_⟩
  · exact (SourceScheduledCaptureAnnotations.Capture.site cut selected annotation).requirements_with laws ready cut selected
  · intro permission
    have origin := (record.metadata.closing permission).trans
      (congrArg SourceBoundSnapshots.Retained.forClosing capturedSame)
    have discarded := (Context.of_request laws project cut source code.requiredActions captureSource permits fresh absent).discarded_of_closing savedBounds permission origin (SourcePlanBounds.ofCode annotation)
    exact ⟨discarded, discarded.admitted admitted⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.SelectedSource.capture_use_payload

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

/-- A single structurally checked request supplies the actual allocator's
source payload. Exact cut and selected-clause uniqueness avoid an additional
universal premise over possible successors. The existing allocator supplies
ownership balance and the physical capture step. -/
theorem capture_from_use_source_retaining
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws nested admission certification [])
    (snapshot : SourceBoundSnapshots.Snapshot world) (snapshotAdmitted : snapshot.Admitted)
    (stored : StackBounds families whole)
    (packet : HandlerBounds families handler)
    (packetAt : stored.handlerAt requested = some ⟨handler, packet⟩)
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
    (atUse : SourceConsumingCleanupAdmission.AtUse [] (actions.insert owner code.erase.requiredActions)
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
      (SourceConsumingCleanupAdmission.Context.of_request laws project plannedCut source
        code.erase.requiredActions captureSource permits freshAction absent) body .nil)
    (aligned : SourceBoundSnapshots.Retained.ofCapability source = snapshot.pending) :
    let context := SourceConsumingCleanupAdmission.Context.of_request laws project plannedCut source
      code.erase.requiredActions captureSource permits freshAction absent
    ∃ useContract : SourceConsumingClauseAnnotations.Bounds,
      packet.bounds.lookup operation savedScope.held = some useContract ∧
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      (∃ dependencies, ∃ nextPlan : SourceDeclarationPlans.Plan dependencies,
      ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
      HEq nextStored (stored.capture cut owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer handler.scope) ∧
      AtPackets operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack nextPlan
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow nextStored evidence ∧
      SourceBoundSnapshots.CapturedUseBounds snapshot context useContract.resume useContract.close nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨useContract, contractAt, satisfied, payload⟩ :=
    SourceConsumingCleanupAdmission.SelectedSource.capture_use_payload laws project snapshot snapshotAdmitted
      declarationBounded plannedCut plannedSelected selectedSource source captureSource permits supplied
      freshAction absent atUse aligned
  refine ⟨useContract, contractAt, ?_⟩
  apply capture_preserves_retaining
    (SourceBoundSnapshots.CapturedUseBounds snapshot
      (SourceConsumingCleanupAdmission.Context.of_request laws project plannedCut source
        code.erase.requiredActions captureSource permits freshAction absent) useContract.resume useContract.close)
    state cut isValue selected found freshContract freshAction freshAnnotation supported
  intro actualPacket actualPacketAt _recipes actualModes actualDeclared capturedScope tailScope
    savedHints waitingHints actualSaved actualWaiting actualCut family actualBodies actualSelected
  cases stored.handlerAt_unique actualPacketAt packetAt
  cases Option.some.inj (declared.symm.trans actualDeclared)
  cases Option.some.inj (plannedCut.erase.lookup.symm.trans actualCut.erase.lookup)
  obtain ⟨rfl, rfl⟩ := plannedCut.erase.unique actualCut.erase.hints
  obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (plannedCut.forest.symm.trans actualCut.forest))
  obtain ⟨rfl, same⟩ := SourceScheduledClauseHandlers.selected_unique plannedSelected actualSelected
  cases same
  exact ⟨satisfied, payload⟩

end Ash.OneShot.SourceAnnotatedStoredRuntimeCapture

#print axioms Ash.OneShot.SourceAnnotatedStoredRuntimeCapture.capture_from_use_source_retaining
