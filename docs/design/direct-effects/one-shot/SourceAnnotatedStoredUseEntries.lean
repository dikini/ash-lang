import SourceConsumingUseAlignedSnapshots
import SourceAnnotatedStoredEntries
import SourceAnnotatedStoredResources

/-! Actual typed cleanup/resource entries carry derived consuming child
records. Each proof reuses the existing runtime step and snapshot theorem;
source descent adds no successor-admission premise. -/
namespace Ash.OneShot.SourceAnnotatedStoredUseEntries
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingCleanupAdmission (Context UseAlignedBody)
open SourceDeclarationPlans (Plan)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)
open SourceScheduledCapabilityAnnotations (Code)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {sourceHints : Hints sourceScope} {frontHints : Hints frontScope}
  {sourceWhole : Forest sourceHints} {front : Forest frontHints}

theorem cleanup_use_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (original : Context world owner outward actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces world front)
    (record : UseAlignedBody resumeRequired closeRequired original cut caller snapshot.current snapshot.pending)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.cleanup hint callback body) stack snapshot.plan snapshot.forest output demand row stored evidence)
    (isValue : callback.erase.IsValue) :
    ∃ answerPort : ScopedPorts.Port, ∃ requests,
    SourceFocusHints.inputPort Instantiation.Environment.empty hint = some answerPort ∧
    SourceFocusHints.inputPort Instantiation.Environment.empty callback.hint = some (.function .unit .unit requests) ∧
    ∀ identity answerType, ScopedPorts.eraseType answerType = answerPort →
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
      action.identity = identity ∧ action.answer = answerType ∧ action.requests = requests ∧
      action.action = callback ∧ action.scope = scope ∧
      RawStep ⟨.cleanup callback.erase body.erase, scope, stack.erase⟩ ⟨body.erase, scope, .push (.armed action.erase) stack.erase⟩ [.cleanup identity] [] ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        scope body (.push (.armed action) stack) nextSnapshot.plan nextSnapshot.forest output demand row (.push .armed stored) evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot ∧
      ∃ needs callbackDependencies, ∃ callbackPlan : Plan callbackDependencies,
      ∃ callbackRequired, ∃ footprint : RequestFootprint callbackPlan callbackRequired,
      ∃ declared : Declared world (signature callbackPlan),
      ∃ child : UseAlignedBody resumeRequired closeRequired original
        (.cleanup (needs := needs) (plan := callbackPlan) cut)
        (.cleanup front callbackRequired footprint declared caller)
        nextSnapshot.current (.cleanup (needs := needs) (.absent (plan := callbackPlan)) snapshot.pending),
        nextSnapshot = ⟨_, nextSnapshot.plan, child.source.body.boundAnnotation, _, _,
          .cleanup (needs := needs) callbackPlan snapshot.forest, .cleanup .absent snapshot.pending⟩ ∧
        (Code.operations (forest := .running snapshot.forest) callbackRequired footprint declared).Valid
          outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) ∧
        (∀ request ∈ callbackRequired, request.1 ∈ needs) := by
  obtain ⟨answerPort, requests, portKnown, callbackKnown, entered⟩ :=
    SourceAnnotatedStoredEntries.cleanup_annotations_exact_snapshot snapshot state isValue
  refine ⟨answerPort, requests, portKnown, callbackKnown, ?_⟩
  intro identity answerType answerSame
  obtain ⟨action, nextSnapshot, identitySame, typeSame, requestsSame, callbackSame, scopeSame,
    raw, next, installed⟩ := entered identity answerType answerSame
  exact ⟨action, nextSnapshot, identitySame, typeSame, requestsSame, callbackSame, scopeSame,
    raw, next, installed, record.cleanup_entered installed⟩

theorem resource_use_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (original : Context world owner outward actions
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) base baseFront saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner sourceWhole front saved waiting)
    (caller : SourceScheduledRetainedInterfaces.Interfaces world front)
    (record : UseAlignedBody resumeRequired closeRequired original cut caller snapshot.current snapshot.pending)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.resource hint binder initializer body) stack snapshot.plan snapshot.forest output demand row stored evidence)
    (isValue : initializer.erase.IsValue) (freshWorld : identity ∉ world)
    (ports : SourceFocusHints.inputPort Instantiation.Environment.empty hint = some (ScopedPorts.eraseType answer)) :
    ∃ payload, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (world ++ [identity]), ∃ nextRow,
      initializer.erase = .integer payload ∧
      RawStep ⟨.resource binder initializer.erase body.erase, scope, stack.erase⟩
        ⟨body.erase.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack.erase⟩ [.resource identity] [] ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations (world ++ [identity]) outward outside
        scope (body.instantiate (Instantiation.Environment.empty.bind binder identity))
        (.push (.cell identity payload scope answer) stack) nextSnapshot.plan nextSnapshot.forest output demand nextRow (.push .cell stored) evidence ∧
      nextRow.Sublist row ∧ SourceBoundSnapshots.EnteredResource identity snapshot nextSnapshot ∧
      ∃ child : UseAlignedBody resumeRequired closeRequired
        (original.world_weaken (List.subset_append_left _ [identity]))
        (.cell (identity := identity) cut) (.cell (caller.world_weaken (List.subset_append_left _ [identity])))
        nextSnapshot.current (.cell (identity := identity) (snapshot.pending.world_weaken (List.subset_append_left _ [identity]))),
        nextSnapshot = ⟨_, nextSnapshot.plan, child.source.body.boundAnnotation, _, _,
          .cell (identity := identity) snapshot.forest,
          .cell (snapshot.pending.world_weaken (List.subset_append_left _ [identity]))⟩ := by
  obtain ⟨payload, nextSnapshot, nextRow, payloadSame, raw, next, included, installed⟩ :=
    SourceAnnotatedStoredResources.resource_narrowing_snapshot snapshot state isValue freshWorld ports
  exact ⟨payload, nextSnapshot, nextRow, payloadSame, raw, next, included, installed,
    record.resource_entered freshWorld installed⟩

end Ash.OneShot.SourceAnnotatedStoredUseEntries

#print axioms Ash.OneShot.SourceAnnotatedStoredUseEntries.cleanup_use_snapshot
#print axioms Ash.OneShot.SourceAnnotatedStoredUseEntries.resource_use_snapshot
