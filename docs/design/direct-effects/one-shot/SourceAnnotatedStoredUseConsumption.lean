import SourceConsumingUseAlignedConsumption
import SourceAnnotatedStoredResumption
import SourceAnnotatedStoredDisposal

/-! Connect source activation to actual typed consumption. Runtime owner
uniqueness authenticates the snapshot cut; existing consumption proofs supply
the successor and one-shot accounting. -/
namespace Ash.OneShot.ScopedExecution

/-- Recursive live tickets form an ordered sublist of owned tickets; scheduled
retirements may add owners but cannot duplicate the live inventory. -/
theorem recursive_live_tickets_sublist (stack : Stack) :
    stack.erase.liveTickets.Sublist (ownedTickets stack) := by
  induction stack with
  | nil => exact .slnil
  | push frame rest ih =>
      cases frame <;> first | exact ih | exact List.Sublist.cons _ ih
  | live owner input answer saved caller rest ihSaved ihRest =>
      exact List.Sublist.cons_cons owner (ihSaved.append ihRest)
  | spent owner answer caller rest ih => exact ih

end Ash.OneShot.ScopedExecution

namespace Ash.OneShot.SourceAnnotatedRuntimeState
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Retained DeclarationPolicy DeclarationLaws)
open SourceConsumingCleanupAdmission (Context UseAlignedBody)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceBoundSnapshots.Retained (ofCapability)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- The existing frame realization identifies source owners with actual live
tickets. Their uniqueness follows from the runtime inventory, not a new input. -/
theorem AtPlan.source_owners_unique {hints : Hints receiving} {forest : Forest hints}
    (state : AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope code stack plan forest output demand row evidence) :
    (SourceDependencyOwners.owners receiving).Nodup := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      rw [SourceDependencyOwners.realized_owners pending.erase.source.source.matches.realizes]
      exact (recursive_live_tickets_sublist stack.erase).nodup unique

variable [nested : DeclarationPolicy]
  {front capture tail : SourceAnnotatedRuntime.Stack}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {sourceFrontHints : Hints sourceFrontScope} {sourceFront : Forest sourceFrontHints}
  {sourceWholeHints : Hints sourceWholeScope} {sourceWhole : Forest sourceWholeHints}

/-- The consuming source constructs the entire pending source at the exact
typed successor. Phase equality comes from the existing one-shot trace. -/
theorem AtPackets.resume_use_snapshot
    (laws : DeclarationLaws nested admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → nested.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (original : Context world owner outward actions
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)).erase))
      base baseFront saved waiting)
    (cut : OwnerCut owner sourceWhole sourceFront saved waiting)
    (before : Interfaces world sourceFront)
    {bounds : SourcePlanBounds.Annotation world (.invoke (key := ⟨owner, .resume⟩))}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds snapshot.pending)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.resume hint binder value) (front.append (.live owner inputType answerType capture caller tail))
      snapshot.plan snapshot.forest output demand row stored evidence)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value.erase) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
      AtPackets operations policy contracts tables families required actions annotations world outward outside
        scope value (capture.append (front.append (.spent owner answerType caller tail)))
        nextSnapshot.plan nextSnapshot.forest output remaining row stored.resume evidence ∧
      demand = owner :: remaining ∧ SourceBoundSnapshots.Resumed owner snapshot nextSnapshot ∧
      ∃ source : Retained world nextSnapshot.forest .nil,
        source.Valid outward actions
          (OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))).erase)) ∧
        ofCapability source = nextSnapshot.pending ∧
      ∃ records : nextSnapshot.pending.Records (SourceBoundSnapshots.CodeRecord outward actions (OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))).erase))),
        SourceBoundSnapshots.Retained.Records.AtReceivers outward actions (OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))).erase)) records .nil := by
  obtain ⟨remaining, nextSnapshot, next, accounting, trace, moved⟩ :=
    SourceAnnotatedStoredResumption.resume_cut_preserves_snapshot snapshot state resolved closed
  obtain ⟨source, ready, kept, covered⟩ := record.resumed laws project
    state.atPlan.source_owners_unique moved
  have actualPhases := OwnerPhaseTransitions.trace_result trace
  refine ⟨remaining, nextSnapshot, next, accounting, moved, source, ?_⟩
  have phasesSame : (OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))).erase)) = OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)).erase)) owner := by
    simpa only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase,
      OwnerPhaseTransitions.spendAll] using actualPhases
  rw [phasesSame]
  exact ⟨ready, kept, covered⟩

/-- The consuming source constructs the entire pending source at the exact
typed successor. Phase equality comes from the existing one-shot trace. -/
theorem AtPackets.discard_use_snapshot
    (laws : DeclarationLaws nested admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → nested.accepts required plans)
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (original : Context world owner outward actions
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)).erase))
      base baseFront saved waiting)
    (cut : OwnerCut owner sourceWhole sourceFront saved waiting)
    (before : Interfaces world sourceFront)
    {bounds : SourcePlanBounds.Annotation world (.invoke (key := ⟨owner, .dispose⟩))}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds snapshot.pending)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.discard hint binder) (front.append (.live owner inputType answerType capture caller tail))
      snapshot.plan snapshot.forest output demand row stored evidence)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (built : makePlan capture.erase = some plan)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world contract.closeEffects plan) :
    ∃ restored : SourceAnnotatedRuntime.Stack,
    ∃ restoredStored : SourceConsumingStoredBounds.StackBounds families restored,
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
      restored.erase = (closeControl scope plan).append
        (.push (.closing closeId scope) (front.erase.append (.spent owner answerType caller tail.erase))) ∧
      RawStep ⟨.discard binder, scope, front.erase.append (.live owner inputType answerType capture.erase caller tail.erase)⟩
        ⟨.unit, scope, restored.erase⟩ [.close closeId] [.ticket owner] ∧
      AtPackets operations policy contracts tables families required actions annotations world outward outside
        scope (.unit .unit) restored nextSnapshot.plan nextSnapshot.forest output remaining row restoredStored evidence ∧
      demand = owner :: remaining ∧
      (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase))).Perm
        (owner :: ownedTickets restored.erase) ∧
      (∃ annotated, SourceAnnotatedRuntime.makePlan capture = some annotated ∧
        restored = (SourceAnnotatedRuntime.closeControl scope annotated).append
          (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))) ∧
        HEq restoredStored (stored.discard scope closeId annotated)) ∧
      SourceBoundSnapshots.Discarded owner snapshot nextSnapshot ∧
      ∃ source : Retained world nextSnapshot.forest .nil,
        source.Valid outward actions (OwnerPhaseTransitions.available (ownedTickets restored.erase)) ∧
        ofCapability source = nextSnapshot.pending ∧
      ∃ records : nextSnapshot.pending.Records (SourceBoundSnapshots.CodeRecord outward actions (OwnerPhaseTransitions.available (ownedTickets restored.erase))),
        SourceBoundSnapshots.Retained.Records.AtReceivers outward actions (OwnerPhaseTransitions.available (ownedTickets restored.erase)) records .nil := by
  obtain ⟨restored, restoredStored, remaining, nextSnapshot, erased, raw, next, accounting,
    owners, trace, actualPlan, moved⟩ :=
    SourceAnnotatedStoredDisposal.discard_cut_preserves_snapshot snapshot state known resolved built typed
  obtain ⟨source, ready, kept, covered⟩ := record.discarded laws project
    state.atPlan.source_owners_unique moved
  have actualPhases := OwnerPhaseTransitions.trace_result trace
  refine ⟨restored, restoredStored, remaining, nextSnapshot, erased, raw, next, accounting,
    owners, actualPlan, moved, source, ?_⟩
  have phasesSame : (OwnerPhaseTransitions.available (ownedTickets restored.erase)) = OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)).erase)) owner := by
    simpa only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase,
      OwnerPhaseTransitions.spendAll] using actualPhases
  rw [phasesSame]
  exact ⟨ready, kept, covered⟩

end Ash.OneShot.SourceAnnotatedRuntimeState

#print axioms Ash.OneShot.ScopedExecution.recursive_live_tickets_sublist
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPlan.source_owners_unique
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.resume_use_snapshot

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.discard_use_snapshot
