import SourceConsumingUseTransitions
import SourceScheduledSourceJoin

/-! Activate the saved or closing source at a consuming leaf. The original
AtUse derivation supplies structural receiver rechecking; the finite clause
check supplies permission and caller checks. Recomposition keeps every bound
in ordinary code, callbacks and dormant branches. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceBoundSnapshots.Retained (ofCapability)

variable [DeclarationPolicy]

/-- Reuse the established empty-suffix and append equalities to close a source
forest. No new source traversal or successor-validity premise is required. -/
theorem retained_join_closed
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (inside : Retained world first second) (tail : Retained world second .nil)
    (ready : inside.Valid outward actions phases) (tailReady : tail.Valid outward actions phases) :
    ∃ annotation : Retained world (first.append second) .nil,
      annotation.Valid outward actions phases ∧
      ofCapability annotation = (ofCapability inside).append (ofCapability tail) := by
  obtain ⟨source, valid, kept⟩ :=
    (SourceScheduledRecomposition.predicate_congr
      (SourceDependencyProjection.scope_append_nil secondScope)
      (SourcePlannedRecomposition.hints_append_nil secondHints)
      (SourceScheduledRecomposition.forest_append_nil second)
      (fun outside => ∃ source : Retained world first outside,
        source.Valid outward actions phases ∧ ofCapability source = ofCapability inside)).mpr ⟨inside, ready, rfl⟩
  obtain ⟨joined, joinedReady, bounds⟩ := retained_append_retaining source tail valid tailReady
  exact ⟨joined, joinedReady, bounds.trans (congrArg (fun first => first.append (ofCapability tail)) kept)⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledCapabilityAnnotations (Retained DeclarationPolicy DeclarationLaws retained_join_closed)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledNeutral (OwnerCut)
open SourceBoundSnapshots.Retained (ofCapability)
open OwnerPhaseTransitions (spend)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {original : Context world owner outward actions phases base baseFront saved waiting}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {cut : OwnerCut owner whole front saved waiting} {before : Interfaces world front}

/-- Saved source is rechecked at the leaf's accumulated caller, then joined
with that caller and the waiting tail. Original resumption bounds remain exact. -/
theorem UseQueuedBody.resume_source
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {bounds : SourcePlanBounds.Annotation world (.invoke (key := ⟨owner, .resume⟩))}
    (record : UseQueuedBody resumeRequired closeRequired original cut before bounds) :
    ∃ permission : (actions owner).any (fun rights => rights.resume) = true,
    ∃ source : Retained world (saved.append (front.append (.spent (owner := owner) waiting))) .nil,
      source.Valid outward actions (spend phases owner) ∧
      ofCapability source = (original.continuationBounds.resumption permission).append
        ((SourceBoundSnapshots.Retained.absent front).append (.spent (owner := owner) (ofCapability original.after))) := by
  rcases record with ⟨body, _origin, admitted, _nested, checked⟩
  cases body with
  | resume =>
    cases admitted with
    | resume recheck =>
      obtain ⟨inside, insideReady, insideBounds⟩ :=
        (recheck checked.1).compile_retaining laws project (original.resumption checked.1).property
      obtain ⟨caller, callerReady, callerBounds⟩ := retained_join_closed
        (Retained.operations before) (Retained.spent (owner := owner) original.after)
        checked.2.2.2 original.tailReady
      obtain ⟨source, ready, bounds⟩ := retained_join_closed inside caller insideReady callerReady
      refine ⟨checked.1, source, ready, ?_⟩
      rw [bounds, insideBounds, callerBounds]
      rfl

/-- Closing source is rechecked under the running boundary at the consuming
leaf. Its callback and dormant-branch bounds survive the same recomposition. -/
theorem UseQueuedBody.dispose_source
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {bounds : SourcePlanBounds.Annotation world (.invoke (key := ⟨owner, .dispose⟩))}
    (record : UseQueuedBody resumeRequired closeRequired original cut before bounds) :
    ∃ permission : (actions owner).any (fun rights => rights.dispose) = true,
    ∃ source : Retained world
      (saved.forClosing.append (.running (front.append (.spent (owner := owner) waiting)))) .nil,
      source.Valid outward actions (spend phases owner) ∧
      ofCapability source = (original.continuationBounds.closing permission).append
        (.running ((SourceBoundSnapshots.Retained.absent front).append
          (.spent (owner := owner) (ofCapability original.after)))) := by
  rcases record with ⟨body, _origin, admitted, _nested, checked⟩
  cases body with
  | dispose =>
    cases admitted with
    | dispose recheck =>
      obtain ⟨inside, insideReady, insideBounds⟩ :=
        (recheck checked.1).compile_retaining laws project (original.closing checked.1).property
      obtain ⟨caller, callerReady, callerBounds⟩ := retained_join_closed
        (Retained.operations before) (Retained.spent (owner := owner) original.after)
        checked.2.2.2 original.tailReady
      obtain ⟨source, ready, bounds⟩ := retained_join_closed inside (Retained.running caller) insideReady callerReady
      refine ⟨checked.1, source, ready, ?_⟩
      rw [bounds, insideBounds]
      change (ofCapability (original.closing checked.1).val).append (.running (ofCapability caller)) = _
      rw [callerBounds]
      rfl

variable [SourceScheduledChecks.DeclarationProjection admission certification]
  {targetHints : Hints targetScope} {target : Forest targetHints}

/-- Split the actual neutral receiver at the same live owner. Restore source
at that receiver, retaining the precise neutral movement of all original bounds. -/
theorem UseReceiverBody.resume_source
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {bounds : SourcePlanBounds.Annotation world (.invoke (key := ⟨owner, .resume⟩))}
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds) :
    ∃ permission : (actions owner).any (fun rights => rights.resume) = true,
    ∃ nextFrontScope nextWaitingScope, ∃ nextFrontHints : Hints nextFrontScope,
    ∃ nextWaitingHints : Hints nextWaitingScope, ∃ nextFront : Forest nextFrontHints,
    ∃ nextWaiting : Forest nextWaitingHints,
      OwnerCut owner target nextFront saved nextWaiting ∧
      ∃ source : Retained world (saved.append (nextFront.append (.spent (owner := owner) nextWaiting))) .nil,
        source.Valid outward actions (spend phases owner) ∧
        SourceBoundSnapshots.Retained.Neutral world
          ((original.continuationBounds.resumption permission).append
            ((SourceBoundSnapshots.Retained.absent front).append (.spent (owner := owner) (ofCapability original.after))))
          (ofCapability source) := by
  obtain ⟨permission, originalSource, ready, kept⟩ := record.source.resume_source laws project
  obtain ⟨_, _, _, _, nextFront, nextWaiting, nextCut, changedFront, changedWaiting⟩ :=
    SourceScheduledNeutral.expand_owner record.receiver cut
  obtain ⟨source, valid, moved⟩ := Retained.expand_neutral laws project
    (SourceScheduledNeutral.Expansion.prefix saved (changedFront.append (.spent changedWaiting)))
    SourceScheduledNeutral.Expansion.refl originalSource ready
  exact ⟨permission, _, _, _, _, nextFront, nextWaiting, nextCut, source, valid, kept ▸ moved⟩

/-- The same receiver split activates closing source under its running marker.
The saved forest's canonical closing order is unchanged; only neutral frames
are inserted into the actual caller and waiting tail. -/
theorem UseReceiverBody.dispose_source
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {bounds : SourcePlanBounds.Annotation world (.invoke (key := ⟨owner, .dispose⟩))}
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds) :
    ∃ permission : (actions owner).any (fun rights => rights.dispose) = true,
    ∃ nextFrontScope nextWaitingScope, ∃ nextFrontHints : Hints nextFrontScope,
    ∃ nextWaitingHints : Hints nextWaitingScope, ∃ nextFront : Forest nextFrontHints,
    ∃ nextWaiting : Forest nextWaitingHints,
      OwnerCut owner target nextFront saved nextWaiting ∧
      ∃ source : Retained world
        (saved.forClosing.append (.running (nextFront.append (.spent (owner := owner) nextWaiting)))) .nil,
        source.Valid outward actions (spend phases owner) ∧
        SourceBoundSnapshots.Retained.Neutral world
          ((original.continuationBounds.closing permission).append
            (.running ((SourceBoundSnapshots.Retained.absent front).append
              (.spent (owner := owner) (ofCapability original.after)))))
          (ofCapability source) := by
  obtain ⟨permission, originalSource, ready, kept⟩ := record.source.dispose_source laws project
  obtain ⟨_, _, _, _, nextFront, nextWaiting, nextCut, changedFront, changedWaiting⟩ :=
    SourceScheduledNeutral.expand_owner record.receiver cut
  obtain ⟨source, valid, moved⟩ := Retained.expand_neutral laws project
    (SourceScheduledNeutral.Expansion.prefix saved.forClosing (.running (changedFront.append (.spent changedWaiting))))
    SourceScheduledNeutral.Expansion.refl originalSource ready
  exact ⟨permission, _, _, _, _, nextFront, nextWaiting, nextCut, source, valid, kept ▸ moved⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_join_closed
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.resume_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.dispose_source

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.resume_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.dispose_source
