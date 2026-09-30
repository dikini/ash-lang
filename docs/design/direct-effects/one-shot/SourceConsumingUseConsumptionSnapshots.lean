import SourceConsumingUseConsumption
import SourceBoundConsumptionSelection

/-! The consuming source record activates at the exact runtime bound snapshot.
Original metadata equality is independent of source validity. The actual
resumption/disposal relation and owner uniqueness identify its source cut. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (ClausePlans)
open SourceScheduledCapabilityAnnotations (Retained DeclarationPolicy DeclarationLaws)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledNeutral (OwnerCut)
open SourceBoundSnapshots (Snapshot Resumed Discarded)
open SourceBoundSnapshots.Retained (ofCapability)
open OwnerPhaseTransitions (spend)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {original : Context world owner outward actions phases base baseFront saved waiting}
  {frontHints : Hints frontScope} {front : Forest frontHints}
  {before : Interfaces world front}

/-- All restored source positions, including callbacks and dormant captures,
are derived from the consuming record. No successor source validity is assumed. -/
theorem UseQueuedBody.resumed
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {snapshot next : Snapshot world}
    (cut : OwnerCut owner snapshot.forest front saved waiting)
    {bounds : SourcePlanBounds.Annotation world (.invoke (key := ⟨owner, .resume⟩))}
    (record : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    (captured : SourceBoundSnapshots.Retained world saved)
    (savedOrigin : ∀ permission, original.continuationBounds.resumption permission = captured)
    (aligned : HEq snapshot.pending ((SourceBoundSnapshots.Retained.absent front).append
      (.live (owner := owner) captured (ofCapability original.after))))
    (unique : (SourceDependencyOwners.owners snapshot.scope).Nodup)
    (step : Resumed owner snapshot next) :
    ∃ source : Retained world next.forest .nil,
      source.Valid outward actions (spend phases owner) ∧ ofCapability source = next.pending := by
  obtain ⟨permission, source, ready, kept⟩ := record.resume_source laws project
  have same := step.at_cut unique cut (.absent front) captured (ofCapability original.after) aligned
  cases same
  exact ⟨source, ready, kept.trans (congrArg (fun saved => saved.append
    ((SourceBoundSnapshots.Retained.absent front).append (.spent (owner := owner) (ofCapability original.after))))
    (savedOrigin permission))⟩

/-- Closing source is tied to the original saved snapshot's canonical closing
projection. Actual disposal therefore activates exactly the retained callback
bounds, including those inside dormant captured branches. -/
theorem UseQueuedBody.discarded
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {snapshot next : Snapshot world}
    (cut : OwnerCut owner snapshot.forest front saved waiting)
    {bounds : SourcePlanBounds.Annotation world (.invoke (key := ⟨owner, .dispose⟩))}
    (record : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    (captured : SourceBoundSnapshots.Retained world saved)
    (closingOrigin : ∀ permission, original.continuationBounds.closing permission = captured.forClosing)
    (aligned : HEq snapshot.pending ((SourceBoundSnapshots.Retained.absent front).append
      (.live (owner := owner) captured (ofCapability original.after))))
    (unique : (SourceDependencyOwners.owners snapshot.scope).Nodup)
    (step : Discarded owner snapshot next) :
    ∃ source : Retained world next.forest .nil,
      source.Valid outward actions (spend phases owner) ∧ ofCapability source = next.pending := by
  obtain ⟨permission, source, ready, kept⟩ := record.dispose_source laws project
  have same := step.at_cut unique cut (.absent front) captured (ofCapability original.after) aligned
  cases same
  exact ⟨source, ready, kept.trans (congrArg (fun closing => closing.append
    (.running ((SourceBoundSnapshots.Retained.absent front).append
      (.spent (owner := owner) (ofCapability original.after))))) (closingOrigin permission))⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.resumed
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.discarded
