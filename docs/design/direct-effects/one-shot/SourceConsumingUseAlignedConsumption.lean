import SourceConsumingUseAligned
import SourceConsumingUseConsumption
import SourceScheduledNeutralActual
import SourceBoundNeutralConsumption
import SourceCodeRecords

/-! Consume a source record at its actual neutral receiver. The record's
metadata relation identifies the runtime destination, and existing structural
source compilation supplies validity there. -/
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

/-- Authenticate the canonical source decomposition using the existing cut
reconstruction equations, without another owner-search induction. -/
theorem canonical_use_cut
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : OwnerCut owner whole front saved waiting) :
    OwnerCut owner (front.append (.live (owner := owner) saved waiting)) front saved waiting :=
  (SourceScheduledRecomposition.predicate_congr
    (SourceContextualInvocationHints.selected_cut cut.found).reconstruct cut.hints cut.forest
    (fun forest => OwnerCut owner forest front saved waiting)).mp cut

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {original : Context world owner outward actions phases base baseFront saved waiting}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {cut : OwnerCut owner whole front saved waiting} {before : Interfaces world front}

/-- Original source compiles at the consuming leaf's caller. Metadata movement
then transports that valid source to the exact runtime successor bounds. -/
theorem UseAlignedBody.resumed
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {snapshot next : Snapshot world}
    {bounds : SourcePlanBounds.Annotation world (.invoke (key := ⟨owner, .resume⟩))}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds snapshot.pending)
    (unique : (SourceDependencyOwners.owners snapshot.scope).Nodup)
    (step : Resumed owner snapshot next) :
    ∃ source : Retained world next.forest .nil,
      source.Valid outward actions (spend phases owner) ∧ ofCapability source = next.pending ∧
      ∃ records : next.pending.Records (SourceBoundSnapshots.CodeRecord outward actions (spend phases owner)),
        SourceBoundSnapshots.Retained.Records.AtReceivers outward actions (spend phases owner) records .nil := by
  obtain ⟨permission, source, ready, kept⟩ := record.source.resume_source laws project
  have movement := record.metadata.movement.resumed (canonical_use_cut cut)
    (.absent front) record.metadata.captured (ofCapability original.after) unique step
  have origin := kept.trans (congrArg (fun captured => captured.append
    ((SourceBoundSnapshots.Retained.absent front).append (.spent (owner := owner) (ofCapability original.after))))
    (record.metadata.resumption permission))
  obtain ⟨target, targetReady, targetOrigin⟩ := Retained.expand_neutral_at laws project movement .refl source ready origin
  exact ⟨target, targetReady, targetOrigin, target.code_records_at targetReady targetOrigin⟩

/-- Closing uses the original captured metadata's canonical closing, including
callbacks inside dormant captures. Changed caller and waiting frames are kept
beneath the running completion boundary of the actual disposal successor. -/
theorem UseAlignedBody.discarded
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {snapshot next : Snapshot world}
    {bounds : SourcePlanBounds.Annotation world (.invoke (key := ⟨owner, .dispose⟩))}
    (record : UseAlignedBody resumeRequired closeRequired original cut before bounds snapshot.pending)
    (unique : (SourceDependencyOwners.owners snapshot.scope).Nodup)
    (step : Discarded owner snapshot next) :
    ∃ source : Retained world next.forest .nil,
      source.Valid outward actions (spend phases owner) ∧ ofCapability source = next.pending ∧
      ∃ records : next.pending.Records (SourceBoundSnapshots.CodeRecord outward actions (spend phases owner)),
        SourceBoundSnapshots.Retained.Records.AtReceivers outward actions (spend phases owner) records .nil := by
  obtain ⟨permission, source, ready, kept⟩ := record.source.dispose_source laws project
  have movement := record.metadata.movement.discarded (canonical_use_cut cut)
    (.absent front) record.metadata.captured (ofCapability original.after) unique step
  have origin := kept.trans (congrArg (fun closing => closing.append
    (.running ((SourceBoundSnapshots.Retained.absent front).append
      (.spent (owner := owner) (ofCapability original.after))))) (record.metadata.closing permission))
  obtain ⟨target, targetReady, targetOrigin⟩ := Retained.expand_neutral_at laws project movement .refl source ready origin
  exact ⟨target, targetReady, targetOrigin, target.code_records_at targetReady targetOrigin⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.canonical_use_cut
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.resumed
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAlignedBody.discarded
