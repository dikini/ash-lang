import SourceScheduledCaptureSource
import SourceScheduledClosingTransport

/-! The strengthened pre-capture source evidence survives the existing
permission, phase and world transports. All saved pieces and closing
annotations retain their original-request checks and canonical metadata. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyOwners (owners)
open SourceScheduledPhaseRestriction (AvailableOn)
open SourceBoundSnapshots.Retained (ofCapability)

variable [DeclarationPolicy]
  {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
  {cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting}
  {source : Retained world whole .nil}

/-- Reuse validity transport for the original normal and closing annotations.
The actual cut derives the availability facts for both saved and waiting pieces. -/
def CaptureSource.transport (captured : CaptureSource outward actions phases cut source rights)
    (permissions : Syntax.UsageExtension actions nextActions)
    (extension : AvailableOn (owners wholeScope) phases nextPhases) :
    CaptureSource outward nextActions nextPhases cut source rights := by
  have insideExtension : AvailableOn (owners (savedScope.append waitingScope)) phases nextPhases :=
    by simpa only [← cut.erase.reconstruct_scope] using extension
  have tailExtension : AvailableOn (owners (waitingScope.append .nil)) phases nextPhases := by
    apply insideExtension.weaken
    simp only [SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil]
    exact List.subset_append_right _ _
  exact {
    sourceReady := source.valid_transport captured.sourceReady permissions
      (by simpa only [SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil] using extension)
    guarded := captured.guarded
    inside := captured.inside
    after := captured.after
    insideReady := captured.inside.valid_transport captured.insideReady permissions insideExtension
    tailReady := captured.after.valid_transport captured.tailReady permissions tailExtension
    original := captured.original
    closing := by
      intro permission
      obtain ⟨annotation, ready, kept⟩ := captured.closing permission
      refine ⟨annotation, annotation.valid_transport ready permissions ?_, kept⟩
      apply insideExtension.weaken
      simp only [SourceScheduledPhaseRestriction.owners_append, owners]
      exact ScopedExpressions.append_subset (SourceScheduledPhaseRestriction.owners_closing savedScope)
        (List.Subset.refl _) }

omit [DeclarationPolicy] in
private theorem world_metadata_heq
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints)
    (sameForest : HEq first second)
    {left : SourceBoundSnapshots.Retained world first} {right : SourceBoundSnapshots.Retained world second}
    (same : HEq left right) (larger : world ⊆ next) :
    HEq (left.world_weaken larger) (right.world_weaken larger) := by
  cases sameScope
  cases sameHints
  cases sameForest
  cases same
  rfl

/-- World extension maps the original split and its canonical closing proof.
The existing projection and append laws retain the exact source-origin equation. -/
def CaptureSource.world_weaken (captured : CaptureSource outward actions phases cut source rights)
    (larger : world ⊆ next) :
    CaptureSource outward actions phases cut (source.world_weaken larger) rights where
  sourceReady := source.world_weaken_valid larger captured.sourceReady
  guarded := captured.guarded
  inside := captured.inside.world_weaken larger
  after := captured.after.world_weaken larger
  insideReady := captured.inside.world_weaken_valid larger captured.insideReady
  tailReady := captured.after.world_weaken_valid larger captured.tailReady
  original := by
    rw [Retained.ofCapability_world_weaken, Retained.ofCapability_world_weaken,
      Retained.ofCapability_world_weaken, ← SourceBoundSnapshots.Retained.world_weaken_append]
    exact world_metadata_heq cut.erase.reconstruct_scope.symm cut.erase.hints.symm cut.forest.symm captured.original larger
  closing := by
    intro permission
    obtain ⟨annotation, ready, kept⟩ := captured.closing permission
    refine ⟨annotation.world_weaken larger, annotation.world_weaken_valid larger ready, ?_⟩
    rw [Retained.ofCapability_world_weaken, Retained.ofCapability_world_weaken, kept,
      ← SourceBoundSnapshots.Retained.forClosing_world_weaken]

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.CaptureSource.transport
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.CaptureSource.world_weaken
