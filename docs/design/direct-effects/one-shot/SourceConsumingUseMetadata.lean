import SourceConsumingUseTransport
import SourceConsumingContextualCapture

/-! Structural correspondence between an original continuation context and
actual pending bounds. The saved metadata is fixed at capture; syntax-directed
caller growth and neutral runtime frames preserve its recorded provenance.
No field assumes validity of a future source or execution. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
open SourceBoundSnapshots (Snapshot)
open SourceBoundSnapshots.Retained (ofCapability)

variable [declarations : DeclarationPolicy]

/-- Original saved and canonical closing bounds, together with the structural
movement of the actual caller and waiting metadata. Neutral movement may insert
pure frames or spent history, but cannot choose different interpretation code. -/
structure UseMetadata
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (original : Context world owner outward actions phases base baseFront saved waiting)
    {frontHints : Hints frontScope} (front : Forest frontHints)
    {targetHints : Hints targetScope} {target : Forest targetHints}
    (pending : SourceBoundSnapshots.Retained world target) where
  captured : SourceBoundSnapshots.Retained world saved
  resumption : ∀ permission, original.continuationBounds.resumption permission = captured
  closing : ∀ permission, original.continuationBounds.closing permission = captured.forClosing
  movement : SourceBoundSnapshots.Retained.Neutral world
    ((SourceBoundSnapshots.Retained.absent front).append
      (.live (owner := owner) captured (ofCapability original.after))) pending

variable {baseHints : Hints baseScope} {base : Forest baseHints}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {original : Context world owner outward actions phases base baseFront saved waiting}
  {frontHints : Hints frontScope} {front : Forest frontHints}
  {targetHints : Hints targetScope} {target : Forest targetHints}
  {pending : SourceBoundSnapshots.Retained world target}

/-- Fresh capture starts with no caller frames and exact original metadata. -/
def UseMetadata.captured_root
    (captured : SourceBoundSnapshots.Retained world saved)
    (resumption : ∀ permission, original.continuationBounds.resumption permission = captured)
    (closing : ∀ permission, original.continuationBounds.closing permission = captured.forClosing) :
    UseMetadata original Forest.nil (.live (owner := owner) captured (ofCapability original.after)) :=
  ⟨captured, resumption, closing, .refl⟩

def UseMetadata.handler (metadata : UseMetadata original front pending) :
    UseMetadata original (.handler (effect := effect) (table := table) (families := families) (required := required) front)
      (.handler (effect := effect) (table := table) (families := families) (required := required) pending) :=
  ⟨metadata.captured, metadata.resumption, metadata.closing, .handler metadata.movement⟩

def UseMetadata.cleanup (metadata : UseMetadata original front pending) :
    UseMetadata original (.cleanup (needs := needs) callback front)
      (.cleanup (needs := needs) (.absent (plan := callback)) pending) :=
  ⟨metadata.captured, metadata.resumption, metadata.closing, .cleanup metadata.movement⟩

def UseMetadata.cell (metadata : UseMetadata original front pending) :
    UseMetadata original (.cell (identity := identity) front) (.cell (identity := identity) pending) :=
  ⟨metadata.captured, metadata.resumption, metadata.closing, .cell metadata.movement⟩

/-- Administrative focus changes the actual receiver, retaining the original
source caller. This is different from source-directed caller growth. -/
def UseMetadata.extra (metadata : UseMetadata original front pending) :
    UseMetadata original front (.plain (.absent (plan := .pure)) pending) :=
  ⟨metadata.captured, metadata.resumption, metadata.closing, .extra metadata.movement⟩

def UseMetadata.completion (metadata : UseMetadata original front pending) :
    UseMetadata original front (.cleanup (needs := []) (.absent (plan := .pure)) pending) :=
  ⟨metadata.captured, metadata.resumption, metadata.closing, .completion metadata.movement⟩

def UseMetadata.history (metadata : UseMetadata original front pending) :
    UseMetadata original front (.spent (owner := retired) pending) :=
  ⟨metadata.captured, metadata.resumption, metadata.closing, .history metadata.movement⟩

/-- Permission extension preserves the original entries. Equal selected-owner
rights prevent inventing metadata for a newly permitted action. -/
def UseMetadata.extend_permissions (metadata : UseMetadata original front pending)
    (permissions : Syntax.UsageExtension actions nextActions) (same : actions owner = nextActions owner) :
    UseMetadata (original.extend_permissions permissions same) front pending :=
  ⟨metadata.captured, (fun permission => metadata.resumption (by simpa only [same] using permission)),
    (fun permission => metadata.closing (by simpa only [same] using permission)), metadata.movement⟩

def UseMetadata.restrict_phases (metadata : UseMetadata original front pending)
    (extension : SourceScheduledPhaseRestriction.AvailableOn (SourceDependencyOwners.owners baseScope) phases nextPhases) :
    UseMetadata (original.restrict_phases extension) front pending :=
  ⟨metadata.captured, metadata.resumption, metadata.closing, metadata.movement⟩

/-- Fresh resource worlds preserve the exact same origin and canonical closing
projection. Existing world/append/closing laws transport every equality. -/
def UseMetadata.world_weaken (metadata : UseMetadata original front pending) (larger : world ⊆ nextWorld) :
    UseMetadata (original.world_weaken larger) front (pending.world_weaken larger) := by
  refine ⟨metadata.captured.world_weaken larger, ?_, ?_, ?_⟩
  · intro permission
    simpa only [Context.world_weaken, Context.continuationBounds,
      SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken] using
      congrArg (fun bounds => bounds.world_weaken larger) (metadata.resumption permission)
  · intro permission
    simpa only [Context.world_weaken, Context.continuationBounds,
      SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken,
      SourceBoundSnapshots.Retained.forClosing_world_weaken] using
      congrArg (fun bounds => bounds.world_weaken larger) (metadata.closing permission)
  · simpa only [SourceBoundSnapshots.Retained.world_weaken_append,
      SourceBoundSnapshots.Retained.absent_world_weaken, SourceBoundSnapshots.Retained.world_weaken,
      Context.world_weaken, SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken] using
      metadata.movement.world_weaken larger

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.captured_root
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.handler
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.cleanup
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.cell
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.extra
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.completion
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.history
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.extend_permissions
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.restrict_phases
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseMetadata.world_weaken
