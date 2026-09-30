import SourceScheduledRetainedSplit
import SourceBoundCapture

/-! Couple the valid source pieces at an actual capture cut to the exact
persistent snapshot moved by capture. Original snapshot/source agreement is
preserved; individually valid but unrelated replacement metadata cannot suffice. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceBoundSnapshots (Snapshot Captured)
open SourceBoundSnapshots.Retained (ofCapability)

/-- Exact recomposition identifies the runtime capture using the existing cut
relation. The metadata may have been obtained by any source-directed split. -/
theorem capture_snapshot_from_parts
    (snapshot : Snapshot world)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes snapshot.forest saved waiting)
    (inside : SourceBoundSnapshots.Retained world saved)
    (tail : SourceBoundSnapshots.Retained world waiting)
    (kept : HEq (inside.append tail) snapshot.pending)
    {plan : Plan dependencies} (current : SourcePlanBounds.Annotation world plan) :
    Captured owner snapshot ⟨_, plan, current, _, _, .live (owner := owner) saved waiting,
      .live inside tail⟩ := by
  rcases snapshot with ⟨_, beforePlan, beforeCurrent, _, _, forest, pending⟩
  cases cut.erase.reconstruct_scope
  cases cut.erase.hints
  have same := eq_of_heq cut.forest
  cases same
  have metadata := eq_of_heq kept
  cases metadata
  exact .cut beforeCurrent current inside tail

variable [DeclarationPolicy]

/-- The same source-derived pieces are valid and form the captured snapshot.
The selected clause's current metadata is independent of this retained split. -/
theorem capture_source_snapshot
    (snapshot : Snapshot world)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes snapshot.forest saved waiting)
    (source : Retained world snapshot.forest .nil) (ready : source.Valid outward actions phases)
    (aligned : ofCapability source = snapshot.pending)
    {plan : Plan dependencies} (current : SourcePlanBounds.Annotation world plan) :
    ∃ inside : Retained world saved waiting, ∃ tail : Retained world waiting .nil,
      inside.Valid outward actions phases ∧ tail.Valid outward actions phases ∧
      Captured owner snapshot ⟨_, plan, current, _, _, .live (owner := owner) saved waiting,
        .live (ofCapability inside) (ofCapability tail)⟩ := by
  obtain ⟨inside, tail, insideReady, tailReady, kept⟩ := retained_at_cut_retaining cut source ready
  exact ⟨inside, tail, insideReady, tailReady,
    capture_snapshot_from_parts snapshot cut (ofCapability inside) (ofCapability tail)
      (kept.trans (heq_of_eq aligned)) current⟩

/-- Admission of both retained pieces is inherited from the original snapshot;
the chosen clause supplies only its own current-plan metadata admission. -/
theorem capture_source_snapshot_admitted
    (snapshot : Snapshot world) (snapshotReady : snapshot.Admitted)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes snapshot.forest saved waiting)
    (source : Retained world snapshot.forest .nil) (ready : source.Valid outward actions phases)
    (aligned : ofCapability source = snapshot.pending)
    {plan : Plan dependencies} (current : SourcePlanBounds.Annotation world plan) (currentReady : current.Admitted) :
    ∃ inside : Retained world saved waiting, ∃ tail : Retained world waiting .nil,
      inside.Valid outward actions phases ∧ tail.Valid outward actions phases ∧
      Captured owner snapshot ⟨_, plan, current, _, _, .live (owner := owner) saved waiting,
        .live (ofCapability inside) (ofCapability tail)⟩ ∧
      (ofCapability inside).Admitted ∧ (ofCapability tail).Admitted := by
  obtain ⟨inside, tail, insideReady, tailReady, captured⟩ := capture_source_snapshot (owner := owner) snapshot cut source ready aligned current
  have admitted := captured.admitted snapshotReady currentReady
  have pending := admitted.2
  cases pending with
  | live saved waiting => exact ⟨inside, tail, insideReady, tailReady, captured, saved, waiting⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.capture_source_snapshot
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.capture_source_snapshot_admitted

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.capture_snapshot_from_parts
