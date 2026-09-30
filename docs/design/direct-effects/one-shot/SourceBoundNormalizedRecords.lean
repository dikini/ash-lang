import SourceScheduledNormalizedRechecking
import SourceBoundRecords
import SourceConsumingQueuedAdmission

/-! Canonical record indices retain the actual original source payload and its
bound provenance. This is a representation change, not a derivation of payload
validity at a changed receiver. Existing record capture and resumption move the
packed values unchanged. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanBounds (Annotation ofCode)

universe u

/-- Keep the source witness at its original bound index, with exact evidence
that the canonical record index is its normalization. -/
structure CanonicalPayload (Payload : RecordFamily.{u} world)
    {dependencies : SourceDependencyAnnotations.Dependencies} {plan : Plan dependencies}
    (bounds : Annotation world plan) where
  sourceBounds : Annotation world plan
  source : Payload sourceBounds
  alignment : sourceBounds.normalize = bounds

/-- The packed record already has a stable runtime index; repeated code
normalization cannot require another change of that index. -/
theorem CanonicalPayload.canonical_bounds (record : CanonicalPayload Payload bounds) :
    bounds.normalize = bounds :=
  (congrArg Annotation.normalize record.alignment.symm).trans
    (record.sourceBounds.normalize_idempotent.trans record.alignment)

variable {Payload : RecordFamily.{u} world}

def RecordEntry.original (entry : RecordEntry (CanonicalPayload Payload)) : RecordEntry Payload :=
  ⟨entry.position, _, _, entry.payload.sourceBounds, entry.payload.source⟩

/-- Expand bound indices while preserving every original record value. -/
def Retained.Records.normalize {bounds : Retained world forest}
    (records : bounds.Records Payload) : bounds.normalize.Records (CanonicalPayload Payload) :=
  match records with
  | .nil => .nil
  | .plain source tail => .plain ⟨_, source, rfl⟩ tail.normalize
  | .handler tail => .handler tail.normalize
  | .cell tail => .cell tail.normalize
  | .cleanup source tail => .cleanup ⟨_, source, rfl⟩ tail.normalize
  | .running tail => .running tail.normalize
  | .live saved tail => .live saved.normalize tail.normalize
  | .spent tail => .spent tail.normalize

/-- Source values, order, positions and multiplicity survive canonicalization;
no source proof is inferred from the new bound tree. -/
theorem Retained.Records.normalize_entries {bounds : Retained world forest}
    (records : bounds.Records Payload) :
    records.normalize.entries.map RecordEntry.original = records.entries := by
  induction records <;> simp_all only [Records.normalize, Records.entries, List.map_nil,
    List.map_cons, List.map_append, RecordEntry.original] <;> rfl

/-- Reuse the existing exact record capture at the normalized metadata cut. -/
theorem Captured.carry_normalized_records {before after : Snapshot world}
    (step : Captured owner before after) (records : before.pending.Records Payload) :
    ∃ next : after.normalize.pending.Records (CanonicalPayload Payload),
      RecordCapture owner (CanonicalPayload Payload)
        (before := before.normalize) (after := after.normalize) records.normalize next ∧
      next.entries.map RecordEntry.original = records.entries := by
  obtain ⟨next, moved⟩ := step.normalize.carry_records records.normalize
  exact ⟨next, moved, (congrArg (List.map RecordEntry.original) moved.entries).trans records.normalize_entries⟩

/-- The old resumption proof also preserves the packed source values, with
exactly its existing saved/caller permutation. No receiver validity is added. -/
theorem Resumed.carry_normalized_records {before after : Snapshot world}
    (step : Resumed owner before after) (records : before.pending.Records Payload) :
    ∃ next : after.normalize.pending.Records (CanonicalPayload Payload),
      RecordResumption owner (CanonicalPayload Payload)
        (before := before.normalize) (after := after.normalize) records.normalize next ∧
      records.entries.Perm (next.entries.map RecordEntry.original) := by
  obtain ⟨next, moved⟩ := step.normalize.carry_records records.normalize
  exact ⟨next, moved, records.normalize_entries ▸ moved.entries.map RecordEntry.original⟩

variable [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open SourceConsumingCleanupAdmission (Context QueuedBody)
open SourceScheduledCapabilityAnnotations (Code DeclarationLaws)

variable
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {wholeHints : SourceContextualHints.Hints wholeScope}
    {frontHints : SourceContextualHints.Hints frontScope}
    {savedHints : SourceContextualHints.Hints savedScope}
    {waitingHints : SourceContextualHints.Hints waitingScope}
    {whole : SourceRetainedPlans.Forest wholeHints} {front : SourceRetainedPlans.Forest frontHints}
    {saved : SourceRetainedPlans.Forest savedHints} {waiting : SourceRetainedPlans.Forest waitingHints}
    {context : Context world owner outward actions phases whole front saved waiting}
    {plan : Plan dependencies} {bounds : Annotation world plan}

/-- The retained original queued derivation generates expanded source aligned
with the canonical record index. Generation still takes place at its recorded
context; capture/restoration does not grant new receiver capabilities. -/
theorem CanonicalPayload.generate_queued
    (record : CanonicalPayload
      (fun bounds => QueuedBody laws project resumeRequired closeRequired context bounds) bounds) :
    ∃ annotation : Code world plan whole, annotation.Valid outward actions phases ∧
      ofCode annotation = bounds ∧ annotation.Expanded ∧ bounds.Admitted := by
  obtain ⟨original, originalReady, originalBounds⟩ :=
    record.source.source.generate_retaining record.source.checked
  obtain ⟨annotation, ready, normalized, expanded⟩ :=
    Code.normalize (fun recipes => project (laws.legacyAdmission recipes)) originalReady
  have origin := originalBounds.trans record.source.origin.symm
  have aligned := normalized.trans ((congrArg Annotation.normalize origin).trans record.alignment)
  have admitted : record.sourceBounds.Admitted := record.source.origin.symm ▸ record.source.nested.boundAnnotation_admitted
  exact ⟨annotation, ready, aligned, expanded, record.alignment ▸ admitted.normalize⟩

/-- Recomposition retains the same original queued source and its existing
admission proof beneath the runtime's pure value prefixes. -/
def CanonicalPayload.plug_queued
    (record : CanonicalPayload
      (fun bounds => QueuedBody laws project resumeRequired closeRequired context bounds) bounds)
    (position : SourceAnnotatedCode.Context) :
    CanonicalPayload
      (fun bounds => QueuedBody laws project resumeRequired closeRequired context bounds)
      (bounds.plug position).2.2 := by
  have source := record.source.plug position
  cases position <;> refine ⟨_, source, ?_⟩ <;>
    simp only [Annotation.plug, Annotation.normalize, Annotation.empty, record.alignment]

/-- Use the record actually returned at the normalized plain frame. The old
queued derivation supplies all source premises; the target annotation and its
exact canonical bounds are generated, not assumed. -/
theorem CanonicalPayload.returned_queued
    (record : CanonicalPayload
      (fun bounds => QueuedBody laws project resumeRequired closeRequired context bounds) bounds)
    (position : SourceAnnotatedCode.Context)
    {currentPlan : Plan currentDependencies} (current : Annotation world currentPlan)
    (pending : Retained world whole) {next : Snapshot world}
    (step : Returned position
      ⟨_, currentPlan, current, _, _, .plain plan whole, .plain bounds pending⟩ next) :
    ∃ annotation : Code world next.plan next.forest, annotation.Valid outward actions phases ∧
      ofCode annotation = next.current ∧ annotation.Expanded ∧ next.current.Admitted := by
  cases step
  exact (record.plug_queued position).generate_queued

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.normalize_entries
#print axioms Ash.OneShot.SourceBoundSnapshots.Captured.carry_normalized_records
#print axioms Ash.OneShot.SourceBoundSnapshots.Resumed.carry_normalized_records
#print axioms Ash.OneShot.SourceBoundSnapshots.CanonicalPayload.generate_queued

#print axioms Ash.OneShot.SourceBoundSnapshots.CanonicalPayload.plug_queued
#print axioms Ash.OneShot.SourceBoundSnapshots.CanonicalPayload.returned_queued

#print axioms Ash.OneShot.SourceBoundSnapshots.CanonicalPayload.canonical_bounds
