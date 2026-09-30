import SourceScheduledPrefixRetention
import SourceBoundRecords

/-! Carry actual queued source payloads through partial caller closing.
Canonical metadata equality supplies the indices; closing filters out pending
prefix records and retains original callback and suffix values in order. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

universe u
variable {Payload : RecordFamily.{u} world}

/-- Closing retains callback payloads, including in dormant branches, and
drops ordinary pending payloads. No new record value is constructed. -/
def Retained.Records.forClosing {bounds : Retained world forest} (records : bounds.Records Payload) :
    bounds.forClosing.Records Payload :=
  match records with
  | .nil => .nil
  | .plain _ tail | .handler tail | .spent tail => tail.forClosing
  | .cell tail => .cell tail.forClosing
  | .cleanup payload tail => .cleanup payload tail.forClosing
  | .running tail => .running tail.forClosing
  | .live saved tail => saved.forClosing.append (.running tail.forClosing)

def RecordEntry.isCallback (entry : RecordEntry Payload) : Bool :=
  match entry.position with
  | .pending => false
  | .callback => true

/-- Exact ordered filtering, including payload values and their multiplicity. -/
theorem Retained.Records.forClosing_entries {bounds : Retained world forest}
    (records : bounds.Records Payload) :
    records.forClosing.entries = records.entries.filter RecordEntry.isCallback := by
  induction records with
  | nil => rfl
  | plain payload tail ih =>
      change tail.forClosing.entries = _
      simpa only [Records.entries, List.filter_cons, RecordEntry.isCallback, Bool.false_eq_true, if_false] using ih
  | handler tail ih | cell tail ih | running tail ih | spent tail ih => exact ih
  | cleanup payload tail ih =>
      simpa only [Records.forClosing, Records.entries, List.filter_cons, RecordEntry.isCallback, if_true] using
        congrArg (List.cons (⟨.callback, _, _, _, payload⟩ : RecordEntry Payload)) ih
  | live saved tail ihSaved ihTail =>
      change (saved.forClosing.append (.running tail.forClosing)).entries = _
      rw [Records.append_entries]
      change saved.forClosing.entries ++ tail.forClosing.entries =
        (saved.entries ++ tail.entries).filter RecordEntry.isCallback
      rw [List.filter_append, ihSaved, ihTail]

/-- Changing an equality index does not change any stored entry. -/
theorem Retained.Records.cast_entries {first second : Retained world forest}
    (same : first = second) (records : first.Records Payload) :
    (same ▸ records : second.Records Payload).entries = records.entries := by
  cases same
  rfl

/-- The original canonical split carries the exact original payload tree.
This reuses the established record split/join theorem. -/
theorem Retained.Records.splitAt_retaining
    {leadingHints : Hints leadingScope} {suffixHints : Hints suffixScope}
    (leading : Forest leadingHints) (suffix : Forest suffixHints)
    {bounds : Retained world (leading.append suffix)} (records : bounds.Records Payload) :
    ∃ inside : ((bounds.splitAt leading suffix).1).Records Payload,
      ∃ outside : ((bounds.splitAt leading suffix).2).Records Payload,
      HEq (inside.append outside) records := by
  have original := bounds.splitAt_append leading suffix
  generalize known : bounds.splitAt leading suffix = pieces at *
  rcases pieces with ⟨first, second⟩
  cases original
  exact ⟨records.of_append.1, records.of_append.2, heq_of_eq records.of_append_join⟩

/-- The optional running boundary carries the original suffix payloads. -/
theorem BoundaryBounds.carry_records
    {source : Forest sourceHints} {target : Forest targetHints}
    {original : Retained world source} {result : Retained world target}
    (kept : BoundaryBounds original result) (records : original.Records Payload) :
    ∃ next : result.Records Payload, next.entries = records.entries := by
  cases kept with
  | same => exact ⟨records, rfl⟩
  | protect => exact ⟨.running records, rfl⟩

end Ash.OneShot.SourceBoundSnapshots

namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Retained DeclarationPolicy DeclarationLaws)
open SourceBoundSnapshots (RecordFamily RecordEntry)
open SourceBoundSnapshots.Retained (ofCapability)

universe u
variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Compile and move the actual original source records in one result. The
prefix split reconstructs the original payload tree; the target retains its
callbacks followed by the unchanged suffix, never replacement source records. -/
theorem PrefixClosing.compile_records
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {prefixHints : Hints prefixScope} {suffixHints : Hints suffixScope}
    {targetHints : Hints targetScope} {leading : Forest prefixHints} {suffix : Forest suffixHints}
    {target : Forest targetHints} {source : Retained world (leading.append suffix) outside}
    (closing : PrefixClosing outward actions phases (suffix := suffix) leading source target next)
    (ready : source.Valid outward actions phases)
    {Payload : RecordFamily.{u} world} (records : (ofCapability source).Records Payload) :
    ∃ annotation : Retained world (leading.forClosing.append target) next,
      ∃ moved : (ofCapability annotation).Records Payload,
      ∃ inside : ((ofCapability source).splitAt leading suffix).1.Records Payload,
      ∃ suffixRecords : ((ofCapability source).splitAt leading suffix).2.Records Payload,
      annotation.Valid outward actions phases ∧ HEq (inside.append suffixRecords) records ∧
      moved.entries = inside.entries.filter RecordEntry.isCallback ++ suffixRecords.entries := by
  obtain ⟨annotation, boundary, valid, origin, kept⟩ := closing.compile_retaining laws project ready
  obtain ⟨inside, suffixRecords, original⟩ := records.splitAt_retaining leading suffix
  obtain ⟨protectedRecords, protectedOrigin⟩ := origin.carry_records suffixRecords
  let joined := inside.forClosing.append protectedRecords
  refine ⟨annotation, kept.symm ▸ joined, inside, suffixRecords, valid, original, ?_⟩
  rw [SourceBoundSnapshots.Retained.Records.cast_entries]
  change (inside.forClosing.append protectedRecords).entries = _
  rw [SourceBoundSnapshots.Retained.Records.append_entries,
    SourceBoundSnapshots.Retained.Records.forClosing_entries, protectedOrigin]

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.forClosing_entries
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.cast_entries
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.splitAt_retaining
#print axioms Ash.OneShot.SourceBoundSnapshots.BoundaryBounds.carry_records
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosing.compile_records
