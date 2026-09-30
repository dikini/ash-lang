import SourceScheduledPrefixRecords

/-! Exact source-record movement through one-shot disposal. Saved ordinary
pending code is discarded, saved callbacks run in their original order, and
caller/waiting records survive. Dormant branches use the established closing
traversal; no payload is reconstructed from a bound annotation. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)

universe u

inductive RecordDisposal (owner : Nat) (Payload : RecordFamily.{u} world) :
    {before after : Snapshot world} → before.pending.Records Payload → after.pending.Records Payload → Prop where
  | cut {plan : Plan dependencies}
      {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
      {before : Retained world front} {captured : Retained world saved} {after : Retained world tail}
      (current : SourcePlanBounds.Annotation world plan)
      (caller : before.Records Payload) (inside : captured.Records Payload) (outside : after.Records Payload) :
      RecordDisposal owner Payload
        (before := ⟨_, plan, current, _, _, _, before.append (.live (owner := owner) captured after)⟩)
        (after := Snapshot.value (captured.forClosing.append (.running (before.append (.spent (owner := owner) after)))))
        (caller.append (.live inside outside)) (inside.forClosing.append (.running (caller.append (.spent outside))))

variable {Payload : RecordFamily.{u} world}

/-- This is ordered filtering of the selected saved segment only. Ordinary
caller and waiting records remain, and repeated callback values are not merged. -/
theorem RecordDisposal.entries {before after : Snapshot world}
    {records : before.pending.Records Payload} {next : after.pending.Records Payload}
    (step : RecordDisposal owner Payload records next) :
    ∃ caller saved waiting : List (RecordEntry Payload),
      records.entries = caller ++ saved ++ waiting ∧
      next.entries = saved.filter RecordEntry.isCallback ++ caller ++ waiting := by
  cases step with
  | cut current caller inside outside =>
      dsimp only [Snapshot.value]
      refine ⟨caller.entries, inside.entries, outside.entries, ?_, ?_⟩
      · simp only [Retained.Records.append_entries, Retained.Records.entries, List.append_assoc]
      · simp only [Retained.Records.append_entries, Retained.Records.entries,
          Retained.Records.forClosing_entries, List.append_assoc]

/-- The actual disposal snapshot determines the source-record cut. The
established append split reconstructs the original record tree, including all
recursive saved branches, before applying the existing callback filter. -/
theorem Discarded.carry_records {before after : Snapshot world}
    (step : Discarded owner before after) (records : before.pending.Records Payload) :
    ∃ next : after.pending.Records Payload, RecordDisposal owner Payload records next := by
  cases step with
  | cut current front saved tail =>
      dsimp only [Snapshot.value]
      have joined := records.of_append_join
      generalize known : records.of_append = pieces at *
      rcases pieces with ⟨caller, rest⟩
      cases rest with
      | live captured waiting =>
          refine ⟨captured.forClosing.append (.running (caller.append (.spent waiting))), ?_⟩
          rw [← joined]
          exact .cut current caller captured waiting

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.RecordDisposal.entries
#print axioms Ash.OneShot.SourceBoundSnapshots.Discarded.carry_records
