import SourceCodeRecords

/-! Positional source coverage composes and splits at existing forest
boundaries. Capture preserves the actual records and their receiving sites.
No new source validation or future execution assumption is introduced. -/
namespace Ash.OneShot.SourceScheduledSavedPlans
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Reuse existing scope/hint/forest reassociation to identify packed receivers. -/
theorem saved_append_assoc
    {firstHints : Hints firstScope} {secondHints : Hints secondScope} {thirdHints : Hints thirdScope}
    (first : Forest firstHints) (second : Forest secondHints) (third : Forest thirdHints) :
    (⟨_, _, (first.append second).append third⟩ : Saved) = ⟨_, _, first.append (second.append third)⟩ :=
  (SourceScheduledRecomposition.predicate_congr
    (SourceDependencyChecks.scope_append_assoc _ _ _)
    (SourcePlannedRecomposition.hints_append_assoc firstHints secondHints thirdHints)
    (SourceScheduledRecomposition.forest_append_assoc first second third)
    (fun forest => (⟨_, _, forest⟩ : Saved) = ⟨_, _, first.append (second.append third)⟩)).mpr rfl

end Ash.OneShot.SourceScheduledSavedPlans

namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation ofCode)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy)
open SourceScheduledSavedPlans (saved_append_assoc Saved)

variable [DeclarationPolicy]

/-- Read the actual source at a position whose packed receiver is identified.
No compilation or choice of replacement metadata is involved. -/
theorem CodeRecord.at_receiver {plan : Plan dependencies} {bounds : Annotation world plan}
    (record : CodeRecord outward actions phases bounds)
    {hints : Hints scope} {forest : Forest hints}
    (located : record.receiver = ⟨_, _, forest⟩) :
    ∃ source : Code world plan forest, source.Valid outward actions phases ∧ ofCode source = bounds := by
  cases record with
  | mk receiver source origin valid =>
      cases located
      exact ⟨source, valid, origin⟩

private def recordedForest {hints : Hints scope} {forest : Forest hints}
    {bounds : Retained world forest} (_records : bounds.Records Payload) : Forest hints := forest

/-- Receiving-suffix reassociation changes only indices. -/
theorem Retained.Records.AtReceivers.receiver_assoc
    {bounds : Retained world forest}
    {records : bounds.Records (CodeRecord outward actions phases)}
    {firstHints : Hints firstScope} {secondHints : Hints secondScope} {thirdHints : Hints thirdScope}
    (first : Forest firstHints) (second : Forest secondHints) (third : Forest thirdHints) :
    AtReceivers outward actions phases records ((first.append second).append third) ↔
      AtReceivers outward actions phases records (first.append (second.append third)) :=
  SourceScheduledRecomposition.predicate_congr
    (SourceDependencyChecks.scope_append_assoc _ _ _)
    (SourcePlannedRecomposition.hints_append_assoc firstHints secondHints thirdHints)
    (SourceScheduledRecomposition.forest_append_assoc first second third)
    (fun outside => AtReceivers outward actions phases records outside)

/-- Source records split at the same boundary as their actual metadata.
Both directions retain every original record value, including saved branches. -/
theorem Retained.Records.AtReceivers.append_iff
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    {firstBounds : Retained world first} {secondBounds : Retained world second}
    (leading : firstBounds.Records (CodeRecord outward actions phases))
    (trailing : secondBounds.Records (CodeRecord outward actions phases))
    {outsideHints : Hints outsideScope} (outside : Forest outsideHints) :
    AtReceivers outward actions phases (leading.append trailing) outside ↔
      AtReceivers outward actions phases leading (second.append outside) ∧
      AtReceivers outward actions phases trailing outside := by
  induction leading with
  | nil =>
      constructor
      · intro covered; exact ⟨.nil, covered⟩
      · intro covered; exact covered.2
  | plain record tail ih =>
      constructor
      · intro covered
        cases covered with
        | plain located remaining =>
          obtain ⟨firstCovered, lastCovered⟩ := ih.mp remaining
          exact ⟨.plain (located.trans (saved_append_assoc (recordedForest tail) second outside)) firstCovered, lastCovered⟩
      · rintro ⟨covered, lastCovered⟩
        cases covered with
        | plain located remaining =>
          exact .plain (located.trans (saved_append_assoc (recordedForest tail) second outside).symm)
            (ih.mpr ⟨remaining, lastCovered⟩)
  | handler tail ih =>
      constructor
      · intro covered; cases covered with
        | handler remaining => obtain ⟨firstCovered, lastCovered⟩ := ih.mp remaining; exact ⟨.handler firstCovered, lastCovered⟩
      · rintro ⟨covered, lastCovered⟩; cases covered with
        | handler remaining => exact .handler (ih.mpr ⟨remaining, lastCovered⟩)
  | cell tail ih =>
      constructor
      · intro covered; cases covered with
        | cell remaining => obtain ⟨firstCovered, lastCovered⟩ := ih.mp remaining; exact ⟨.cell firstCovered, lastCovered⟩
      · rintro ⟨covered, lastCovered⟩; cases covered with
        | cell remaining => exact .cell (ih.mpr ⟨remaining, lastCovered⟩)
  | cleanup record tail ih =>
      have same := congrArg (fun receiving : Saved => (⟨_, _, Forest.running receiving.forest⟩ : Saved))
        (saved_append_assoc (recordedForest tail) second outside)
      constructor
      · intro covered
        cases covered with
        | cleanup located remaining =>
          obtain ⟨firstCovered, lastCovered⟩ := ih.mp remaining
          exact ⟨.cleanup (located.trans same) firstCovered, lastCovered⟩
      · rintro ⟨covered, lastCovered⟩
        cases covered with
        | cleanup located remaining => exact .cleanup (located.trans same.symm) (ih.mpr ⟨remaining, lastCovered⟩)
  | running tail ih =>
      constructor
      · intro covered; cases covered with
        | running remaining => obtain ⟨firstCovered, lastCovered⟩ := ih.mp remaining; exact ⟨.running firstCovered, lastCovered⟩
      · rintro ⟨covered, lastCovered⟩; cases covered with
        | running remaining => exact .running (ih.mpr ⟨remaining, lastCovered⟩)
  | live saved tail ihSaved ih =>
      constructor
      · intro covered
        cases covered with
        | live inside remaining =>
          obtain ⟨firstCovered, lastCovered⟩ := ih.mp remaining
          exact ⟨.live ((receiver_assoc (recordedForest tail) second outside).mp inside) firstCovered, lastCovered⟩
      · rintro ⟨covered, lastCovered⟩
        cases covered with
        | live inside remaining =>
          exact .live ((receiver_assoc (recordedForest tail) second outside).mpr inside) (ih.mpr ⟨remaining, lastCovered⟩)
  | spent tail ih =>
      constructor
      · intro covered; cases covered with
        | spent remaining => obtain ⟨firstCovered, lastCovered⟩ := ih.mp remaining; exact ⟨.spent firstCovered, lastCovered⟩
      · rintro ⟨covered, lastCovered⟩; cases covered with
        | spent remaining => exact .spent (ih.mpr ⟨remaining, lastCovered⟩)

/-- The existing capture movement keeps each original code record at the same
receiving suffix. The new live boundary changes storage, not these suffixes. -/
theorem RecordCapture.at_receivers
    {before after : Snapshot world}
    {records : before.pending.Records (CodeRecord outward actions phases)}
    {next : after.pending.Records (CodeRecord outward actions phases)}
    (moved : RecordCapture owner (CodeRecord outward actions phases) records next)
    (covered : Retained.Records.AtReceivers outward actions phases records .nil) :
    Retained.Records.AtReceivers outward actions phases next .nil := by
  cases moved with
  | cut before after inside outside =>
      obtain ⟨insideCovered, outsideCovered⟩ := (Retained.Records.AtReceivers.append_iff inside outside .nil).mp covered
      exact .live insideCovered outsideCovered

/-- Actual capture produces complete positioned source records, preserving
their values through the existing all-record capture theorem. -/
theorem Captured.carry_code_records {before after : Snapshot world}
    (step : Captured owner before after)
    (records : before.pending.Records (CodeRecord outward actions phases))
    (covered : Retained.Records.AtReceivers outward actions phases records .nil) :
    ∃ next : after.pending.Records (CodeRecord outward actions phases),
      RecordCapture owner (CodeRecord outward actions phases) records next ∧
      Retained.Records.AtReceivers outward actions phases next .nil := by
  obtain ⟨next, moved⟩ := step.carry_records records
  exact ⟨next, moved, moved.at_receivers covered⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceScheduledSavedPlans.saved_append_assoc
#print axioms Ash.OneShot.SourceBoundSnapshots.CodeRecord.at_receiver
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.AtReceivers.receiver_assoc
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.AtReceivers.append_iff
#print axioms Ash.OneShot.SourceBoundSnapshots.RecordCapture.at_receivers
#print axioms Ash.OneShot.SourceBoundSnapshots.Captured.carry_code_records
