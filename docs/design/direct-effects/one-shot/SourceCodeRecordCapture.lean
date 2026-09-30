import SourceCodeRecordPositions
import SourceScheduledCapabilityPhases

/-! Introduce a fresh continuation capability for every retained code record,
then carry those records through actual capture. Existing capability transport
preserves the code annotation and its receiver; capture only splits the forest. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)
open OwnerPhaseTransitions (introduce)

variable [DeclarationPolicy]

def CodeRecord.fresh_owner (record : CodeRecord outward actions phases bounds)
    (fresh : actions owner = none) :
    CodeRecord outward (actions.insert owner rights) (introduce phases owner) bounds :=
  ⟨record.receiver, record.source, record.origin, record.source.valid_fresh_owner record.valid fresh⟩

def Retained.Records.fresh_owner {bounds : Retained world forest}
    (records : bounds.Records (CodeRecord outward actions phases))
    (fresh : actions owner = none) :
    bounds.Records (CodeRecord outward (actions.insert owner rights) (introduce phases owner)) :=
  match records with
  | .nil => .nil
  | .plain record tail => .plain (record.fresh_owner fresh) (tail.fresh_owner fresh)
  | .handler tail => .handler (tail.fresh_owner fresh)
  | .cell tail => .cell (tail.fresh_owner fresh)
  | .cleanup record tail => .cleanup (record.fresh_owner fresh) (tail.fresh_owner fresh)
  | .running tail => .running (tail.fresh_owner fresh)
  | .live saved tail => .live (saved.fresh_owner fresh) (tail.fresh_owner fresh)
  | .spent tail => .spent (tail.fresh_owner fresh)

theorem Retained.Records.AtReceivers.fresh_owner
    {hints : Hints scope} {forest : Forest hints} {bounds : Retained world forest}
    {records : bounds.Records (CodeRecord outward actions phases)}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (covered : AtReceivers outward actions phases records outside)
    (fresh : actions owner = none) :
    AtReceivers outward (actions.insert owner rights) (introduce phases owner)
      (records.fresh_owner fresh) outside := by
  induction covered with
  | nil => exact .nil
  | plain located _ ih => exact .plain located ih
  | handler _ ih => exact .handler ih
  | cell _ ih => exact .cell ih
  | cleanup located _ ih => exact .cleanup located ih
  | running _ ih => exact .running ih
  | live _ _ ihSaved ihTail => exact .live ihSaved ihTail
  | spent _ ih => exact .spent ih

/-- The actual capture carries all original pending and callback code,
including dormant saved branches, under the newly allocated owner's rights
and phase. The movement relation applies to the explicitly upgraded records. -/
theorem Captured.carry_fresh_code_records
    (step : Captured owner before after)
    (records : before.pending.Records (CodeRecord outward actions phases))
    (covered : Retained.Records.AtReceivers outward actions phases records .nil)
    (fresh : actions owner = none) :
    ∃ next : after.pending.Records (CodeRecord outward (actions.insert owner rights) (introduce phases owner)),
      RecordCapture owner _ (records.fresh_owner fresh) next ∧
      Retained.Records.AtReceivers outward (actions.insert owner rights) (introduce phases owner) next .nil :=
  step.carry_code_records (records.fresh_owner fresh) (covered.fresh_owner fresh)

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.CodeRecord.fresh_owner
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.fresh_owner
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.AtReceivers.fresh_owner
#print axioms Ash.OneShot.SourceBoundSnapshots.Captured.carry_fresh_code_records
