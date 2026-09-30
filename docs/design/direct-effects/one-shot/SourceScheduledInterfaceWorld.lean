import SourceScheduledRetainedInterfaces

/-! Opening a fresh resource preserves the operation annotations already
retained by a clause. World extension does not change operation requirements,
source plans or their receiving-order checks. -/
namespace Ash.OneShot.SourceScheduledSourceInterfaces

theorem Declared.world_weaken (declared : Declared world checking) (larger : world ⊆ next) :
    Declared next checking := by
  induction declared generalizing next with
  | pure => exact .pure
  | request => exact .request
  | invoke => exact .invoke
  | sequence first second ihFirst ihSecond => exact .sequence (ihFirst larger) (ihSecond larger)
  | choice first second ihFirst ihSecond => exact .choice (ihFirst larger) (ihSecond larger)
  | handler declarations body ih => exact .handler declarations (ih larger)
  | cleanup callback body ihCallback ihBody => exact .cleanup (ihCallback larger) (ihBody larger)
  | resource body ih =>
      exact .resource (fun identity fresh => ih identity (fun member => fresh (larger member))
        (ScopedExpressions.append_subset larger (List.Subset.refl _)))

end Ash.OneShot.SourceScheduledSourceInterfaces

namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

def Interfaces.world_weaken {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (larger : world ⊆ next) : Interfaces next forest :=
  match interfaces with
  | .nil => .nil
  | .plain rest required footprint declared tail =>
      .plain rest required footprint (declared.world_weaken larger) (tail.world_weaken larger)
  | .handler rest tail => .handler rest (tail.world_weaken larger)
  | .cell tail => .cell (tail.world_weaken larger)
  | .cleanup rest required footprint declared tail =>
      .cleanup rest required footprint (declared.world_weaken larger) (tail.world_weaken larger)
  | .running tail => .running (tail.world_weaken larger)
  | .live rest saved tail => .live rest (saved.world_weaken larger) (tail.world_weaken larger)
  | .spent tail => .spent (tail.world_weaken larger)

theorem Interfaces.world_weaken_trans {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (first : world ⊆ middle) (second : middle ⊆ next) :
    (interfaces.world_weaken first).world_weaken second = interfaces.world_weaken (first.trans second) := by
  induction interfaces <;> simp_all [Interfaces.world_weaken]

/-- Extension preserves acceptance and rejection at every receiving scope. -/
theorem Interfaces.check_world_weaken {hints : Hints scope} {forest : Forest hints}
    (interfaces : Interfaces world forest) (larger : world ⊆ next) :
    (interfaces.world_weaken larger).check outside = interfaces.check outside := by
  induction interfaces generalizing outside <;>
    simp_all [Interfaces.world_weaken, Interfaces.check] <;> rfl

end Ash.OneShot.SourceScheduledRetainedInterfaces

#print axioms Ash.OneShot.SourceScheduledSourceInterfaces.Declared.world_weaken
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_world_weaken

#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.world_weaken_trans
