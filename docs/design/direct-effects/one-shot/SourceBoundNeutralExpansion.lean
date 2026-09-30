import SourceBoundResources
import SourceScheduledNeutralComposition

/-! Neutral changes of retained metadata preserve each original code annotation.
Inserted pure frames carry absent bounds; dormant saved branches stay exact. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyCapture (Scope)

inductive Retained.Neutral (world : List Nat) :
    {first second : Scope} → {beforeHints : Hints first} → {afterHints : Hints second} →
    {before : Forest beforeHints} → {after : Forest afterHints} →
    Retained world before → Retained world after → Prop where
  | refl : Neutral world source source
  | extra : Neutral world before after → Neutral world before (.plain (.absent (plan := .pure)) after)
  | completion : Neutral world before after →
      Neutral world before (.cleanup (needs := []) (.absent (plan := .pure)) after)
  | history : Neutral world before after → Neutral world before (.spent (owner := owner) after)
  | plain : Neutral world before after → Neutral world (.plain code before) (.plain code after)
  | handler : Neutral world before after →
      Neutral world (.handler (effect := effect) (table := table) (families := families) (required := required) before)
        (.handler (effect := effect) (table := table) (families := families) (required := required) after)
  | cell : Neutral world before after →
      Neutral world (.cell (identity := identity) before) (.cell (identity := identity) after)
  | cleanup : Neutral world before after →
      Neutral world (.cleanup (needs := needs) code before) (.cleanup (needs := needs) code after)
  | running : Neutral world before after → Neutral world (.running before) (.running after)
  | live : Neutral world before after →
      Neutral world (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Neutral world before after →
      Neutral world (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Retained.Neutral.forest {before : Retained world first} {after : Retained world second}
    (changed : Neutral world before after) : SourceScheduledNeutral.Expansion first second := by
  induction changed with
  | refl => exact .refl
  | extra _ ih => exact .extra ih
  | completion _ ih => exact .completion ih
  | history _ ih => exact .history ih
  | plain _ ih => exact .plain ih
  | handler _ ih => exact .handler ih
  | cell _ ih => exact .cell ih
  | cleanup _ ih => exact .cleanup ih
  | running _ ih => exact .running ih
  | live _ ih => exact .live ih
  | spent _ ih => exact .spent ih

theorem Retained.Neutral.absent (changed : SourceScheduledNeutral.Expansion before after) :
    Neutral world (Retained.absent before) (Retained.absent after) := by
  induction changed with
  | refl => exact .refl
  | extra _ ih => exact .extra ih
  | completion _ ih => exact .completion ih
  | history _ ih => exact .history ih
  | plain _ ih => exact .plain ih
  | handler _ ih => exact .handler ih
  | cell _ ih => exact .cell ih
  | cleanup _ ih => exact .cleanup ih
  | running _ ih => exact .running ih
  | live _ ih => exact .live ih
  | spent _ ih => exact .spent ih

/-- Fresh resource worlds preserve the same structural tail provenance. -/
theorem Retained.Neutral.world_weaken {before : Retained world first} {after : Retained world second}
    (changed : Neutral world before after) (larger : world ⊆ nextWorld) :
    Neutral nextWorld (before.world_weaken larger) (after.world_weaken larger) := by
  induction changed with
  | refl => exact .refl
  | extra _ ih => exact .extra ih
  | completion _ ih => exact .completion ih
  | history _ ih => exact .history ih
  | plain _ ih => exact .plain ih
  | handler _ ih => exact .handler ih
  | cell _ ih => exact .cell ih
  | cleanup _ ih => exact .cleanup ih
  | running _ ih => exact .running ih
  | live _ ih => exact .live ih
  | spent _ ih => exact .spent ih

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Neutral.forest
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Neutral.absent

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Neutral.world_weaken
