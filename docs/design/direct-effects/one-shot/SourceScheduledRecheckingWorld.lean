import SourceScheduledSourceRechecking
import SourceScheduledAnnotationWorldLaws

/-! Structural rechecking survives resource-world extension. Original source
annotations are weakened constructor by constructor; callback declarations and
pending-owner bounds reuse their existing world-extension theorems. -/
namespace Ash.OneShot.SourceScheduledCallbackInterfaces

theorem Declared.world_weaken (declared : Declared world interfaces) (larger : world ⊆ next) :
    Declared next interfaces := by
  induction declared with
  | nil => exact .nil
  | plain tail ih => exact .plain ih
  | handler tail ih => exact .handler ih
  | cell tail ih => exact .cell ih
  | cleanup source tail ih => exact .cleanup (source.world_weaken larger) ih
  | running tail ih => exact .running ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

end Ash.OneShot.SourceScheduledCallbackInterfaces

namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)

variable [DeclarationPolicy]

theorem weaken_rechecking_world (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ phases world {dependencies beforeScope afterScope} {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
      (plan : Plan dependencies) (before : Forest beforeHints) (source : Code world plan before) (after : Forest afterHints),
      Expression outward actions phases source after → ∀ next (larger : world ⊆ next),
      Expression outward actions phases (source.world_weaken larger) after) ∧
    (∀ phases world {beforeScope outsideScope afterScope nextOutsideScope}
      {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
      {afterHints : Hints afterScope} {nextOutsideHints : Hints nextOutsideScope}
      (before : Forest beforeHints) (outside : Forest outsideHints) (source : Retained world before outside)
      (after : Forest afterHints) (nextOutside : Forest nextOutsideHints),
      RetainedChange outward actions phases source after nextOutside → ∀ next (larger : world ⊆ next),
      RetainedChange outward actions phases (source.world_weaken larger) after nextOutside) := by
  constructor
  all_goals first
    | (intro phases world dependencies beforeScope afterScope beforeHints afterHints plan before source after changed
       apply Expression.rec
         (motive_1 := fun phases {world _ _ _ _ _} plan before source after _ =>
           ∀ next (larger : world ⊆ next), Expression outward actions phases (source.world_weaken larger) after)
         (motive_2 := fun phases {world _ _ _ _ _ _ _ _} before outside source after nextOutside _ =>
           ∀ next (larger : world ⊆ next), RetainedChange outward actions phases (source.world_weaken larger) after nextOutside)
         (t := changed))
    | (intro phases world beforeScope outsideScope afterScope nextOutsideScope beforeHints outsideHints afterHints nextOutsideHints
         before outside source after nextOutside changed
       apply RetainedChange.rec
         (motive_1 := fun phases {world _ _ _ _ _} plan before source after _ =>
           ∀ next (larger : world ⊆ next), Expression outward actions phases (source.world_weaken larger) after)
         (motive_2 := fun phases {world _ _ _ _ _ _ _ _} before outside source after nextOutside _ =>
           ∀ next (larger : world ⊆ next), RetainedChange outward actions phases (source.world_weaken larger) after nextOutside)
         (t := changed))
  all_goals intros
  all_goals first
    | exact .same
    | (rename_i supplied next larger; exact .operations supplied)
    | (rename_i footprint supplied next larger; exact .reinterface footprint supplied)
    | (rename_i supplied next larger; exact .capability supplied)
    | (rename_i cut guarded denied next larger; exact .nonDisposing cut guarded denied)
    | (rename_i nextCut guarded bounded closing ih next larger
       exact .selected nextCut guarded (fun disposes => (bounded disposes).world_weaken larger)
         (fun disposes => ih disposes next larger))
    | (rename_i intercepted callbacks declared covered normal guarded bounded next larger
       exact .freshInterfaces intercepted callbacks (declared.world_weaken larger) covered normal guarded
         (fun disposes => (bounded disposes).world_weaken larger))
    | (rename_i intercepted normal original guarded bounded closing ih next larger
       exact .freshRich intercepted (normal.world_weaken larger)
         (fun disposes => normal.world_weaken_valid larger (original disposes))
         guarded (fun disposes => (bounded disposes).world_weaken larger) (fun disposes => ih disposes next larger))
    | (rename_i nextCut inside before tail ihInside ihBefore ihTail next larger
       exact .resume nextCut (ihInside next larger) (ihBefore next larger) (ihTail next larger))
    | (rename_i nextCut closing before tail ihClosing ihBefore ihTail next larger
       exact .dispose nextCut (ihClosing next larger) (ihBefore next larger) (ihTail next larger))
    | (rename_i first second ihFirst ihSecond next larger
       exact .sequence (ihFirst next larger) (ihSecond next larger))
    | (rename_i first second ihFirst ihSecond next larger
       exact .choice (ihFirst next larger) (ihSecond next larger))
    | (rename_i declared bounds supplied body ih next larger; exact .handler supplied (ih next larger))
    | (rename_i body completion ihBody ihCompletion next larger
       exact .cleanup (ihBody next larger) (ihCompletion next larger))
    | (rename_i body ih next larger
       exact .resource (fun identity fresh => ih identity (fun member => fresh (larger member)) _
         (ScopedExpressions.append_subset larger (List.Subset.refl _))))
    | (rename_i interfaces supplied next larger
       exact .operations (interfaces.world_weaken larger)
         (by simpa only [SourceScheduledRetainedInterfaces.Interfaces.check_world_weaken] using supplied))
    | (rename_i source ready previous inserted ih next larger
       exact .provide (source.world_weaken_valid larger ready) (ih next larger) inserted)
    | (rename_i code tail ihCode ihTail next larger
       exact .plain (ihCode next larger) (ihTail next larger))
    | (rename_i supplied tail ih next larger; exact .handler supplied (ih next larger))
    | (rename_i tail ih next larger; exact .cell (ih next larger))
    | (rename_i completion tail ihCompletion ihTail next larger
       exact .cleanup (ihCompletion next larger) (ihTail next larger))
    | (rename_i tail ih next larger; exact .running (ih next larger))
    | (rename_i saved tail ihSaved ihTail next larger; exact .live (ihSaved next larger) (ihTail next larger))
    | (rename_i tail ih next larger; exact .spent (ih next larger))
    | (rename_i before outside source supplied next larger; exact .install supplied)
    | (rename_i source required footprint declared supplied next larger
       exact .installCleanup required footprint (declared.world_weaken larger) supplied)
    | (rename_i tail ih next larger; exact .dropPlain (ih next larger))
    | (rename_i tail ih next larger; exact .dropHandler (ih next larger))
    | (rename_i tail ih next larger; exact .dropSpent (ih next larger))
    | (rename_i tail ih next larger; exact .protect (ih next larger))
    | (rename_i saved tail ihSaved ihTail next larger; exact .closeLive (ihSaved next larger) (ihTail next larger))

theorem Expression.world_weaken
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints} {source : Code world plan before}
    (changed : Expression outward actions phases source after) (larger : world ⊆ next) :
    Expression outward actions phases (source.world_weaken larger) after :=
  (weaken_rechecking_world outward actions).1 _ _ _ _ _ _ changed next larger

theorem RetainedChange.world_weaken
    {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
    {afterHints : Hints afterScope} {nextOutsideHints : Hints nextOutsideScope}
    {before : Forest beforeHints} {outside : Forest outsideHints}
    {after : Forest afterHints} {nextOutside : Forest nextOutsideHints} {source : Retained world before outside}
    (changed : RetainedChange outward actions phases source after nextOutside) (larger : world ⊆ next) :
    RetainedChange outward actions phases (source.world_weaken larger) after nextOutside :=
  (weaken_rechecking_world outward actions).2 _ _ _ _ _ _ _ changed next larger

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledCallbackInterfaces.Declared.world_weaken
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.weaken_rechecking_world
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.world_weaken
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RetainedChange.world_weaken
