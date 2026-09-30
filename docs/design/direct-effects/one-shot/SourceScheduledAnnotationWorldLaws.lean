import SourceScheduledAnnotationWorld
import SourceBoundDisposal

/-! Composition and bound-data preservation for structural annotation world
extension. These laws make repeated allocation independent of proof witnesses. -/
namespace Ash.OneShot.SourceBoundSnapshots

theorem Retained.absent_world_weaken (forest : SourceRetainedPlans.Forest hints) (larger : world ⊆ next) :
    (Retained.absent forest (world := world)).world_weaken larger = Retained.absent forest := by
  induction forest <;> simp_all only [Retained.absent, Retained.world_weaken, SourcePlanBounds.Annotation.world_weaken]

/-- World extension commutes with ordered snapshot recomposition. -/
theorem Retained.world_weaken_append (first : Retained world firstForest) (second : Retained world secondForest)
    (larger : world ⊆ next) :
    (first.append second).world_weaken larger = (first.world_weaken larger).append (second.world_weaken larger) := by
  induction first <;> simp_all only [Retained.append, Retained.world_weaken,
    SourceRetainedPlans.Forest.append, SourceContextualHints.Hints.append, SourceDependencyCapture.Scope.append]

/-- Resource entry does not change the canonical closing projection. -/
theorem Retained.forClosing_world_weaken (source : Retained world forest) (larger : world ⊆ next) :
    (source.world_weaken larger).forClosing = source.forClosing.world_weaken larger := by
  induction source <;> simp_all only [Retained.forClosing, Retained.world_weaken, Retained.world_weaken_append,
    SourceRetainedPlans.Forest.forClosing, SourceContextualInvocationHints.forClosing, SourceDependencyCapture.Scope.forClosing]

end Ash.OneShot.SourceBoundSnapshots

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)

variable [DeclarationPolicy]

theorem annotation_world_composition :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (annotation : Code world plan forest) middle next (first : world ⊆ middle) (second : middle ⊆ next),
      (annotation.world_weaken first).world_weaken second = annotation.world_weaken (first.trans second)) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (annotation : Retained world forest outside)
      middle next (first : world ⊆ middle) (second : middle ⊆ next),
      (annotation.world_weaken first).world_weaken second = annotation.world_weaken (first.trans second)) := by
  constructor
  all_goals first
    | (intro world dependencies scope hints plan forest annotation
       apply Code.rec
         (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
           ∀ middle next (first : world ⊆ middle) (second : middle ⊆ next),
             (annotation.world_weaken first).world_weaken second = annotation.world_weaken (first.trans second))
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
           ∀ middle next (first : world ⊆ middle) (second : middle ⊆ next),
             (annotation.world_weaken first).world_weaken second = annotation.world_weaken (first.trans second))
         (t := annotation))
    | (intro world scope outsideScope hints outsideHints forest outside annotation
       apply Retained.rec
         (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
           ∀ middle next (first : world ⊆ middle) (second : middle ⊆ next),
             (annotation.world_weaken first).world_weaken second = annotation.world_weaken (first.trans second))
         (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
           ∀ middle next (first : world ⊆ middle) (second : middle ⊆ next),
             (annotation.world_weaken first).world_weaken second = annotation.world_weaken (first.trans second))
         (t := annotation))
  all_goals intros
  all_goals simp_all only [Code.world_weaken, Retained.world_weaken,
    SourceScheduledRetainedInterfaces.Interfaces.world_weaken_trans]

theorem Code.world_weaken_trans {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    (annotation : Code world plan forest) (first : world ⊆ middle) (second : middle ⊆ next) :
    (annotation.world_weaken first).world_weaken second = annotation.world_weaken (first.trans second) :=
  annotation_world_composition.1 _ _ _ annotation _ _ first second

theorem Retained.world_weaken_trans {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (first : world ⊆ middle) (second : middle ⊆ next) :
    (annotation.world_weaken first).world_weaken second = annotation.world_weaken (first.trans second) :=
  annotation_world_composition.2 _ _ _ annotation _ _ first second

/-- The exact current-plan bounds commute with world extension, including
fresh-resource families. Original handler bounds are neither omitted nor replaced. -/
theorem Code.ofCode_world_weaken {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    (annotation : Code world plan forest) (larger : world ⊆ next) :
    SourcePlanBounds.ofCode (annotation.world_weaken larger) =
      (SourcePlanBounds.ofCode annotation).world_weaken larger := by
  revert next
  apply Code.rec
    (motive_1 := fun world {dependencies scope hints} plan forest annotation =>
      ∀ next (larger : world ⊆ next), SourcePlanBounds.ofCode (annotation.world_weaken larger) =
        (SourcePlanBounds.ofCode annotation).world_weaken larger)
    (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation => True)
    (t := annotation)
  all_goals intros
  all_goals simp_all only [Code.world_weaken, SourcePlanBounds.ofCode, SourcePlanBounds.Annotation.world_weaken]

/-- Exact retained snapshot projection commutes with resource-world extension. -/
theorem Retained.ofCapability_world_weaken {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (larger : world ⊆ next) :
    SourceBoundSnapshots.Retained.ofCapability (annotation.world_weaken larger) =
      (SourceBoundSnapshots.Retained.ofCapability annotation).world_weaken larger := by
  revert next
  apply Retained.rec
    (motive_1 := fun _ {_ _ _} _ _ _ => True)
    (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside annotation =>
      ∀ next (larger : world ⊆ next), SourceBoundSnapshots.Retained.ofCapability (annotation.world_weaken larger) =
        (SourceBoundSnapshots.Retained.ofCapability annotation).world_weaken larger)
    (t := annotation)
  all_goals intros
  all_goals first
    | trivial
    | simp_all only [Retained.world_weaken, SourceBoundSnapshots.Retained.ofCapability,
        SourceBoundSnapshots.Retained.world_weaken, Code.ofCode_world_weaken,
        SourceBoundSnapshots.Retained.absent_world_weaken]

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.annotation_world_composition
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.world_weaken_trans
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.world_weaken_trans
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.ofCode_world_weaken

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.absent_world_weaken
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.world_weaken_append
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.forClosing_world_weaken
