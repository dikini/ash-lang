import SourceBoundExits

/-! Allocation selects the original fresh-body annotation and weakens queued
annotations to the extended resource world. Installed handler bounds remain a
separate invariant. -/
namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan)

def Annotation.world_weaken {plan : Plan dependencies} (annotation : Annotation world plan)
    (larger : world ⊆ nextWorld) : Annotation nextWorld plan :=
  match annotation with
  | .absent => .absent
  | .sequence first second => .sequence (first.world_weaken larger) (second.world_weaken larger)
  | .choice first second => .choice (first.world_weaken larger) (second.world_weaken larger)
  | .handler bounds body => .handler bounds (body.world_weaken larger)
  | .cleanup body callback => .cleanup (body.world_weaken larger) (callback.world_weaken larger)
  | .resource body => .resource (fun identity fresh =>
      (body identity (fun member => fresh (larger member))).world_weaken
        (ScopedExpressions.append_subset larger (List.Subset.refl _)))

/-- Resource choices along a lookup path must remain fresh after allocation. -/
def Path.Fresh (world : List Nat) : Path → Prop
  | .here => True
  | .first rest | .second rest | .body rest | .callback rest => rest.Fresh world
  | .resource identity rest => identity ∉ world ∧ rest.Fresh (world ++ [identity])

theorem Annotation.lookup_world_weaken {plan : Plan dependencies}
    (annotation : Annotation world plan) (larger : world ⊆ nextWorld)
    (fresh : path.Fresh nextWorld) :
    (annotation.world_weaken larger).lookup path operation held = annotation.lookup path operation held := by
  induction path generalizing world nextWorld dependencies with
  | here => cases annotation <;> rfl
  | first path ih | second path ih | body path ih | callback path ih =>
      cases annotation <;> first | rfl | exact ih _ _ fresh
  | resource identity path ih =>
      cases annotation <;> first
        | rfl
        | (simp only [Path.Fresh] at fresh
           simp only [Annotation.world_weaken, Annotation.lookup, dif_pos fresh.1,
             dif_pos (show identity ∉ world from fun member => fresh.1 (larger member))]
           exact ih _ _ fresh.2)

def Annotation.resourceBody {dependencies : Nat → SourceDependencyAnnotations.Dependencies}
    {body : (identity : Nat) → Plan (dependencies identity)}
    (annotation : Annotation world (.resource body)) (fresh : identity ∉ world) :
    Annotation (world ++ [identity]) (body identity) :=
  match annotation with
  | .absent => .absent
  | .resource body => body identity fresh

theorem Annotation.resourceBody_lookup {dependencies : Nat → SourceDependencyAnnotations.Dependencies}
    {body : (identity : Nat) → Plan (dependencies identity)}
    (annotation : Annotation world (.resource body)) (fresh : identity ∉ world) :
    (annotation.resourceBody fresh).lookup path operation held =
      annotation.lookup (.resource identity path) operation held := by
  cases annotation <;> simp only [Annotation.resourceBody, Annotation.lookup, dif_pos fresh]

end Ash.OneShot.SourcePlanBounds

namespace Ash.OneShot.SourceBoundSnapshots
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

def Retained.world_weaken {hints : Hints scope} {forest : Forest hints}
    (pending : Retained world forest) (larger : world ⊆ nextWorld) : Retained nextWorld forest :=
  match pending with
  | .nil => .nil
  | .plain code rest => .plain (code.world_weaken larger) (rest.world_weaken larger)
  | .handler rest => .handler (rest.world_weaken larger)
  | .cell rest => .cell (rest.world_weaken larger)
  | .cleanup code rest => .cleanup (code.world_weaken larger) (rest.world_weaken larger)
  | .running rest => .running (rest.world_weaken larger)
  | .live saved rest => .live (saved.world_weaken larger) (rest.world_weaken larger)
  | .spent rest => .spent (rest.world_weaken larger)

inductive EnteredResource (identity : Nat) : Snapshot world → Snapshot (world ++ [identity]) → Prop where
  | step {initial : Plan initialDependencies} {dependencies : Nat → SourceDependencyAnnotations.Dependencies}
    {body : (identity : Nat) → Plan (dependencies identity)}
      {hints : Hints scope} {forest : Forest hints}
      (bounds : Annotation world (.sequence initial (.resource body)))
      (remaining : Retained world forest) (fresh : identity ∉ world) :
      EnteredResource identity ⟨_, _, bounds, _, hints, forest, remaining⟩
        ⟨_, body identity, bounds.second.resourceBody fresh, _, _, .cell (identity := identity) forest,
          .cell (remaining.world_weaken (List.subset_append_left _ _))⟩

theorem EnteredResource.body_lookup {before : Snapshot world} {after : Snapshot (world ++ [identity])}
    (step : EnteredResource identity before after) :
    after.current.lookup path operation held =
      before.current.lookup (.second (.resource identity path)) operation held := by
  cases step
  simp only [SourcePlanBounds.Annotation.resourceBody_lookup, SourcePlanBounds.Annotation.second_lookup]

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourcePlanBounds.Annotation.lookup_world_weaken
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.resourceBody_lookup
#print axioms Ash.OneShot.SourceBoundSnapshots.EnteredResource.body_lookup
