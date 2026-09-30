import SourceDeclarationPlans
import SourceContextualInvocationHints

/-! Retained source plans and their structural operations, available before
clause recipes and source checkers. Existing public names are preserved so
later capture, scheduling and ownership proofs use the same data. -/
namespace Ash.OneShot.SourceRetainedPlans
open SourceContextualHints (Hints)
open SourceDeclarationPlans (Plan)
open SourceContextualInvocationHints (forClosing)

inductive Forest : {scope : SourceDependencyCapture.Scope} → Hints scope → Type where
  | nil : Forest .nil
  | plain (plan : Plan dependencies) : Forest rest → Forest (.plain (dependencies := dependencies) rest)
  | handler : Forest rest → Forest (.handler (effect := effect) (table := table) (families := families) required rest)
  | cell : Forest rest → Forest (.cell (identity := identity) rest)
  | cleanup (plan : Plan dependencies) : Forest rest → Forest (.cleanup (needs := needs) (callback := dependencies) rest)
  | running : Forest rest → Forest (.running rest)
  | live : Forest saved → Forest rest → Forest (.live (owner := owner) saved rest)
  | spent : Forest rest → Forest (.spent (owner := owner) rest)

def Forest.append (first : Forest front) (second : Forest tail) : Forest (front.append tail) :=
  match first with
  | .nil => second
  | .plain plan rest => .plain plan (rest.append second)
  | .handler rest => .handler (rest.append second)
  | .cell rest => .cell (rest.append second)
  | .cleanup plan rest => .cleanup plan (rest.append second)
  | .running rest => .running (rest.append second)
  | .live saved rest => .live saved (rest.append second)
  | .spent rest => .spent (rest.append second)

def Forest.forClosing (source : Forest hints) : Forest (forClosing hints) :=
  match source with
  | .nil => .nil
  | .plain _ rest => rest.forClosing
  | .handler rest => rest.forClosing
  | .cell rest => .cell rest.forClosing
  | .cleanup plan rest => .cleanup plan rest.forClosing
  | .running rest => .running rest.forClosing
  | .live saved rest => saved.forClosing.append (.running rest.forClosing)
  | .spent rest => rest.forClosing

/-- Fixed annotated scopes determine the retained pieces uniquely, including
all callback plans. Equal dependency indices alone are not used. -/
theorem Forest.append_injective {front : Hints captured} {tail : Hints outside}
    {first second : Forest front} {rest other : Forest tail}
    (same : first.append rest = second.append other) : first = second ∧ rest = other := by
  induction first with
  | nil => cases second; exact ⟨rfl, same⟩
  | plain plan suffix ih => cases second with
    | plain otherPlan otherSuffix =>
        obtain ⟨rfl, next⟩ := Forest.plain.inj same
        obtain ⟨rfl, rfl⟩ := ih next
        exact ⟨rfl, rfl⟩
  | handler suffix ih => cases second with
    | handler otherSuffix => obtain ⟨rfl, rfl⟩ := ih (Forest.handler.inj same); exact ⟨rfl, rfl⟩
  | cell suffix ih => cases second with
    | cell otherSuffix => obtain ⟨rfl, rfl⟩ := ih (Forest.cell.inj same); exact ⟨rfl, rfl⟩
  | cleanup plan suffix ih => cases second with
    | cleanup otherPlan otherSuffix =>
        obtain ⟨rfl, next⟩ := Forest.cleanup.inj same
        obtain ⟨rfl, rfl⟩ := ih next
        exact ⟨rfl, rfl⟩
  | running suffix ih => cases second with
    | running otherSuffix => obtain ⟨rfl, rfl⟩ := ih (Forest.running.inj same); exact ⟨rfl, rfl⟩
  | live saved suffix ihSaved ih => cases second with
    | live otherSaved otherSuffix =>
        obtain ⟨rfl, next⟩ := Forest.live.inj same
        obtain ⟨rfl, rfl⟩ := ih next
        exact ⟨rfl, rfl⟩
  | spent suffix ih => cases second with
    | spent otherSuffix => obtain ⟨rfl, rfl⟩ := ih (Forest.spent.inj same); exact ⟨rfl, rfl⟩

end Ash.OneShot.SourceRetainedPlans

#print axioms Ash.OneShot.SourceRetainedPlans.Forest.append_injective
