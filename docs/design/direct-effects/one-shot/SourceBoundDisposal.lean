import SourceBoundResumption

/-! Disposal retains the original callback annotations while materializing the
saved forest's closing traversal. Caller annotations survive unchanged. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

def Retained.forClosing {forest : Forest hints} (source : Retained world forest) :
    Retained world forest.forClosing :=
  match source with
  | .nil => .nil
  | .plain _ rest => rest.forClosing
  | .handler rest => rest.forClosing
  | .cell rest => .cell rest.forClosing
  | .cleanup code rest => .cleanup code rest.forClosing
  | .running rest => .running rest.forClosing
  | .live saved rest => saved.forClosing.append (.running rest.forClosing)
  | .spent rest => rest.forClosing

inductive DiscardForest (owner : Nat) : {beforeScope afterScope : SourceDependencyCapture.Scope} →
    {beforeHints : Hints beforeScope} → {afterHints : Hints afterScope} →
    Forest beforeHints → Forest afterHints → Prop where
  | cut (front : Forest frontHints) (saved : Forest savedHints) (tail : Forest tailHints) :
      DiscardForest owner (front.append (.live (owner := owner) saved tail))
        (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail))))

inductive Discarded (owner : Nat) : Snapshot world → Snapshot world → Prop where
  | cut {plan : SourceDeclarationPlans.Plan dependencies}
      {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
      (current : SourcePlanBounds.Annotation world plan)
      (before : Retained world front) (captured : Retained world saved) (after : Retained world tail) :
      Discarded owner ⟨_, plan, current, _, _, _, before.append (.live (owner := owner) captured after)⟩
        (Snapshot.value (captured.forClosing.append (.running (before.append (.spent (owner := owner) after)))))

theorem DiscardForest.snapshot {before : Snapshot world} {after : Forest afterHints}
    (shape : DiscardForest owner before.forest after) :
    ∃ pending : Retained world after, Discarded owner before (Snapshot.value pending) := by
  rcases before with ⟨_, plan, current, _, _, forest, retained⟩
  cases shape with
  | cut front saved tail =>
    have reconstruct := retained.splitAt_append front (.live (owner := owner) saved tail)
    generalize piecesKnown : retained.splitAt front (.live (owner := owner) saved tail) = pieces at *
    rcases pieces with ⟨first, remaining⟩
    cases remaining with
    | live captured last =>
      cases reconstruct
      exact ⟨_, .cut current first captured last⟩

section
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem Retained.Admitted.forClosing {forest : Forest hints} {source : Retained world forest}
    (admitted : source.Admitted) : source.forClosing.Admitted := by
  induction admitted with
  | nil => exact .nil
  | plain code rest ih => exact ih
  | handler rest ih => exact ih
  | cell rest ih => exact .cell ih
  | cleanup code rest ih => exact .cleanup code ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ih => exact ihSaved.append (.running ih)
  | spent rest ih => exact ih

theorem Discarded.admitted {before after : Snapshot world}
    (step : Discarded owner before after) (admitted : before.Admitted) : after.Admitted := by
  cases step with
  | cut current first captured last =>
    obtain ⟨before, remaining⟩ := admitted.2.of_append
    cases remaining with
    | live saved tail =>
      exact Snapshot.value_admitted (saved.forClosing.append (.running (before.append (.spent tail))))

end
end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.DiscardForest.snapshot
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Admitted.forClosing
#print axioms Ash.OneShot.SourceBoundSnapshots.Discarded.admitted
