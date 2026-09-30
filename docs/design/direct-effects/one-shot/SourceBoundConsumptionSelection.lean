import SourceBoundDisposalRecords
import SourceScheduledCallerDecomposition

/-! Authenticate the source-snapshot consumption cut by the existing owner
lookup and unique live-owner inventory. This connects a structural source cut
to the exact resumption/disposal snapshot chosen by execution. -/
namespace Ash.OneShot.SourceScheduledNeutral
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Deterministic owner lookup and forest append injectivity identify every
part of a source cut, without another induction over stack frames. -/
theorem OwnerCut.parts_unique
    {wholeHints : Hints wholeScope} {whole : Forest wholeHints}
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    {nextFrontHints : Hints nextFrontScope} {nextSavedHints : Hints nextSavedScope} {nextTailHints : Hints nextTailScope}
    {nextFront : Forest nextFrontHints} {nextSaved : Forest nextSavedHints} {nextTail : Forest nextTailHints}
    (first : OwnerCut owner whole front saved tail) (second : OwnerCut owner whole nextFront nextSaved nextTail) :
    frontScope = nextFrontScope ∧ savedScope = nextSavedScope ∧ tailScope = nextTailScope ∧
    HEq frontHints nextFrontHints ∧ HEq savedHints nextSavedHints ∧ HEq tailHints nextTailHints ∧
    HEq front nextFront ∧ HEq saved nextSaved ∧ HEq tail nextTail := by
  have selected := Option.some.inj (first.found.symm.trans second.found)
  have frontSame := congrArg (fun selection : SourceContextualInvocationHints.Selection => selection.scopes.front) selected
  have savedSame := congrArg (fun selection : SourceContextualInvocationHints.Selection => selection.scopes.captured) selected
  have tailSame := congrArg (fun selection : SourceContextualInvocationHints.Selection => selection.scopes.tail) selected
  cases frontSame
  cases savedSame
  cases tailSame
  injection selected with sameScopes sameFront sameSaved sameTail
  cases sameFront
  cases sameSaved
  cases sameTail
  obtain ⟨sameFront, sameRest⟩ := Forest.append_injective (eq_of_heq (first.forest.symm.trans second.forest))
  cases sameFront
  injection sameRest with _ _ _ _ _ sameSaved sameTail
  cases sameSaved
  cases sameTail
  exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end Ash.OneShot.SourceScheduledNeutral

#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.parts_unique

namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledNeutral (OwnerCut)
open SourceDependencyOwners (owners)

/-- No repeated owner can hide an earlier copy in the consumed caller prefix. -/
private theorem selected_absent
    (unique : (owners (frontScope.append (.live owner savedScope tailScope))).Nodup) :
    owner ∉ owners frontScope := by
  rw [SourceScheduledPhaseRestriction.owners_append] at unique
  exact fun member => (List.nodup_append.mp unique).2.2 owner member owner (by simp [owners]) rfl

/-- Eliminate a source-record cut at the original snapshot data. The motive
may observe any recomposition of those exact data, including closing. -/
theorem Retained.cut_cases
    {actualFrontHints : Hints actualFrontScope} {actualSavedHints : Hints actualSavedScope}
    {actualTailHints : Hints actualTailScope}
    {actualFront : Forest actualFrontHints} {actualSaved : Forest actualSavedHints} {actualTail : Forest actualTailHints}
    (unique : (owners (actualFrontScope.append (.live owner actualSavedScope actualTailScope))).Nodup)
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner (actualFront.append (.live (owner := owner) actualSaved actualTail)) front saved tail)
    (actualCaller : Retained world actualFront) (actualCaptured : Retained world actualSaved) (actualWaiting : Retained world actualTail)
    (caller : Retained world front) (captured : Retained world saved) (waiting : Retained world tail)
    (aligned : HEq (actualCaller.append (.live (owner := owner) actualCaptured actualWaiting))
      (caller.append (.live (owner := owner) captured waiting)))
    (motive : ∀ {frontScope savedScope tailScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {tailHints : Hints tailScope}
      {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints},
      Retained world front → Retained world saved → Retained world tail → Prop)
    (known : motive actualCaller actualCaptured actualWaiting) : motive caller captured waiting := by
  have actualCut : OwnerCut owner (actualFront.append (.live (owner := owner) actualSaved actualTail))
      actualFront actualSaved actualTail :=
    (SourceScheduledRecomposition.predicate_congr
      (SourceDependencyProjection.scope_append_nil actualFrontScope)
      (SourcePlannedRecomposition.hints_append_nil actualFrontHints)
      (SourceScheduledRecomposition.forest_append_nil actualFront)
      (fun caller => OwnerCut owner (actualFront.append (.live (owner := owner) actualSaved actualTail))
        caller actualSaved actualTail)).mp
      ((OwnerCut.hit (owner := owner) (saved := actualSaved) (tail := actualTail)).prefix_without_owner
        actualFront (selected_absent unique))
  obtain ⟨sameFrontScope, sameSavedScope, sameTailScope, sameFrontHints, sameSavedHints, sameTailHints,
    sameFront, sameSaved, sameTail⟩ := cut.parts_unique actualCut
  cases sameFrontScope
  cases sameSavedScope
  cases sameTailScope
  cases sameFrontHints
  cases sameSavedHints
  cases sameTailHints
  cases sameFront
  cases sameSaved
  cases sameTail
  have same := congrArg (Retained.splitAt actualFront (.live (owner := owner) actualSaved actualTail)) (eq_of_heq aligned)
  simp only [Retained.splitAt_join, Prod.mk.injEq] at same
  cases same.1
  have remaining := same.2
  cases remaining
  exact known

/-- Identify the actual resumption snapshot with the source record's exact
cut and metadata. Only uniqueness and equality of original data are required. -/
theorem Resumed.at_cut {before after : Snapshot world}
    (step : Resumed owner before after) (unique : (owners before.scope).Nodup)
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner before.forest front saved tail)
    (caller : Retained world front) (captured : Retained world saved) (waiting : Retained world tail)
    (aligned : HEq before.pending (caller.append (.live (owner := owner) captured waiting))) :
    after = Snapshot.value (captured.append (caller.append (.spent (owner := owner) waiting))) := by
  cases step with
  | cut current actualCaller actualCaptured actualWaiting =>
    exact Retained.cut_cases unique cut actualCaller actualCaptured actualWaiting caller captured waiting aligned
      (fun caller captured waiting =>
        Snapshot.value (actualCaptured.append (actualCaller.append (.spent (owner := owner) actualWaiting))) =
          Snapshot.value (captured.append (caller.append (.spent (owner := owner) waiting)))) rfl

/-- Identify the actual disposal snapshot with the source record's exact
cut and metadata. Only uniqueness and equality of original data are required. -/
theorem Discarded.at_cut {before after : Snapshot world}
    (step : Discarded owner before after) (unique : (owners before.scope).Nodup)
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner before.forest front saved tail)
    (caller : Retained world front) (captured : Retained world saved) (waiting : Retained world tail)
    (aligned : HEq before.pending (caller.append (.live (owner := owner) captured waiting))) :
    after = Snapshot.value (captured.forClosing.append (.running (caller.append (.spent (owner := owner) waiting)))) := by
  cases step with
  | cut current actualCaller actualCaptured actualWaiting =>
    exact Retained.cut_cases unique cut actualCaller actualCaptured actualWaiting caller captured waiting aligned
      (fun caller captured waiting =>
        Snapshot.value (actualCaptured.forClosing.append (.running (actualCaller.append (.spent (owner := owner) actualWaiting)))) =
          Snapshot.value (captured.forClosing.append (.running (caller.append (.spent (owner := owner) waiting))))) rfl

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Resumed.at_cut

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.cut_cases
#print axioms Ash.OneShot.SourceBoundSnapshots.Discarded.at_cut
