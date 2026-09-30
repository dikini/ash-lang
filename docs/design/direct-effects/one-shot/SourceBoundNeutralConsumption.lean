import SourceBoundNeutralOwners

/-! Neutral metadata correspondence commutes with the actual resumption and
disposal snapshot relations. The existing unique-owner cut theorem identifies
the runtime successor; no typing or scheduling premise is added. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledNeutral (OwnerCut)
open SourceDependencyOwners (owners)

theorem Snapshot.pending_heq {first second : Snapshot world} (same : first = second) :
    HEq first.pending second.pending := by
  cases same
  rfl

/-- Authenticate the original components by splitting the same bound tree at
the same forest boundary. The moved components are then the actual data. -/
theorem Retained.Neutral.owner_parts_at
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner (front.append (.live (owner := owner) saved tail)) front saved tail)
    (caller : Retained world front) (captured : Retained world saved) (waiting : Retained world tail)
    {afterHints : Hints afterScope} {after : Forest afterHints} {last : Retained world after}
    (changed : Neutral world (caller.append (.live (owner := owner) captured waiting)) last) :
    ∃ nextFrontScope nextTailScope, ∃ nextFrontHints : Hints nextFrontScope, ∃ nextTailHints : Hints nextTailScope,
    ∃ nextFront : Forest nextFrontHints, ∃ nextTail : Forest nextTailHints,
    ∃ nextCaller : Retained world nextFront, ∃ nextWaiting : Retained world nextTail,
      OwnerCut owner after nextFront saved nextTail ∧
      Snapshot.value last = Snapshot.value (nextCaller.append (.live (owner := owner) captured nextWaiting)) ∧
      Neutral world caller nextCaller ∧ Neutral world waiting nextWaiting := by
  obtain ⟨actualCaller, actualCaptured, actualWaiting, origin, _, _, _, _, _, _, nextCaller, nextWaiting,
    nextCut, nextOrigin, callerMove, tailMove⟩ := changed.owner_parts cut
  have aligned := Snapshot.pending_heq origin
  dsimp only [Snapshot.value] at aligned
  have pieces := congrArg (Retained.splitAt front (.live (owner := owner) saved tail)) (eq_of_heq aligned)
  simp only [Retained.splitAt_join, Prod.mk.injEq] at pieces
  rcases pieces with ⟨rfl, remaining⟩
  cases remaining
  exact ⟨_, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextOrigin, callerMove, tailMove⟩

/-- Resumption moves the original saved annotations in front of the changed
caller and waiting tail. Neutral movement supplies their exact provenance. -/
theorem Retained.Neutral.resumed
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner (front.append (.live (owner := owner) saved tail)) front saved tail)
    (caller : Retained world front) (captured : Retained world saved) (waiting : Retained world tail)
    {snapshot next : Snapshot world}
    (changed : Neutral world (caller.append (.live (owner := owner) captured waiting)) snapshot.pending)
    (unique : (owners snapshot.scope).Nodup) (step : Resumed owner snapshot next) :
    Neutral world (captured.append (caller.append (.spent (owner := owner) waiting))) next.pending := by
  obtain ⟨_, _, _, _, _, _, nextCaller, nextWaiting, nextCut, aligned, callerMove, tailMove⟩ :=
    changed.owner_parts_at cut caller captured waiting
  have same := step.at_cut unique nextCut nextCaller captured nextWaiting (Snapshot.pending_heq aligned)
  cases same
  exact (callerMove.append (.spent tailMove)).prefix captured

/-- Disposal retains exactly the original canonical closing bounds and moves
the changed caller/waiting tail below the running completion boundary. -/
theorem Retained.Neutral.discarded
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner (front.append (.live (owner := owner) saved tail)) front saved tail)
    (caller : Retained world front) (captured : Retained world saved) (waiting : Retained world tail)
    {snapshot next : Snapshot world}
    (changed : Neutral world (caller.append (.live (owner := owner) captured waiting)) snapshot.pending)
    (unique : (owners snapshot.scope).Nodup) (step : Discarded owner snapshot next) :
    Neutral world (captured.forClosing.append (.running (caller.append (.spent (owner := owner) waiting)))) next.pending := by
  obtain ⟨_, _, _, _, _, _, nextCaller, nextWaiting, nextCut, aligned, callerMove, tailMove⟩ :=
    changed.owner_parts_at cut caller captured waiting
  have same := step.at_cut unique nextCut nextCaller captured nextWaiting (Snapshot.pending_heq aligned)
  cases same
  exact (Retained.Neutral.running (callerMove.append (.spent tailMove))).prefix captured.forClosing

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.pending_heq
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Neutral.owner_parts_at
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Neutral.resumed
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Neutral.discarded
