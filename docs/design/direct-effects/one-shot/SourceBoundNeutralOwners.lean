import SourceBoundNeutralExpansion
import SourceBoundConsumptionSelection

/-! Decompose actual neutral metadata at a selected owner. Original saved
annotations remain exact; caller and waiting metadata move structurally. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledNeutral (OwnerCut)

/-- Prefixing equal value snapshots keeps their exact retained data equal. -/
theorem Snapshot.value_prefix
    {first : Retained world before} {second : Retained world after}
    (leadingBounds : Retained world leading) (same : Snapshot.value first = Snapshot.value second) :
    Snapshot.value (leadingBounds.append first) = Snapshot.value (leadingBounds.append second) :=
  congrArg (fun snapshot : Snapshot world => Snapshot.value (leadingBounds.append snapshot.pending)) same

/-- The original owner-cut equations and existing metadata split expose the
actual values at the cut. No source annotation is generated here. -/
theorem Retained.owner_parts
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail) (source : Retained world whole) :
    ∃ caller : Retained world front, ∃ captured : Retained world saved, ∃ waiting : Retained world tail,
      Snapshot.value source = Snapshot.value (caller.append (.live (owner := owner) captured waiting)) := by
  apply (SourceScheduledRecomposition.predicate_congr
    (SourceContextualInvocationHints.selected_cut cut.found).reconstruct cut.hints cut.forest
    (fun forest => ∀ source : Retained world forest,
      ∃ caller : Retained world front, ∃ captured : Retained world saved, ∃ waiting : Retained world tail,
        Snapshot.value source = Snapshot.value (caller.append (.live (owner := owner) captured waiting)))).mpr ?_ source
  intro source
  have reconstruct := source.splitAt_append front (.live (owner := owner) saved tail)
  generalize piecesKnown : source.splitAt front (.live (owner := owner) saved tail) = pieces at *
  rcases pieces with ⟨caller, remaining⟩
  cases remaining with
  | live captured waiting => exact ⟨caller, captured, waiting, congrArg Snapshot.value reconstruct.symm⟩

/-- Neutral movement can be prefixed by unchanged original metadata. -/
theorem Retained.Neutral.prefix
    {first : Retained world before} {second : Retained world after}
    (leadingBounds : Retained world leading) (changed : Neutral world first second) :
    Neutral world (leadingBounds.append first) (leadingBounds.append second) := by
  induction leadingBounds with
  | nil => exact changed
  | plain code rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup code rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ih => exact .live ih
  | spent rest ih => exact .spent ih

theorem Retained.Neutral.append
    {first : Retained world before} {second : Retained world after}
    (changed : Neutral world first second)
    {tail : Retained world waiting} {nextTail : Retained world nextWaiting}
    (outside : Neutral world tail nextTail) :
    Neutral world (first.append tail) (second.append nextTail) := by
  induction changed with
  | refl => exact outside.prefix _
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

/-- The saved bound tree is identical on both sides. Existing cut traversal
chooses the owner; this induction adds only the data correspondence. -/
theorem Retained.Neutral.owner_parts
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {first : Retained world before} {last : Retained world after}
    (changed : Neutral world first last)
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner before front saved tail) :
    ∃ caller : Retained world front, ∃ captured : Retained world saved, ∃ waiting : Retained world tail,
      Snapshot.value first = Snapshot.value (caller.append (.live (owner := owner) captured waiting)) ∧
    ∃ nextFrontScope nextTailScope, ∃ nextFrontHints : Hints nextFrontScope, ∃ nextTailHints : Hints nextTailScope,
    ∃ nextFront : Forest nextFrontHints, ∃ nextTail : Forest nextTailHints,
    ∃ nextCaller : Retained world nextFront, ∃ nextWaiting : Retained world nextTail,
      OwnerCut owner after nextFront saved nextTail ∧
      Snapshot.value last = Snapshot.value (nextCaller.append (.live (owner := owner) captured nextWaiting)) ∧
      Neutral world caller nextCaller ∧ Neutral world waiting nextWaiting := by
  induction changed generalizing frontScope tailScope with
  | refl =>
      obtain ⟨caller, captured, waiting, same⟩ := Retained.owner_parts cut _
      exact ⟨caller, captured, waiting, same, _, _, _, _, _, _, caller, waiting, cut, same, .refl, .refl⟩
  | extra changed ih =>
      obtain ⟨caller, captured, waiting, same, _, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextSame, callerMove, tailMove⟩ := ih cut
      exact ⟨caller, captured, waiting, same, _, _, _, _, _, _, .plain .absent nextCaller, nextWaiting,
        .plain nextCut, Snapshot.value_prefix (.plain (.absent (plan := .pure)) .nil) nextSame, .extra callerMove, tailMove⟩
  | completion changed ih =>
      obtain ⟨caller, captured, waiting, same, _, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextSame, callerMove, tailMove⟩ := ih cut
      exact ⟨caller, captured, waiting, same, _, _, _, _, _, _, .cleanup .absent nextCaller, nextWaiting,
        .cleanup nextCut, Snapshot.value_prefix (.cleanup (needs := []) (.absent (plan := .pure)) .nil) nextSame, .completion callerMove, tailMove⟩
  | history changed ih =>
      obtain ⟨caller, captured, waiting, same, _, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextSame, callerMove, tailMove⟩ := ih cut
      exact ⟨caller, captured, waiting, same, _, _, _, _, _, _, .spent nextCaller, nextWaiting,
        .spent nextCut, Snapshot.value_prefix (.spent .nil) nextSame, .history callerMove, tailMove⟩
  | plain changed ih =>
    rename_i code
    cases cut with
    | plain next =>
      obtain ⟨caller, captured, waiting, same, _, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextSame, callerMove, tailMove⟩ := ih next
      exact ⟨.plain code caller, captured, waiting, Snapshot.value_prefix (.plain code .nil) same,
        _, _, _, _, _, _, .plain code nextCaller, nextWaiting,
        .plain nextCut, Snapshot.value_prefix (.plain code .nil) nextSame, .plain callerMove, tailMove⟩
  | handler changed ih =>
    rename_i effect table families required
    cases cut with
    | handler next =>
      obtain ⟨caller, captured, waiting, same, _, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextSame, callerMove, tailMove⟩ := ih next
      exact ⟨.handler caller, captured, waiting, Snapshot.value_prefix (.handler (effect := effect) (table := table) (families := families) (required := required) .nil) same,
        _, _, _, _, _, _, .handler nextCaller, nextWaiting,
        .handler nextCut, Snapshot.value_prefix (.handler (effect := effect) (table := table) (families := families) (required := required) .nil) nextSame, .handler callerMove, tailMove⟩
  | cell changed ih => cases cut with
    | cell next =>
      obtain ⟨caller, captured, waiting, same, _, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextSame, callerMove, tailMove⟩ := ih next
      exact ⟨.cell caller, captured, waiting, Snapshot.value_prefix (.cell .nil) same,
        _, _, _, _, _, _, .cell nextCaller, nextWaiting,
        .cell nextCut, Snapshot.value_prefix (.cell .nil) nextSame, .cell callerMove, tailMove⟩
  | cleanup changed ih =>
    rename_i needs dependencies callback code
    cases cut with
    | cleanup next =>
      obtain ⟨caller, captured, waiting, same, _, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextSame, callerMove, tailMove⟩ := ih next
      exact ⟨.cleanup (needs := needs) code caller, captured, waiting, Snapshot.value_prefix (.cleanup (needs := needs) code .nil) same,
        _, _, _, _, _, _, .cleanup (needs := needs) code nextCaller, nextWaiting,
        .cleanup nextCut, Snapshot.value_prefix (.cleanup (needs := needs) code .nil) nextSame, .cleanup callerMove, tailMove⟩
  | running changed ih => cases cut with
    | running next =>
      obtain ⟨caller, captured, waiting, same, _, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextSame, callerMove, tailMove⟩ := ih next
      exact ⟨.running caller, captured, waiting, Snapshot.value_prefix (.running .nil) same,
        _, _, _, _, _, _, .running nextCaller, nextWaiting,
        .running nextCut, Snapshot.value_prefix (.running .nil) nextSame, .running callerMove, tailMove⟩
  | live changed ih =>
    rename_i other dormantScope dormantHints dormantForest dormant
    cases cut with
    | hit => exact ⟨.nil, _, _, rfl, _, _, _, _, _, _, .nil, _, .hit, rfl, .refl, changed⟩
    | live different next =>
      obtain ⟨caller, captured, waiting, same, _, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextSame, callerMove, tailMove⟩ := ih next
      exact ⟨.live (owner := other) dormant caller, captured, waiting, Snapshot.value_prefix (.live (owner := other) dormant .nil) same,
        _, _, _, _, _, _, .live (owner := other) dormant nextCaller, nextWaiting,
        .live different nextCut, Snapshot.value_prefix (.live (owner := other) dormant .nil) nextSame, .live callerMove, tailMove⟩
  | spent changed ih => cases cut with
    | spent next =>
      obtain ⟨caller, captured, waiting, same, _, _, _, _, _, _, nextCaller, nextWaiting, nextCut, nextSame, callerMove, tailMove⟩ := ih next
      exact ⟨.spent caller, captured, waiting, Snapshot.value_prefix (.spent .nil) same,
        _, _, _, _, _, _, .spent nextCaller, nextWaiting,
        .spent nextCut, Snapshot.value_prefix (.spent .nil) nextSame, .spent callerMove, tailMove⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.value_prefix
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.owner_parts
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Neutral.prefix
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Neutral.append
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Neutral.owner_parts
