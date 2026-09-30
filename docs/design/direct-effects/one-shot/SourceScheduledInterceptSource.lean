import SourceScheduledStructuralClosing
import SourceScheduledRetainedSplit

/-! Recover the original normal prefix at a newly intercepting handler from
whole retained source. Existing interception and source-splitting proofs supply
its shape, validation and exact snapshot origin. Capture guards, owner bounds
and closing obligations remain separate premises of the fresh-disposer rule. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceScheduledHandlerSelection (Intercept)
open SourceBoundSnapshots.Retained (ofCapability)

/-- Original source evidence at a fresh interception, not a target admission
judgment. The waiting suffix is retained separately in its original order. -/
structure InterceptSource [DeclarationPolicy]
    (outward : List Instance) (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (_intercepted : Intercept effect operation contract modes table families required before after saved waiting)
    (source : Retained world before .nil) where
  prefixScope : Scope
  prefixHints : Hints prefixScope
  front : Forest prefixHints
  passed : SourceHandlerRequirements.reaches effect prefixScope = true
  beforeScopeEq : beforeScope = prefixScope.append waitingScope
  savedScopeEq : savedScope = prefixScope.append (.handler effect table families .nil)
  beforeHintsEq : HEq beforeHints (prefixHints.append waitingHints)
  savedHintsEq : HEq savedHints
    (prefixHints.append (.handler (effect := effect) (table := table) (families := families) required .nil))
  beforeEq : HEq before (front.append waiting)
  savedEq : HEq saved (front.append
    (.handler (effect := effect) (table := table) (families := families) (required := required) .nil))
  normal : Retained world front waiting
  tail : Retained world waiting .nil
  normalReady : normal.Valid outward actions phases
  tailReady : tail.Valid outward actions phases
  original : HEq ((ofCapability normal).append (ofCapability tail)) (ofCapability source)

variable [DeclarationPolicy]

/-- When traversal constructs whole source from its actual children, retain
those children instead of choosing a new split witness. Whole-source validity
supplies both child checks; removing the empty receiver is only index transport. -/
def InterceptSource.recoverJoined
    {frontHints : Hints frontScope} {front : Forest frontHints}
    {afterHints : Hints afterScope} {after : Forest afterHints}
    {waitingHints : Hints waitingScope} {waiting : Forest waitingHints}
    (passed : SourceHandlerRequirements.reaches effect frontScope = true)
    (intercepted : Intercept effect operation contract modes table families required
      (front.append waiting) after
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) .nil)) waiting)
    (normal : Retained world front (waiting.append .nil))
    (tail : Retained world waiting .nil)
    (ready : (normal.joinSource tail).Valid outward actions phases) :
    InterceptSource outward actions phases intercepted (normal.joinSource tail) := by
  let original := SourceScheduledSourceJoin.receiverCast
    (fun receiver => Retained world front receiver)
    (SourceDependencyProjection.scope_append_nil waitingScope)
    (SourcePlannedRecomposition.hints_append_nil waitingHints)
    (SourceScheduledRecomposition.forest_append_nil waiting) normal
  have childChecks := (normal.joinSource_valid tail).mp ready
  have originalReady : original.Valid outward actions phases := by
    have same : original.Valid outward actions phases = normal.Valid outward actions phases :=
      SourceScheduledSourceJoin.receiverCast_observe
      (fun receiver => Retained world front receiver)
      (fun _ source => source.Valid outward actions phases) _ _ _ normal
    exact same.mpr childChecks.1
  have originalBounds : ofCapability original = ofCapability normal :=
    SourceScheduledSourceJoin.receiverCast_observe
      (fun receiver => Retained world front receiver) (fun _ source => ofCapability source) _ _ _ normal
  exact ⟨frontScope, frontHints, front, passed, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    original, tail, originalReady, childChecks.2,
    heq_of_eq ((congrArg (fun part => part.append (ofCapability tail)) originalBounds).trans
      (normal.joinSource_bounds tail).symm)⟩

/-- Recovery from a source join retains the actual original annotation,
including invocation children and resource families, up to receiver equality. -/
theorem InterceptSource.recoverJoined_normal
    {frontHints : Hints frontScope} {front : Forest frontHints}
    {afterHints : Hints afterScope} {after : Forest afterHints}
    {waitingHints : Hints waitingScope} {waiting : Forest waitingHints}
    (passed : SourceHandlerRequirements.reaches effect frontScope = true)
    (intercepted : Intercept effect operation contract modes table families required
      (front.append waiting) after
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) .nil)) waiting)
    (normal : Retained world front (waiting.append .nil))
    (tail : Retained world waiting .nil)
    (ready : (normal.joinSource tail).Valid outward actions phases) :
    HEq (InterceptSource.recoverJoined passed intercepted normal tail ready).normal normal :=
  SourceScheduledSourceJoin.receiverCast_heq (fun receiver => Retained world front receiver) _ _ _ normal

private theorem original_parts
    {frontHints : Hints frontScope} {waitingHints : Hints waitingScope}
    (front : Forest frontHints) (waiting : Forest waitingHints)
    (source : Retained world (front.append waiting) .nil) (ready : source.Valid outward actions phases) :
    ∃ normal : Retained world front waiting, ∃ tail : Retained world waiting .nil,
      normal.Valid outward actions phases ∧ tail.Valid outward actions phases ∧
      (ofCapability normal).append (ofCapability tail) = ofCapability source := by
  obtain ⟨normal, tail, normalReady, tailReady, kept⟩ :=
    SourceScheduledCapabilityAnnotations.retained_split_retaining front waiting source ready
  obtain ⟨normal, normalReady, same⟩ :=
    (SourceScheduledCapabilityAnnotations.retained_receiver_nil_bounds waiting _).mp ⟨normal, normalReady, rfl⟩
  exact ⟨normal, tail, normalReady, tailReady,
    (congrArg (fun part => part.append (ofCapability tail)) same).trans kept⟩

/-- When syntax traversal already knows the insertion prefix, keep that exact
index in the returned record while still recovering its source from the whole. -/
noncomputable def InterceptSource.recoverAt
    {frontHints : Hints frontScope} (front : Forest frontHints)
    {afterHints : Hints afterScope} {after : Forest afterHints}
    {waitingHints : Hints waitingScope} {waiting : Forest waitingHints}
    (passed : SourceHandlerRequirements.reaches effect frontScope = true)
    (intercepted : Intercept effect operation contract modes table families required
      (front.append waiting) after
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) .nil)) waiting)
    (source : Retained world (front.append waiting) .nil) (ready : source.Valid outward actions phases) :
    InterceptSource outward actions phases intercepted source :=
  let parts := original_parts front waiting source ready
  let normal := Classical.choose parts
  let tail := Classical.choose (Classical.choose_spec parts)
  let checked := Classical.choose_spec (Classical.choose_spec parts)
  ⟨frontScope, frontHints, front, passed, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    normal, tail, checked.1, checked.2.1, heq_of_eq checked.2.2⟩

/-- Reuse the existing interception decomposition and source-directed split.
No separate front annotation, target check, or closing proof is supplied. -/
noncomputable def InterceptSource.recover
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (intercepted : Intercept effect operation contract modes table families required before after saved waiting)
    (source : Retained world before .nil) (ready : source.Valid outward actions phases) :
    InterceptSource outward actions phases intercepted source := Classical.choice (by
  obtain ⟨prefixScope, prefixHints, front, passed, beforeScopeEq, savedScopeEq,
    beforeHintsEq, savedHintsEq, beforeEq, savedEq⟩ := intercepted.prefix
  obtain ⟨recomposed, valid, original⟩ :=
    (SourceScheduledRecomposition.predicate_congr beforeScopeEq beforeHintsEq beforeEq
      (fun forest => ∃ annotation : Retained world forest .nil,
        annotation.Valid outward actions phases ∧ HEq (ofCapability annotation) (ofCapability source))).mp
      ⟨source, ready, HEq.rfl⟩
  obtain ⟨normal, tail, normalReady, tailReady, kept⟩ := original_parts front waiting recomposed valid
  exact ⟨⟨prefixScope, prefixHints, front, passed, beforeScopeEq, savedScopeEq,
    beforeHintsEq, savedHintsEq, beforeEq, savedEq, normal, tail, normalReady, tailReady,
    (heq_of_eq kept).trans original⟩⟩)

/-- The fresh-disposer rule now consumes the recovered original front. Its
validity and its precise relation to the whole source are already established;
the recursive closing check remains on that same recovered source. -/
theorem InterceptSource.rechecking
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {intercepted : Intercept effect operation contract modes table families required before after saved waiting}
    {wholeSource : Retained world before .nil}
    (original : InterceptSource outward actions phases intercepted wholeSource)
    {request : Code world (.request (effect := effect) (operation := operation)) before}
    (guarded : SourceDependencyCapture.checkCapture outward afterScope effect operation = true)
    (bounded : contract.dispose = true → SourceDependencyOwners.PendingWithin world
      (SourceDependencyOwners.owners savedScope) savedScope)
    (closing : ∀ _disposes : contract.dispose = true,
      Closing outward actions phases original.normal (.running waiting)) :
    Expression outward actions phases request after := by
  cases original with
  | mk prefixScope prefixHints front passed beforeScopeEq savedScopeEq beforeHintsEq savedHintsEq
      beforeEq savedEq normal tail normalReady tailReady origin =>
    cases beforeScopeEq
    cases savedScopeEq
    cases beforeHintsEq
    cases savedHintsEq
    cases beforeEq
    cases savedEq
    exact .fresh_closing intercepted normal (fun _ => normalReady) guarded bounded closing

/-- A primitive outside capability derives closing for a single request
callback, for either original retained annotation form. It supplies no owner use. -/
theorem Closing.request_callback
    {beforeHints : Hints beforeScope} {before : Forest beforeHints}
    {nextHints : Hints nextScope} {next : Forest nextHints}
    {source : Retained world (.cleanup (needs := needs)
      (.request (effect := effect) (operation := operation)) .nil) before}
    (supplied : SourceContextualClauses.RequestCapability effect operation (.running nextScope)) :
    Closing outward actions phases source next := by
  cases source with
  | operations original =>
      apply Closing.operations (.cleanup .nil [(effect, operation)] .request .request .nil)
      change (SourceContextualHints.checkRequirements (.running nextScope) [(effect, operation)] && true) = true
      rw [Bool.and_true]
      apply SourceContextualRequirements.check_requirements_iff.mpr
      intro request member
      cases List.mem_singleton.mp member
      exact supplied
  | cleanup code tail => exact .cleanup (.capability supplied) .empty

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSource.recover
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSource.rechecking

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSource.recoverAt
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.request_callback

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSource.recoverJoined
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InterceptSource.recoverJoined_normal
