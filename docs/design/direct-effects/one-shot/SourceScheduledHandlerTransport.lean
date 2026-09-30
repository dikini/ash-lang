import SourceScheduledHandlerSelection
import SourceScheduledScopedInvocations

/-! Reuse original request schedules under handler insertion. The inserted
handler vanishes during closing; insertion into a waiting suffix transports
only actual callback sites through the shared pending traversal. -/
namespace Ash.OneShot.SourceScheduledHandlerTransport
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope CaptureGuard)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledInterpretationInsertion (Insertion Split)
open SourceScheduledChecks (Local Pending)
open SourceDependencyOwners (owners PendingWithin)

/-- Recover the exact active prefix and suffix surrounding an insertion.
This lets all prefix-based owner and closing lemmas be reused unchanged. -/
theorem handler_context {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Insertion (.handler effect table families required) before after) :
    ∃ frontScope tailScope, ∃ frontHints : Hints frontScope, ∃ tailHints : Hints tailScope,
    ∃ front : Forest frontHints, ∃ tail : Forest tailHints,
      first = frontScope.append tailScope ∧
      second = frontScope.append (.handler effect table families tailScope) ∧
      HEq beforeHints (frontHints.append tailHints) ∧
      HEq afterHints (frontHints.append (.handler (effect := effect) (table := table) (families := families) required tailHints)) ∧
      HEq before (front.append tail) ∧
      HEq after (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) tail)) := by
  induction changed with
  | here => exact ⟨_, _, .nil, _, .nil, _, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  | plain next ih =>
      rename_i dependencies plan
      obtain ⟨_, _, _, _, front, tail, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, _, _, .plain plan front, tail, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | handler next ih =>
      rename_i other otherTable otherFamilies otherRequired
      obtain ⟨_, _, _, _, front, tail, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, _, _, .handler (effect := other) (table := otherTable) (families := otherFamilies) (required := otherRequired) front, tail, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | cell next ih =>
      rename_i identity
      obtain ⟨_, _, _, _, front, tail, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, _, _, .cell (identity := identity) front, tail, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | cleanup next ih =>
      rename_i needs dependencies plan
      obtain ⟨_, _, _, _, front, tail, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, _, _, .cleanup (needs := needs) plan front, tail, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | running next ih =>
      obtain ⟨_, _, _, _, front, tail, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, _, _, .running front, tail, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | live next ih =>
      rename_i owner dormantScope dormantHints dormant
      obtain ⟨_, _, _, _, front, tail, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, _, _, .live (owner := owner) dormant front, tail, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  | spent next ih =>
      rename_i owner
      obtain ⟨_, _, _, _, front, tail, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih
      refine ⟨_, _, _, _, .spent (owner := owner) front, tail, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Insertion anywhere in the captured active spine leaves its actual
closing forest unchanged, including every dormant saved branch. -/
theorem closing_same {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Insertion (.handler effect table families required) before after) :
    first.forClosing = second.forClosing ∧
      HEq (SourceContextualInvocationHints.forClosing beforeHints) (SourceContextualInvocationHints.forClosing afterHints) ∧
      HEq before.forClosing after.forClosing := by
  obtain ⟨_, _, _, _, front, tail, rfl, rfl, rfl, rfl, rfl, rfl⟩ := handler_context changed
  exact ⟨(SourceHandlerRequests.forClosing_inserted _).symm,
    (SourceScheduledHandlerRequests.hints_forClosing_inserted _ _).symm,
    (SourceScheduledHandlerRequests.forest_forClosing_inserted front tail).symm⟩

/-- The captured inventory and pending owner-membership derivation survive
insertion. Reuse the existing prefix proof rather than inspecting code again. -/
theorem owners_preserved {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Insertion (.handler effect table families required) before after) :
    owners first = owners second ∧
      (PendingWithin world owned first → PendingWithin world owned second) := by
  obtain ⟨_, _, _, _, front, tail, rfl, rfl, rfl, rfl, rfl, rfl⟩ := handler_context changed
  exact ⟨(SourceHandlerRequests.owners_inserted _).symm, SourceHandlerRequests.pending_owners_inserted _⟩

/-- Only changes to the receiving suffix require a recursive callback proof.
Closing removes any inserted captured handler, so that branch reuses the
original schedule verbatim. No target Pending proof is an input. -/
theorem closing_transport {savedHints : Hints captured} {waitingHints : Hints tail}
    {nextSavedHints : Hints nextCaptured} {nextWaitingHints : Hints nextTail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {nextSaved : Forest nextSavedHints} {nextWaiting : Forest nextWaitingHints}
    (changed : Split (.handler effect table families required) saved waiting nextSaved nextWaiting)
    (checked : Pending outward actions phases world saved.forClosing (.running waiting))
    (transfer : ∀ {dependencies oldScope targetScope} {plan : SourceDeclarationPlans.Plan dependencies}
      {oldHints : Hints oldScope} {targetHints : Hints targetScope}
      (old : Forest oldHints) (target : Forest targetHints),
      SourceScheduledPendingSites.Site saved.forClosing (.running waiting) plan old →
      Insertion (.handler effect table families required) old target →
      Local outward actions phases world plan old → Local outward actions phases world plan target) :
    Pending outward actions phases world nextSaved.forClosing (.running nextWaiting) := by
  cases changed with
  | inside inserted =>
      obtain ⟨sameScope, sameHints, sameForest⟩ := closing_same inserted
      exact (SourceScheduledRecomposition.predicate_congr sameScope sameHints sameForest
        (fun closing => Pending outward actions phases world closing (.running waiting))).mp checked
  | outside inserted =>
      exact SourceScheduledPendingSites.pending_transport checked (.outside (.running inserted))
        (SourcePlannedRecomposition.closing_check _) transfer

/-- Assemble an existing selected request from its transported schedule.
This is a proof helper: structural adaptation constructs the schedule rather
than storing a target Pending proof in a source rule. -/
theorem retained_request [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    {beforeHints : Hints first} {afterHints : Hints second}
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {nextSavedHints : Hints nextCaptured} {nextWaitingHints : Hints nextTail}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {nextSaved : Forest nextSavedHints} {nextWaiting : Forest nextWaitingHints}
    (oldCut : SourceScheduledNeutral.Cut effect operation contract modes before saved waiting)
    (nextCut : SourceScheduledNeutral.Cut effect operation contract modes after nextSaved nextWaiting)
    (pieces : Split (.handler installed table families required) saved waiting nextSaved nextWaiting)
    (checked : Local outward actions phases world (.request (effect := effect) (operation := operation)) before)
    (guarded : CaptureGuard outward second effect operation)
    (scheduled : contract.dispose = true → Pending outward actions phases world nextSaved.forClosing (.running nextWaiting)) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) after := by
  apply SourceScheduledFreshRequests.request_from_schedule
    (fun source => SourceScheduledChecks.DeclarationProjection.project source) nextCut guarded
  · intro disposes
    have oldBound := SourceDependencySchemes.checked_request_owners checked.erase.erase oldCut.erase.lookup disposes
    cases pieces with
    | outside inserted => exact oldBound
    | inside inserted =>
        obtain ⟨sameOwners, retained⟩ := owners_preserved (world := world) (owned := owners captured) inserted
        simpa only [sameOwners] using retained oldBound
  · exact scheduled

/-- The complete request case of handler insertion. A newly intercepted
request supplies independent structural owner and callback judgments; retained
selections reuse their old proofs. The callback transformer is the local
induction obligation, not a source annotation or a target Pending premise. -/
theorem request_transport {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Insertion (.handler installed table families required) before after)
    (checked : Local outward actions phases world (.request (effect := effect) (operation := operation)) before)
    (guarded : CaptureGuard outward second effect operation)
    (fresh : ∀ {captured tail} {savedHints : Hints captured} {waitingHints : Hints tail}
      (saved : Forest savedHints) (waiting : Forest waitingHints) contract modes,
      SourceScheduledHandlerSelection.Intercept installed operation contract modes table families required before after saved waiting →
      contract.dispose = true →
      PendingWithin world (owners captured) captured ∧
      SourceScheduledClosingCallbacks.Callbacks outward actions phases world saved (.running waiting))
    (transfer : ∀ {captured tail} {savedHints : Hints captured} {waitingHints : Hints tail}
      (saved : Forest savedHints) (waiting : Forest waitingHints) contract modes,
      SourceScheduledNeutral.Cut effect operation contract modes before saved waiting →
      contract.dispose = true →
      ∀ {dependencies oldScope targetScope} {plan : SourceDeclarationPlans.Plan dependencies}
        {oldHints : Hints oldScope} {targetHints : Hints targetScope}
        (old : Forest oldHints) (target : Forest targetHints),
        SourceScheduledPendingSites.Site saved.forClosing (.running waiting) plan old →
        Insertion (.handler installed table families required) old target →
        Local outward actions phases world plan old → Local outward actions phases world plan target) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) after := by
  have guard := guarded
  cases guard with
  | builtin found => exact SourceScheduledScopedInvocations.request_from_capability (.builtin found)
  | handler found permission row body closing =>
      rename_i captured tail contract modes footprint family
      obtain ⟨savedHints, waitingHints, selected⟩ := SourcePlannedCuts.of_lookup afterHints found
      obtain ⟨saved, waiting, cut⟩ := SourceScheduledNeutral.of_cut selected after
      rcases SourceScheduledHandlerSelection.cut_origin changed cut with
        ⟨same, intercepted⟩ | ⟨oldCaptured, oldTail, oldSavedHints, oldWaitingHints, oldSaved, oldWaiting, oldCut, pieces⟩
      · exact SourceScheduledFreshRequests.request_from_callbacks cut guarded
          (fun disposes => (fresh saved waiting contract modes intercepted disposes).1)
          (fun disposes => (fresh saved waiting contract modes intercepted disposes).2)
      · apply retained_request oldCut cut pieces checked guarded
        intro disposes
        have oldSchedule : Pending outward actions phases world oldSaved.forClosing (.running oldWaiting) := by
          cases checked with
          | request lower scheduled => exact scheduled _ _ _ _ _ _ oldCut.erase oldSaved oldWaiting oldCut.forest disposes
        exact closing_transport pieces oldSchedule
          (transfer oldSaved oldWaiting contract modes oldCut disposes)

end Ash.OneShot.SourceScheduledHandlerTransport

#print axioms Ash.OneShot.SourceScheduledHandlerTransport.handler_context
#print axioms Ash.OneShot.SourceScheduledHandlerTransport.closing_same
#print axioms Ash.OneShot.SourceScheduledHandlerTransport.owners_preserved
#print axioms Ash.OneShot.SourceScheduledHandlerTransport.closing_transport

#print axioms Ash.OneShot.SourceScheduledHandlerTransport.request_transport

#print axioms Ash.OneShot.SourceScheduledHandlerTransport.retained_request
