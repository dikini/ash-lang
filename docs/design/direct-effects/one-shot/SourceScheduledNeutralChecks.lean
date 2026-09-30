import SourceScheduledNeutral

/-! Transport scheduling through pure frames and callbacks, retaining actual plans.
The older checker supplies capability observations; plan-carrying cuts supply
the exact source pieces needed by the stronger recursive schedules. -/
namespace Ash.OneShot.SourceScheduledNeutralChecks
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceScheduledNeutral (Expansion Cut OwnerCut)

theorem owner_of_parts {hints : Hints scope} {forest : Forest hints}
    {selected : SourceContextualInvocationHints.Selection}
    {front : Forest selected.front} {saved : Forest selected.saved} {tail : Forest selected.tail}
    (found : SourceContextualInvocationHints.findOwner owner hints = some selected)
    (same : HEq forest (front.append (.live (owner := owner) saved tail))) :
    OwnerCut owner forest front saved tail := by
  obtain ⟨actualFront, actualSaved, actualTail, cut⟩ := SourceScheduledNeutral.of_owner forest found
  obtain ⟨frontSame, liveSame⟩ := Forest.append_injective (eq_of_heq (cut.forest.symm.trans same))
  obtain ⟨savedSame, tailSame⟩ := Forest.live.inj liveSame
  cases frontSame
  cases savedSame
  cases tailSame
  exact cut

theorem resume_at {hints : Hints scope}
    (access : SourceContextualInvocations.Resume actions phases owner hints result)
    (found : SourceContextualInvocationHints.findOwner owner hints = some selected) :
    SourceContextualInvocations.Resume actions phases owner hints (selected.resumed owner) := by
  cases access with
  | checked actual checked compatible =>
      cases Option.some.inj (actual.symm.trans found)
      exact .checked found checked compatible

theorem dispose_at {hints : Hints scope}
    (access : SourceContextualInvocations.Dispose outward actions phases owner hints result)
    (found : SourceContextualInvocationHints.findOwner owner hints = some selected) :
    SourceContextualInvocations.Dispose outward actions phases owner hints (selected.disposed owner) := by
  cases access with
  | checked actual checked compatible =>
      cases Option.some.inj (actual.symm.trans found)
      exact .checked found checked compatible

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Reuse the existing request guard transport, then authenticate every new
schedule against the uniquely selected plan-carrying cut. -/
theorem request_transport {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (legacy : SourcePlannedChecks.Local outward actions phases world
      (.request (effect := effect) (operation := operation)) beforeHints)
    (changed : Expansion before after)
    (scheduled : ∀ {captured tail} {savedHints : Hints captured} {waitingHints : Hints tail}
      (saved : Forest savedHints) (waiting : Forest waitingHints) contract modes,
      SourceScheduledNeutral.Cut effect operation contract modes before saved waiting → contract.dispose = true →
      ∀ {nextCaptured nextScope} {closingHints : Hints nextCaptured} {nextHints : Hints nextScope}
        (closing : Forest closingHints) (outside : Forest nextHints),
        Expansion saved.forClosing closing → Expansion (.running waiting) outside →
        Pending outward actions phases world closing outside) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) after := by
  have nextGuard := (SourcePlannedNeutralChecks.local_transport legacy changed.erase).erase
  refine .request nextGuard ?_
  intro captured tail savedHints waitingHints contract modes targetCut targetSaved targetWaiting targetSame disposes
  have guard := SourceDependencyCapture.check_capture_iff.mp (SourceDependencySchemes.checked_request legacy.erase)
  cases guard with
  | builtin found =>
      have next := SourcePlannedCuts.builtin_expand changed.erase found
      cases Option.some.inj (next.symm.trans targetCut.lookup)
  | handler found permission row body closing =>
      obtain ⟨savedHints, waitingHints, selected⟩ := SourcePlannedCuts.of_lookup beforeHints found
      obtain ⟨saved, waiting, cut⟩ := SourceScheduledNeutral.of_cut selected before
      obtain ⟨nextCaptured, nextTail, nextSavedHints, nextWaitingHints, nextSaved, nextWaiting,
        nextCut, inside, outside⟩ := SourceScheduledNeutral.expand changed cut
      cases Option.some.inj (nextCut.erase.lookup.symm.trans targetCut.lookup)
      obtain ⟨rfl, rfl⟩ := nextCut.erase.unique targetCut.hints
      obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (nextCut.forest.symm.trans targetSame))
      exact scheduled saved waiting _ _ cut disposes _ _ inside.forClosing (.running outside)

variable [SourceScheduledChecks.DeclarationProjection admission certification]

theorem local_transport {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (checked : Local outward actions phases world plan forest) {nextHints : Hints nextScope} {next : Forest nextHints}
    (changed : Expansion forest next) : Local outward actions phases world plan next := by
  refine (Local.rec
    (motive_1 := fun phases world _ _ _ plan hints _ => ∀ {nextScope} {nextHints : Hints nextScope} (next : Forest nextHints),
      Expansion hints next → Local outward actions phases world plan next)
    (motive_2 := fun phases world _ _ _ _ hints outside _ => ∀ {nextScope nextOutside}
      {nextHints : Hints nextScope} {nextOutsideHints : Hints nextOutside}
      (next : Forest nextHints) (nextOutsideForest : Forest nextOutsideHints),
      Expansion hints next → Expansion outside nextOutsideForest →
        Pending outward actions phases world next nextOutsideForest)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) next changed
  · intros; exact .pure
  · intros
    rename_i guard scheduled ih nextScope nextHints next expanded
    apply request_transport (Local.erase (.request guard scheduled)) expanded
    intro captured tail savedHints waitingHints saved waiting contract modes cut disposes nextCaptured nextOutside closingHints outsideHints closing outside insideExpansion outsideExpansion
    exact ih _ _ _ _ contract modes cut.erase saved waiting cut.forest disposes closing outside insideExpansion outsideExpansion
  · intros
    rename_i found access same restored ih nextScope nextHints next expanded
    have cut := owner_of_parts found same
    obtain ⟨_, _, _, _, front, tail, nextCut, caller, waiting⟩ := SourceScheduledNeutral.expand_owner expanded cut
    obtain ⟨result, nextAccess, related⟩ := expanded.erase.resume access
    exact .resume (front := front) (tail := tail) nextCut.found (resume_at nextAccess nextCut.found) nextCut.forest
      (ih _ _ ((caller.append (.spent waiting)).prefix _) .refl)
  · intros
    rename_i found access same scheduled ih nextScope nextHints next expanded
    have cut := owner_of_parts found same
    obtain ⟨_, _, _, _, front, tail, nextCut, caller, waiting⟩ := SourceScheduledNeutral.expand_owner expanded cut
    obtain ⟨result, nextAccess, related⟩ := expanded.erase.dispose access
    exact .dispose (front := front) (tail := tail) nextCut.found (dispose_at nextAccess nextCut.found) nextCut.forest
      (ih _ _ ((Expansion.running (caller.append (.spent waiting))).prefix _) .refl)
  · intros
    rename_i first second ihFirst ihSecond nextScope nextHints next expanded
    exact .sequence (ihFirst _ (.plain expanded)) (ihSecond _ expanded)
  · intros
    rename_i left right ihLeft ihRight nextScope nextHints next expanded
    exact .choice (ihLeft _ expanded) (ihRight _ expanded)
  · intros
    rename_i recipes declarations supplied body ih nextScope nextHints next expanded
    exact .handler recipes declarations (expanded.erase.requirements ▸ supplied) (ih _ (.handler expanded))
  · intros
    rename_i body completion ihBody ihCompletion nextScope nextHints next expanded
    exact .cleanup (ihBody _ (.cleanup expanded)) (ihCompletion _ (.running expanded))
  · intros
    rename_i body ih nextScope nextHints next expanded
    exact .resource (fun identity fresh => ih identity fresh _ (.cell expanded))
  · intros
    rename_i targetScope targetOutside targetHints targetOutsideHints target targetOutsideForest expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | exact .nil
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
  · intros
    rename_i restPlan code tail ihCode ihTail targetScope targetOutside targetHints targetOutsideHints target targetOutsideForest expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | (apply Pending.plain (plan := restPlan)
         · apply ihCode
           exact Expansion.append (by first | exact .refl | assumption) outsideExpanded
         · exact ihTail _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i restHints rest outsideHints outside supplied tail ih targetScope targetOutside targetHints targetOutsideHints target targetOutsideForest expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | (apply Pending.handler
         · refine Eq.mp ?_ supplied
           apply congrArg (fun checked => checked = true)
           exact (Expansion.append (a := rest) (c := outside) (by first | exact .refl | assumption) outsideExpanded).erase.requirements
         · exact ih _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i tail ih targetScope targetOutside targetHints targetOutsideHints target targetOutsideForest expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | exact .cell (ih _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i restPlan completion tail ihCompletion ihTail targetScope targetOutside targetHints targetOutsideHints target targetOutsideForest expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | (apply Pending.cleanup (plan := restPlan)
         · apply ihCompletion
           exact .running (Expansion.append (by first | exact .refl | assumption) outsideExpanded)
         · exact ihTail _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i tail ih targetScope targetOutside targetHints targetOutsideHints target targetOutsideForest expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | exact .running (ih _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i saved tail ihSaved ihTail targetScope targetOutside targetHints targetOutsideHints target targetOutsideForest expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | exact .live (ihSaved _ _ .refl (Expansion.append (by first | exact .refl | assumption) outsideExpanded))
          (ihTail _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i tail ih targetScope targetOutside targetHints targetOutsideHints target targetOutsideForest expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | exact .spent (ih _ _ (by first | exact .refl | assumption) outsideExpanded)

/-- Only the receiving suffix changes; each pending frame keeps its plan. -/
theorem pending_outside_transport {hints : Hints scope} {beforeHints : Hints first} {afterHints : Hints second}
    {forest : Forest hints} {before : Forest beforeHints} {after : Forest afterHints}
    (checked : Pending outward actions phases world forest before) (changed : Expansion before after) :
    Pending outward actions phases world forest after := by
  induction forest generalizing first second with
  | nil => exact .nil
  | plain plan rest ih => cases checked with
    | plain code tail => exact .plain (local_transport code (changed.prefix _)) (ih tail changed)
  | handler rest ih => cases checked with
    | handler supplied tail => exact .handler ((changed.prefix rest).erase.requirements ▸ supplied) (ih tail changed)
  | cell rest ih => cases checked with | cell tail => exact .cell (ih tail changed)
  | cleanup plan rest ih => cases checked with
    | cleanup completion tail => exact .cleanup (local_transport completion (.running (changed.prefix _))) (ih tail changed)
  | running rest ih => cases checked with | running tail => exact .running (ih tail changed)
  | live saved rest ihSaved ihRest => cases checked with
    | live inside tail => exact .live (ihSaved inside (changed.prefix _)) (ihRest tail changed)
  | spent rest ih => cases checked with | spent tail => exact .spent (ih tail changed)

/-- Recheck both sides of a retained schedule. New pure callbacks are kept;
existing callback plans, owner permissions and phases remain the same. -/
theorem pending_transport {beforeHints : Hints first} {afterHints : Hints second}
    {outsideBeforeHints : Hints firstOutside} {outsideAfterHints : Hints secondOutside}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideBefore : Forest outsideBeforeHints} {outsideAfter : Forest outsideAfterHints}
    (checked : Pending outward actions phases world before outsideBefore)
    (inside : Expansion before after) (outside : Expansion outsideBefore outsideAfter) :
    Pending outward actions phases world after outsideAfter := by
  have retained := pending_outside_transport checked outside
  clear checked
  induction inside with
  | refl => exact retained
  | extra changed ih => exact .plain (plan := .pure) .pure (ih retained)
  | completion changed ih => exact .cleanup (plan := .pure) .pure (ih retained)
  | history changed ih => exact .spent (ih retained)
  | plain changed ih => cases retained with
    | plain code rest => exact .plain (local_transport code (changed.append .refl)) (ih rest)
  | handler changed ih => cases retained with
    | handler supplied rest => exact .handler ((changed.append (.refl (forest := outsideAfter))).erase.requirements ▸ supplied) (ih rest)
  | cell changed ih => cases retained with | cell rest => exact .cell (ih rest)
  | cleanup changed ih => cases retained with
    | cleanup completion rest => exact .cleanup (local_transport completion (.running (changed.append .refl))) (ih rest)
  | running changed ih => cases retained with | running rest => exact .running (ih rest)
  | live changed ih => cases retained with
    | live saved rest => exact .live (pending_outside_transport saved (changed.append .refl)) (ih rest)
  | spent changed ih => cases retained with | spent rest => exact .spent (ih rest)

/-- A structural cleanup rule for any admitted plan, including continuation
use and requests that may dispose their captures. No successor check is assumed. -/
theorem pure_cleanup {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (body : Local outward actions phases world plan forest) :
    Local outward actions phases world (.cleanup (needs := []) .pure plan) forest :=
  .cleanup (local_transport body (.completion .refl)) .pure

end Ash.OneShot.SourceScheduledNeutralChecks

#print axioms Ash.OneShot.SourceScheduledNeutralChecks.request_transport
#print axioms Ash.OneShot.SourceScheduledNeutralChecks.local_transport
#print axioms Ash.OneShot.SourceScheduledNeutralChecks.pending_outside_transport

#print axioms Ash.OneShot.SourceScheduledNeutralChecks.pending_transport
#print axioms Ash.OneShot.SourceScheduledNeutralChecks.pure_cleanup

#print axioms Ash.OneShot.SourceScheduledNeutralChecks.owner_of_parts

#print axioms Ash.OneShot.SourceScheduledNeutralChecks.resume_at

#print axioms Ash.OneShot.SourceScheduledNeutralChecks.dispose_at
