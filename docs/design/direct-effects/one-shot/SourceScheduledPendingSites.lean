import SourceScheduledInterpretationInsertion

/-! Retained source sites separate pending-code traversal from the local
operation and invocation obligations. Sites are derived from actual forests;
they preserve the exact stored plan and its receiving scope. -/
namespace Ash.OneShot.SourceScheduledPendingSites
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceDependencyCapture (Scope)
open SourceScheduledChecks (Local Pending)
open SourceScheduledInterpretationInsertion (Insertion)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- A stored computation is checked at its suffix. A callback receives running
protection; a dormant branch receives its original complete waiting suffix. -/
inductive Site : {scope outside : Scope} → {hints : Hints scope} → {outsideHints : Hints outside} →
    Forest hints → Forest outsideHints → {dependencies : SourceDependencyAnnotations.Dependencies} →
    Plan dependencies → {atScope : Scope} → {atHints : Hints atScope} → Forest atHints → Prop where
  | code : Site (.plain plan rest) outside plan (rest.append outside)
  | callback : Site (.cleanup plan rest) outside plan (.running (rest.append outside))
  | plain : Site rest outside plan atForest → Site (.plain other rest) outside plan atForest
  | handler : Site rest outside plan atForest →
      Site (.handler (effect := effect) (table := table) (families := families) (required := required) rest) outside plan atForest
  | cell : Site rest outside plan atForest → Site (.cell (identity := identity) rest) outside plan atForest
  | cleanup : Site rest outside plan atForest → Site (.cleanup (needs := needs) other rest) outside plan atForest
  | running : Site rest outside plan atForest → Site (.running rest) outside plan atForest
  | saved : Site captured (rest.append outside) plan atForest → Site (.live (owner := owner) captured rest) outside plan atForest
  | live : Site rest outside plan atForest → Site (.live (owner := owner) captured rest) outside plan atForest
  | spent : Site rest outside plan atForest → Site (.spent (owner := owner) rest) outside plan atForest

/-- Every site is an existing subderivation of the pending source check. -/
theorem Site.checked (site : Site forest outside plan atForest)
    (checked : Pending outward actions phases world forest outside) :
    Local outward actions phases world plan atForest := by
  induction site with
  | code => cases checked with | plain code tail => exact code
  | callback => cases checked with | cleanup callback tail => exact callback
  | plain site ih => cases checked with | plain code tail => exact ih tail
  | handler site ih => cases checked with | handler supplied tail => exact ih tail
  | cell site ih => cases checked with | cell tail => exact ih tail
  | cleanup site ih => cases checked with | cleanup callback tail => exact ih tail
  | running site ih => cases checked with | running tail => exact ih tail
  | saved site ih => cases checked with | live saved tail => exact ih saved
  | live site ih => cases checked with | live saved tail => exact ih tail
  | spent site ih => cases checked with | spent tail => exact ih tail

/-- No pending-source obligation is lost by separating declaration interfaces
from local code sites. This is a decomposition theorem, not an admission axiom. -/
theorem pending_iff {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} :
    Pending outward actions phases world forest outside ↔
      hints.check outsideScope = true ∧
      ∀ {dependencies atScope} {plan : Plan dependencies} {atHints : Hints atScope} {atForest : Forest atHints},
        Site forest outside plan atForest → Local outward actions phases world plan atForest := by
  constructor
  · intro checked
    exact ⟨(SourceContextualHintChecking.check_iff _).mpr checked.compatible, fun site => site.checked checked⟩
  · rintro ⟨compatible, supplied⟩
    induction forest generalizing outsideScope with
    | nil => exact .nil
    | plain plan rest ih => exact .plain (supplied .code) (ih compatible (fun site => supplied (.plain site)))
    | handler rest ih =>
        simp only [Hints.check, Bool.and_eq_true] at compatible
        exact .handler compatible.1 (ih compatible.2 (fun site => supplied (.handler site)))
    | cell rest ih => exact .cell (ih compatible (fun site => supplied (.cell site)))
    | cleanup plan rest ih => exact .cleanup (supplied .callback) (ih compatible (fun site => supplied (.cleanup site)))
    | running rest ih => exact .running (ih compatible (fun site => supplied (.running site)))
    | live saved rest ihSaved ihRest =>
        simp only [Hints.check, Bool.and_eq_true] at compatible
        exact .live (ihSaved compatible.1 (fun site => supplied (.saved site)))
          (ihRest compatible.2 (fun site => supplied (.live site)))
    | spent rest ih => exact .spent (ih compatible (fun site => supplied (.spent site)))

omit admission certification in
/-- Replacing the outside by an inserted interpretation keeps the stored plan
and inserts the same frame into the site's actual receiving forest. -/
theorem Site.outside {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    {atHints : Hints atScope} {atForest : Forest atHints}
    (changed : Insertion frame before after) (site : Site forest after plan atForest) :
    ∃ oldScope, ∃ oldHints : Hints oldScope, ∃ oldForest : Forest oldHints,
      Site forest before plan oldForest ∧ Insertion frame oldForest atForest := by
  induction site generalizing first with
  | code => exact ⟨_, _, _, .code, changed.prefix _⟩
  | callback => exact ⟨_, _, _, .callback, .running (changed.prefix _)⟩
  | plain site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .plain oldSite, inserted⟩
  | handler site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .handler oldSite, inserted⟩
  | cell site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .cell oldSite, inserted⟩
  | cleanup site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .cleanup oldSite, inserted⟩
  | running site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .running oldSite, inserted⟩
  | saved site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih (changed.prefix _)
      exact ⟨_, _, _, .saved oldSite, inserted⟩
  | live site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .live oldSite, inserted⟩
  | spent site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .spent oldSite, inserted⟩

omit admission certification in
/-- Insertion inside a retained forest either leaves a site's receiving
scope identical or inserts the same interpretation there. No code site is
created by the new interpretation frame itself. -/
theorem Site.inside {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {plan : Plan dependencies} {atHints : Hints atScope} {atForest : Forest atHints}
    (changed : Insertion frame before after) (site : Site after outside plan atForest) :
    Site before outside plan atForest ∨
      ∃ oldScope, ∃ oldHints : Hints oldScope, ∃ oldForest : Forest oldHints,
        Site before outside plan oldForest ∧ Insertion frame oldForest atForest := by
  induction changed generalizing atScope with
  | here => cases frame with
    | cell identity => cases site with | cell next => exact .inl next
    | handler effect table families required => cases site with | handler next => exact .inl next
  | plain changed ih => cases site with
    | code => exact .inr ⟨_, _, _, .code, changed.suffix outside⟩
    | plain next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩
        · exact .inl (.plain same)
        · exact .inr ⟨_, _, _, .plain oldSite, inserted⟩
  | handler changed ih => cases site with
    | handler next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩
        · exact .inl (.handler same)
        · exact .inr ⟨_, _, _, .handler oldSite, inserted⟩
  | cell changed ih => cases site with
    | cell next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩
        · exact .inl (.cell same)
        · exact .inr ⟨_, _, _, .cell oldSite, inserted⟩
  | cleanup changed ih => cases site with
    | callback => exact .inr ⟨_, _, _, .callback, .running (changed.suffix outside)⟩
    | cleanup next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩
        · exact .inl (.cleanup same)
        · exact .inr ⟨_, _, _, .cleanup oldSite, inserted⟩
  | running changed ih => cases site with
    | running next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩
        · exact .inl (.running same)
        · exact .inr ⟨_, _, _, .running oldSite, inserted⟩
  | live changed ih => cases site with
    | saved next =>
        obtain ⟨_, _, _, oldSite, inserted⟩ := next.outside (changed.suffix outside)
        exact .inr ⟨_, _, _, .saved oldSite, inserted⟩
    | live next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩
        · exact .inl (.live same)
        · exact .inr ⟨_, _, _, .live oldSite, inserted⟩
  | spent changed ih => cases site with
    | spent next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩
        · exact .inl (.spent same)
        · exact .inr ⟨_, _, _, .spent oldSite, inserted⟩

omit admission certification in
theorem Site.transport {beforeHints : Hints first} {afterHints : Hints second}
    {beforeOutsideHints : Hints firstOutside} {afterOutsideHints : Hints secondOutside}
    {before : Forest beforeHints} {after : Forest afterHints}
    {beforeOutside : Forest beforeOutsideHints} {afterOutside : Forest afterOutsideHints}
    {plan : Plan dependencies} {atHints : Hints atScope} {atForest : Forest atHints}
    (changed : SourceScheduledInterpretationInsertion.Split frame before beforeOutside after afterOutside)
    (site : Site after afterOutside plan atForest) :
    Site before beforeOutside plan atForest ∨
      ∃ oldScope, ∃ oldHints : Hints oldScope, ∃ oldForest : Forest oldHints,
        Site before beforeOutside plan oldForest ∧ Insertion frame oldForest atForest := by
  cases changed with
  | inside inserted => exact site.inside inserted
  | outside inserted => exact .inr (site.outside inserted)

/-- Reuse the pending traversal once local checks at affected retained sites
have been transported. The `transfer` argument is a local proof transformer;
it is not stored in source syntax or accepted as a declaration recipe. -/
theorem pending_transport {beforeHints : Hints first} {afterHints : Hints second}
    {beforeOutsideHints : Hints firstOutside} {afterOutsideHints : Hints secondOutside}
    {before : Forest beforeHints} {after : Forest afterHints}
    {beforeOutside : Forest beforeOutsideHints} {afterOutside : Forest afterOutsideHints}
    (checked : Pending outward actions phases world before beforeOutside)
    (changed : SourceScheduledInterpretationInsertion.Split frame before beforeOutside after afterOutside)
    (compatible : afterHints.check secondOutside = true)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      (old : Forest oldHints) (next : Forest nextHints), Site before beforeOutside plan old →
        Insertion frame old next → Local outward actions phases world plan old →
          Local outward actions phases world plan next) :
    Pending outward actions phases world after afterOutside := by
  apply pending_iff.mpr
  refine ⟨compatible, ?_⟩
  intro dependencies atScope plan atHints atForest site
  rcases site.transport changed with same | ⟨_, _, old, oldSite, inserted⟩
  · exact same.checked checked
  · exact transfer old atForest oldSite inserted (oldSite.checked checked)

/-- An outside insertion changes declaration compatibility only through the
old forest's exposed finite operation list. All retained code uses the same
site transformer, including code nested in dormant continuations. -/
theorem pending_outside {hints : Hints scope} {forest : Forest hints}
    {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (checked : Pending outward actions phases world forest before)
    (changed : Insertion frame before after)
    (supplied : SourceContextualHints.checkRequirements second (SourceHandlerRequirements.exposed hints) = true)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      (old : Forest oldHints) (next : Forest nextHints), Site forest before plan old →
        Insertion frame old next → Local outward actions phases world plan old →
          Local outward actions phases world plan next) :
    Pending outward actions phases world forest after :=
  pending_transport checked (.outside changed)
    (SourceHandlerRequirements.check_transport hints (pending_iff.mp checked).1 supplied) transfer

/-- For insertion inside the checked forest, the already established finite
handler interface discharges the declaration part of pending transport. -/
theorem pending_handler_inside {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (checked : Pending outward actions phases world before outside)
    (changed : Insertion (.handler effect table families required) before after)
    (supplied : SourceHandlerInvocations.Interface effect table families required outsideScope beforeHints afterHints)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      (old : Forest oldHints) (next : Forest nextHints), Site before outside plan old →
        Insertion (.handler effect table families required) old next → Local outward actions phases world plan old →
          Local outward actions phases world plan next) :
    Pending outward actions phases world after outside :=
  pending_transport checked (.inside changed) (supplied.check (pending_iff.mp checked).1) transfer

end Ash.OneShot.SourceScheduledPendingSites

#print axioms Ash.OneShot.SourceScheduledPendingSites.Site.checked
#print axioms Ash.OneShot.SourceScheduledPendingSites.pending_iff
#print axioms Ash.OneShot.SourceScheduledPendingSites.Site.outside

#print axioms Ash.OneShot.SourceScheduledPendingSites.Site.inside
#print axioms Ash.OneShot.SourceScheduledPendingSites.Site.transport
#print axioms Ash.OneShot.SourceScheduledPendingSites.pending_transport
#print axioms Ash.OneShot.SourceScheduledPendingSites.pending_outside
#print axioms Ash.OneShot.SourceScheduledPendingSites.pending_handler_inside
