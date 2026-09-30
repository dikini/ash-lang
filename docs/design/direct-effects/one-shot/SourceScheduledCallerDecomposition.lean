import SourceScheduledPrefixClosing

/-! Recover the original caller decomposition at an outside continuation.
The existing lookup and forest equations authenticate the caller, not just the
selected saved body and tail. Source children can then be transported by equality. -/
namespace Ash.OneShot.SourceScheduledNeutral
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyOwners (owners)

/-- Two selections of the same owner in the same forest have exactly the same
caller. Reuse lookup determinism and append injectivity, without a new cut induction. -/
theorem OwnerCut.caller_unique
    {wholeHints : Hints wholeScope} {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {first : Forest firstHints} {second : Forest secondHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (before : OwnerCut owner whole first saved tail) (after : OwnerCut owner whole second saved tail) :
    firstScope = secondScope ∧ HEq firstHints secondHints ∧ HEq first second := by
  have selected := Option.some.inj (before.found.symm.trans after.found)
  have sameScope := congrArg (fun selection : SourceContextualInvocationHints.Selection => selection.scopes.front) selected
  refine ⟨sameScope, ?_⟩
  cases sameScope
  injection selected with sameScopes sameFront sameSaved sameTail
  cases sameFront
  exact ⟨HEq.rfl, heq_of_eq (Forest.append_injective
    (eq_of_heq (before.forest.symm.trans after.forest))).1⟩

/-- Recover the actual outside selection and exact decomposition of the
ORIGINAL caller. Its source annotations may be transported by these equalities. -/
theorem OwnerCut.drop_prefix_retaining
    {prefixHints : Hints prefixScope} (leading : Forest prefixHints)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (absent : owner ∉ owners prefixScope)
    (cut : OwnerCut owner (leading.append whole) front saved tail) :
    ∃ suffixScope, ∃ suffixHints : Hints suffixScope, ∃ suffix : Forest suffixHints,
      OwnerCut owner whole suffix saved tail ∧
      frontScope = prefixScope.append suffixScope ∧
      HEq frontHints (prefixHints.append suffixHints) ∧ HEq front (leading.append suffix) := by
  obtain ⟨suffixScope, suffixHints, suffix, outsideCut⟩ := cut.drop_prefix leading absent
  exact ⟨suffixScope, suffixHints, suffix, outsideCut,
    cut.caller_unique (outsideCut.prefix_without_owner leading absent)⟩

/-- Eliminate an arbitrary original caller at the authenticated prefix split.
The motive may quantify its actual saved/caller source children, so equality
transport does not choose substitute source or metadata witnesses. -/
theorem OwnerCut.prefix_cases
    {prefixHints : Hints prefixScope} (leading : Forest prefixHints)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (absent : owner ∉ owners prefixScope)
    (cut : OwnerCut owner (leading.append whole) front saved tail)
    (motive : ∀ {scope} {hints : Hints scope} (caller : Forest hints),
      OwnerCut owner (leading.append whole) caller saved tail → Prop)
    (known : ∀ {scope} {hints : Hints scope} (suffix : Forest hints)
      (outsideCut : OwnerCut owner whole suffix saved tail),
      motive (leading.append suffix) (outsideCut.prefix_without_owner leading absent)) :
    motive front cut := by
  obtain ⟨suffixScope, suffixHints, suffix, outsideCut, sameScope, sameHints, sameForest⟩ :=
    cut.drop_prefix_retaining leading absent
  cases sameScope
  cases sameHints
  cases sameForest
  exact known suffix outsideCut

end Ash.OneShot.SourceScheduledNeutral

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyOwners (owners)
open SourceScheduledNeutral (OwnerCut)

variable [DeclarationPolicy]

/-- Expose the original resumption source at its actual outside caller split.
Both source children are transported identically; the entire original Code is
retained, not merely its current bound projection. -/
theorem Code.resume_caller_source
    {prefixHints : Hints prefixScope} (leading : Forest prefixHints)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (absent : owner ∉ owners prefixScope)
    (cut : OwnerCut owner (leading.append whole) front saved tail)
    (inside : Retained world saved (front.append (.spent (owner := owner) tail)))
    (before : Retained world front (.spent (owner := owner) tail))
    (after : Retained world tail .nil) :
    ∃ suffixScope, ∃ suffixHints : Hints suffixScope, ∃ suffix : Forest suffixHints,
      ∃ outsideCut : OwnerCut owner whole suffix saved tail,
      ∃ savedSource : Retained world saved ((leading.append suffix).append (.spent (owner := owner) tail)),
      ∃ callerSource : Retained world (leading.append suffix) (.spent (owner := owner) tail),
      HEq savedSource inside ∧ HEq callerSource before ∧
      Code.resume (outsideCut.prefix_without_owner leading absent) savedSource callerSource after =
        Code.resume cut inside before after := by
  revert inside before
  apply cut.prefix_cases leading absent
  intro suffixScope suffixHints suffix outsideCut inside before
  exact ⟨_, _, suffix, outsideCut, inside, before, HEq.rfl, HEq.rfl, rfl⟩

/-- Disposal exposes the exact stored closing child at the same original
caller split. The running receiver remains part of that child's index. -/
theorem Code.dispose_caller_source
    {prefixHints : Hints prefixScope} (leading : Forest prefixHints)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (absent : owner ∉ owners prefixScope)
    (cut : OwnerCut owner (leading.append whole) front saved tail)
    (closing : Retained world saved.forClosing (.running (front.append (.spent (owner := owner) tail))))
    (before : Retained world front (.spent (owner := owner) tail))
    (after : Retained world tail .nil) :
    ∃ suffixScope, ∃ suffixHints : Hints suffixScope, ∃ suffix : Forest suffixHints,
      ∃ outsideCut : OwnerCut owner whole suffix saved tail,
      ∃ closingSource : Retained world saved.forClosing
        (.running ((leading.append suffix).append (.spent (owner := owner) tail))),
      ∃ callerSource : Retained world (leading.append suffix) (.spent (owner := owner) tail),
      HEq closingSource closing ∧ HEq callerSource before ∧
      Code.dispose (outsideCut.prefix_without_owner leading absent) closingSource callerSource after =
        Code.dispose cut closing before after := by
  revert closing before
  apply cut.prefix_cases leading absent
  intro suffixScope suffixHints suffix outsideCut closing before
  exact ⟨_, _, suffix, outsideCut, closing, before, HEq.rfl, HEq.rfl, rfl⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.caller_unique

#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.drop_prefix_retaining
#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.prefix_cases

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.resume_caller_source
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.dispose_caller_source
