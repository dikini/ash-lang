import SourceScheduledInterfaceRequirements

/-! Split retained operation annotations at the existing handler cut. Closing
annotations are computed from the same source; captures cannot substitute a
different callback footprint. -/
namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)

def Interfaces.append {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {tail : Forest tailHints}
    (first : Interfaces world front) (second : Interfaces world tail) :
    Interfaces world (front.append tail) :=
  match first with
  | .nil => second
  | .plain rest required footprint declared next =>
      .plain (rest.append tail) required footprint declared (next.append second)
  | .handler rest next => .handler (rest.append tail) (next.append second)
  | .cell next => .cell (next.append second)
  | .cleanup rest required footprint declared next =>
      .cleanup (rest.append tail) required footprint declared (next.append second)
  | .running next => .running (next.append second)
  | .live rest saved next => .live (rest.append tail) saved (next.append second)
  | .spent next => .spent (next.append second)

theorem Interfaces.check_append {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {tail : Forest tailHints}
    (first : Interfaces world front) (second : Interfaces world tail) :
    (first.append second).check outside =
      (first.check (tailScope.append outside) && second.check outside) := by
  induction first with
  | nil => rfl
  | plain rest required footprint declared next ih =>
      change (_ && (next.append second).check outside) = ((_ && next.check _) && _)
      rw [ih, Bool.and_assoc]
      congr 2
      exact SourceDependencyChecks.scope_append_assoc _ _ _
  | handler rest next ih =>
      change (_ && (next.append second).check outside) = ((_ && next.check _) && _)
      rw [ih, Bool.and_assoc]
      congr 2
      exact SourceDependencyChecks.scope_append_assoc _ _ _
  | cell next ih | running next ih | spent next ih => exact ih
  | cleanup rest required footprint declared next ih =>
      change (_ && (next.append second).check outside) = ((_ && next.check _) && _)
      rw [ih, Bool.and_assoc]
      congr 2
      exact congrArg Scope.running (SourceDependencyChecks.scope_append_assoc _ _ _)
  | live rest saved next ihSaved ih =>
      change (_ && (next.append second).check outside) = ((_ && next.check _) && _)
      rw [ih, Bool.and_assoc]
      congr 2
      exact SourceDependencyChecks.scope_append_assoc _ _ _

/-- Splitting reads each annotation once and retains its exact footprint and
source declaration proof. It does not infer a new footprint after capture. -/
def Interfaces.splitAt {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    (front : Forest frontHints) (tail : Forest tailHints)
    (source : Interfaces world (front.append tail)) :
    Interfaces world front × Interfaces world tail :=
  match front with
  | .nil => (.nil, source)
  | .plain _ rest => match source with
    | .plain _ required footprint declared next =>
      let parts := next.splitAt rest tail
      (.plain rest required footprint declared parts.1, parts.2)
  | .handler rest => match source with
    | .handler _ next =>
      let parts := next.splitAt rest tail
      (.handler rest parts.1, parts.2)
  | .cell rest => match source with
    | .cell next =>
      let parts := next.splitAt rest tail
      (.cell parts.1, parts.2)
  | .cleanup _ rest => match source with
    | .cleanup _ required footprint declared next =>
      let parts := next.splitAt rest tail
      (.cleanup rest required footprint declared parts.1, parts.2)
  | .running rest => match source with
    | .running next =>
      let parts := next.splitAt rest tail
      (.running parts.1, parts.2)
  | .live _ rest => match source with
    | .live _ saved next =>
      let parts := next.splitAt rest tail
      (.live rest saved parts.1, parts.2)
  | .spent rest => match source with
    | .spent next =>
      let parts := next.splitAt rest tail
      (.spent parts.1, parts.2)

theorem Interfaces.splitAt_append {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    (front : Forest frontHints) (tail : Forest tailHints)
    (source : Interfaces world (front.append tail)) :
    (source.splitAt front tail).1.append (source.splitAt front tail).2 = source := by
  induction front with
  | nil => rfl
  | plain plan rest ih => cases source with
    | plain _ required footprint declared next =>
        simpa only [Interfaces.splitAt, Interfaces.append, Forest.append, Hints.append, Scope.append] using
          congrArg (fun next => Interfaces.plain (rest.append tail) required footprint declared next) (ih next)
  | handler rest ih => cases source with
    | handler _ next =>
        simpa only [Interfaces.splitAt, Interfaces.append, Forest.append, Hints.append, Scope.append] using
          congrArg (Interfaces.handler (rest.append tail)) (ih next)
  | cell rest ih => cases source with
    | cell next => simpa only [Interfaces.splitAt, Interfaces.append, Forest.append, Hints.append, Scope.append] using congrArg Interfaces.cell (ih next)
  | cleanup plan rest ih => cases source with
    | cleanup _ required footprint declared next =>
        simpa only [Interfaces.splitAt, Interfaces.append, Forest.append, Hints.append, Scope.append] using
          congrArg (fun next => Interfaces.cleanup (rest.append tail) required footprint declared next) (ih next)
  | running rest ih => cases source with
    | running next => simpa only [Interfaces.splitAt, Interfaces.append, Forest.append, Hints.append, Scope.append] using congrArg Interfaces.running (ih next)
  | live dormant rest ihDormant ih => cases source with
    | live _ saved next =>
        simpa only [Interfaces.splitAt, Interfaces.append, Forest.append, Hints.append, Scope.append] using
          congrArg (Interfaces.live (rest.append tail) saved) (ih next)
  | spent rest ih => cases source with
    | spent next => simpa only [Interfaces.splitAt, Interfaces.append, Forest.append, Hints.append, Scope.append] using congrArg Interfaces.spent (ih next)

/-- The existing cut supplies all scope, hint and plan equalities. Recombining
the extracted interfaces gives precisely the pre-capture source annotation. -/
theorem Interfaces.split_cut {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (source : Interfaces world forest)
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved tail) :
    ∃ inside : Interfaces world saved, ∃ after : Interfaces world tail,
      HEq source (inside.append after) ∧
      ∀ outside, source.check outside =
        (inside.check (tailScope.append outside) && after.check outside) := by
  have scopeSame := cut.erase.reconstruct_scope
  have hintsSame := cut.erase.hints
  have forestSame := cut.forest
  cases scopeSame
  cases hintsSame
  cases forestSame
  let parts := source.splitAt saved tail
  have same := source.splitAt_append saved tail
  exact ⟨parts.1, parts.2, HEq.symm (heq_of_eq same),
    fun outside => same ▸ parts.1.check_append parts.2⟩

/-- Equality transport along an already selected cut makes the structural
split available to the finite request checker. No choice of annotations is
made here: the result is computed by `splitAt` on the original source. -/
def Interfaces.atCut {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (source : Interfaces world forest)
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved tail) :
    Interfaces world saved × Interfaces world tail := by
  have scopeSame := cut.erase.reconstruct_scope
  have hintsSame := cut.erase.hints
  have forestSame := cut.forest
  cases scopeSame
  cases hintsSame
  cases forestSame
  exact source.splitAt saved tail

theorem Interfaces.check_atCut {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (source : Interfaces world forest)
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved tail) :
    source.check outside =
      ((source.atCut cut).1.check (tailScope.append outside) && (source.atCut cut).2.check outside) := by
  have scopeSame := cut.erase.reconstruct_scope
  have hintsSame := cut.erase.hints
  have forestSame := cut.forest
  cases scopeSame
  cases hintsSame
  cases forestSame
  change source.check outside =
    ((source.splitAt saved tail).1.check _ && (source.splitAt saved tail).2.check outside)
  exact (congrArg (fun annotation => annotation.check outside) (source.splitAt_append saved tail)).symm.trans
    ((source.splitAt saved tail).1.check_append (source.splitAt saved tail).2)

/-- Closing erases ordinary pending code and handlers, retains callbacks and
builtin providers, and preserves dormant captures in their actual order. -/
def Interfaces.forClosing {hints : Hints scope} {forest : Forest hints}
    (source : Interfaces world forest) : Interfaces world forest.forClosing :=
  match source with
  | .nil => .nil
  | .plain _ _ _ _ next | .handler _ next | .spent next => next.forClosing
  | .cell next => .cell next.forClosing
  | .cleanup rest required footprint declared next =>
      .cleanup rest.forClosing required footprint declared next.forClosing
  | .running next => .running next.forClosing
  | .live _ saved next => saved.forClosing.append (.running next.forClosing)

theorem Interfaces.check_forClosing {hints : Hints scope} {forest : Forest hints}
    (source : Interfaces world forest) :
    source.forClosing.check outside = source.callbacks.check outside := by
  induction source generalizing outside with
  | nil => rfl
  | plain rest required footprint declared next ih | handler rest next ih => exact ih
  | cell next ih | running next ih | spent next ih => exact ih
  | cleanup rest required footprint declared next ih =>
      change (_ && next.forClosing.check outside) = (_ && next.callbacks.check outside)
      rw [ih]
      rfl
  | live rest saved next ihSaved ih =>
      change (saved.forClosing.append (.running next.forClosing)).check outside =
        (saved.callbacks.check _ && next.callbacks.check outside)
      rw [saved.forClosing.check_append (.running next.forClosing)]
      change (saved.forClosing.check _ && next.forClosing.check outside) =
        (saved.callbacks.check _ && next.callbacks.check outside)
      rw [ihSaved, ih]
      rfl

theorem Interfaces.check_forClosing_iff {hints : Hints scope} {forest : Forest hints}
    (source : Interfaces world forest) :
    source.forClosing.check outside = true ↔
      SourceContextualHints.checkRequirements outside source.callbacks.exposed = true := by
  rw [source.check_forClosing]
  exact source.callbacks.check_iff

theorem Interfaces.append_world_weaken {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {tail : Forest tailHints}
    (first : Interfaces world front) (second : Interfaces world tail) (larger : world ⊆ nextWorld) :
    (first.append second).world_weaken larger =
      (first.world_weaken larger).append (second.world_weaken larger) := by
  induction first <;> simp_all [Interfaces.append, Interfaces.world_weaken] <;> rfl

theorem Interfaces.forClosing_world_weaken {hints : Hints scope} {forest : Forest hints}
    (source : Interfaces world forest) (larger : world ⊆ nextWorld) :
    (source.world_weaken larger).forClosing = source.forClosing.world_weaken larger := by
  induction source with
  | nil => rfl
  | plain rest required footprint declared next ih | handler rest next ih => exact ih
  | cell next ih => exact congrArg Interfaces.cell ih
  | running next ih => exact congrArg Interfaces.running ih
  | spent next ih => exact ih
  | cleanup rest required footprint declared next ih =>
      exact congrArg (Interfaces.cleanup rest.forClosing required footprint (declared.world_weaken larger)) ih
  | live rest saved next ihSaved ih =>
      change (saved.world_weaken larger).forClosing.append (.running (next.world_weaken larger).forClosing) =
        (saved.forClosing.append (.running next.forClosing)).world_weaken larger
      rw [ihSaved, ih]
      exact (saved.forClosing.append_world_weaken (.running next.forClosing) larger).symm

theorem Interfaces.splitAt_world_weaken {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    (front : Forest frontHints) (tail : Forest tailHints)
    (source : Interfaces world (front.append tail)) (larger : world ⊆ nextWorld) :
    (source.world_weaken larger).splitAt front tail =
      ((source.splitAt front tail).1.world_weaken larger, (source.splitAt front tail).2.world_weaken larger) := by
  induction front with
  | nil => rfl
  | plain plan rest ih => cases source with
    | plain _ required footprint declared next =>
        simp only [Interfaces.splitAt, Interfaces.world_weaken, ih]
  | handler rest ih => cases source with
    | handler _ next => simp only [Interfaces.splitAt, Interfaces.world_weaken, ih]
  | cell rest ih => cases source with
    | cell next => simp only [Interfaces.splitAt, Interfaces.world_weaken, ih]
  | cleanup plan rest ih => cases source with
    | cleanup _ required footprint declared next =>
        simp only [Interfaces.splitAt, Interfaces.world_weaken, ih]
  | running rest ih => cases source with
    | running next => simp only [Interfaces.splitAt, Interfaces.world_weaken, ih]
  | live dormant rest ihDormant ih => cases source with
    | live _ saved next => simp only [Interfaces.splitAt, Interfaces.world_weaken, ih]
  | spent rest ih => cases source with
    | spent next => simp only [Interfaces.splitAt, Interfaces.world_weaken, ih]

/-- Opening a fresh resource world retains the exact source-derived pieces.
This is data transport, not a new bound chosen in the larger world. -/
theorem Interfaces.atCut_world_weaken {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (source : Interfaces world forest)
    (cut : SourceScheduledNeutral.Cut effect operation offered modes forest saved tail)
    (larger : world ⊆ nextWorld) :
    (source.world_weaken larger).atCut cut =
      ((source.atCut cut).1.world_weaken larger, (source.atCut cut).2.world_weaken larger) := by
  have scopeSame := cut.erase.reconstruct_scope
  have hintsSame := cut.erase.hints
  have forestSame := cut.forest
  cases scopeSame
  cases hintsSame
  cases forestSame
  exact source.splitAt_world_weaken saved tail larger

end Ash.OneShot.SourceScheduledRetainedInterfaces

#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_append
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.splitAt_append
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.split_cut
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_atCut
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_forClosing
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_forClosing_iff
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.append_world_weaken
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.forClosing_world_weaken
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.splitAt_world_weaken
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.atCut_world_weaken
