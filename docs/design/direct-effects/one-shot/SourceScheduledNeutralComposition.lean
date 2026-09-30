import SourceScheduledNeutral

/-! Composition of structural neutral caller expansions. -/
namespace Ash.OneShot.SourceScheduledNeutral
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)

theorem Expansion.trans
    {first middle last : Scope}
    {firstHints : Hints first} {middleHints : Hints middle} {lastHints : Hints last}
    {before : Forest firstHints} {between : Forest middleHints} {after : Forest lastHints}
    (left : Expansion before between) (right : Expansion between after) :
    Expansion before after := by
  induction right generalizing first with
  | refl => exact left
  | extra next ih => exact .extra (ih left)
  | completion next ih => exact .completion (ih left)
  | history next ih => exact .history (ih left)
  | plain next ih =>
      cases left with
      | refl => exact .plain next
      | extra old => exact .extra (ih old)
      | plain old => exact .plain (ih old)
  | handler next ih =>
      cases left with
      | refl => exact .handler next
      | handler old => exact .handler (ih old)
  | cell next ih =>
      cases left with
      | refl => exact .cell next
      | cell old => exact .cell (ih old)
  | cleanup next ih =>
      cases left with
      | refl => exact .cleanup next
      | completion old => exact .completion (ih old)
      | cleanup old => exact .cleanup (ih old)
  | running next ih =>
      cases left with
      | refl => exact .running next
      | running old => exact .running (ih old)
  | live next ih =>
      cases left with
      | refl => exact .live next
      | live old => exact .live (ih old)
  | spent next ih =>
      cases left with
      | refl => exact .spent next
      | history old => exact .history (ih old)
      | spent old => exact .spent (ih old)

end Ash.OneShot.SourceScheduledNeutral

#print axioms Ash.OneShot.SourceScheduledNeutral.Expansion.trans
