import SourceScheduledPendingSites

/-! Structural callback admission at closing positions. This judgment walks
the original retained source and checks only callbacks that survive closing;
it does not take a checked replacement schedule as a constructor premise. -/
namespace Ash.OneShot.SourceScheduledClosingCallbacks
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceDependencyCapture (Scope)

/-- Closing drops ordinary pending computations and installed handlers,
retains resources and callbacks, and closes saved branches before their tails.
The callback check uses exactly the receiving suffix of that construction. -/
inductive Callbacks (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (world : List Nat) :
    {scope outside : Scope} → {hints : Hints scope} → {outsideHints : Hints outside} →
    Forest hints → Forest outsideHints → Prop where
  | nil : Callbacks outward actions phases world .nil outside
  | plain : Callbacks outward actions phases world rest outside →
      Callbacks outward actions phases world (.plain plan rest) outside
  | handler : Callbacks outward actions phases world rest outside →
      Callbacks outward actions phases world
        (.handler (effect := effect) (table := table) (families := families) (required := required) rest) outside
  | cell : Callbacks outward actions phases world rest outside →
      Callbacks outward actions phases world (.cell (identity := identity) rest) outside
  | cleanup (callback : Local outward actions phases world plan (.running (rest.forClosing.append outside)))
      (tail : Callbacks outward actions phases world rest outside) :
      Callbacks outward actions phases world (.cleanup (needs := needs) plan rest) outside
  | running : Callbacks outward actions phases world rest outside →
      Callbacks outward actions phases world (.running rest) outside
  | live (saved : Callbacks outward actions phases world captured ((Forest.running rest.forClosing).append outside))
      (tail : Callbacks outward actions phases world rest outside) :
      Callbacks outward actions phases world (.live (owner := owner) captured rest) outside
  | spent : Callbacks outward actions phases world rest outside →
      Callbacks outward actions phases world (.spent (owner := owner) rest) outside

/-- Generate the actual closing source schedule from the per-callback rules,
reusing ordered recomposition for nested live captures. -/
theorem Callbacks.schedule (checked : Callbacks outward actions phases world forest outside) :
    Pending outward actions phases world forest.forClosing outside := by
  induction checked with
  | nil => exact .nil
  | plain next ih | handler next ih | spent next ih => exact ih
  | cell next ih => exact .cell ih
  | cleanup callback next ih => exact .cleanup callback ih
  | running next ih => exact .running ih
  | live saved tail ihSaved ihTail =>
      exact (SourceScheduledRecomposition.pending_append_iff _ _ _).mpr ⟨ihSaved, .running ihTail⟩

/-- The callback rules omit no check required by the current closing
construction. There are no installed-handler requirements in a closing forest. -/
theorem callbacks_of_schedule {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (checked : Pending outward actions phases world forest.forClosing outside) :
    Callbacks outward actions phases world forest outside := by
  induction forest generalizing outsideScope with
  | nil => exact .nil
  | plain plan rest ih => exact .plain (ih checked)
  | handler rest ih => exact .handler (ih checked)
  | cell rest ih => cases checked with | cell next => exact .cell (ih next)
  | cleanup plan rest ih => cases checked with | cleanup callback next => exact .cleanup callback (ih next)
  | running rest ih => cases checked with | running next => exact .running (ih next)
  | live saved rest ihSaved ihRest =>
      obtain ⟨inside, tail⟩ := (SourceScheduledRecomposition.pending_append_iff _ _ _).mp checked
      cases tail with | running next => exact .live (ihSaved inside) (ihRest next)
  | spent rest ih => exact .spent (ih checked)

theorem callbacks_iff_schedule {hints : Hints scope} {forest : Forest hints} :
    Callbacks outward actions phases world forest outside ↔ Pending outward actions phases world forest.forClosing outside :=
  ⟨Callbacks.schedule, callbacks_of_schedule⟩

/-- The preceding retained-site decomposition also characterizes these rules:
only local code in the closing forest remains, with no declaration interface
obligation. This characterization is a theorem, not an opaque constructor. -/
theorem callbacks_iff_sites {hints : Hints scope} {forest : Forest hints} {outside : Forest outsideHints} :
    Callbacks outward actions phases world forest outside ↔
      ∀ {dependencies atScope} {plan : SourceDeclarationPlans.Plan dependencies}
        {atHints : Hints atScope} {atForest : Forest atHints},
        SourceScheduledPendingSites.Site forest.forClosing outside plan atForest →
          Local outward actions phases world plan atForest := by
  rw [callbacks_iff_schedule, SourceScheduledPendingSites.pending_iff,
    SourcePlannedRecomposition.closing_check]
  exact ⟨And.right, fun supplied => ⟨rfl, supplied⟩⟩

end Ash.OneShot.SourceScheduledClosingCallbacks

#print axioms Ash.OneShot.SourceScheduledClosingCallbacks.Callbacks.schedule
#print axioms Ash.OneShot.SourceScheduledClosingCallbacks.callbacks_of_schedule
#print axioms Ash.OneShot.SourceScheduledClosingCallbacks.callbacks_iff_schedule
#print axioms Ash.OneShot.SourceScheduledClosingCallbacks.callbacks_iff_sites
