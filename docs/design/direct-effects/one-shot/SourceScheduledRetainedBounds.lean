import SourceScheduledRetainedRecomposition

/-! Structural provenance for retained bound metadata during source rechecking.
Rules preserve each retained code position's original current-plan bounds,
record added frames with absent code bounds, and identify deliberately dropped
closing frames. This relation contains no source-validity or execution premise. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceBoundSnapshots.Retained (ofCapability)
open SourcePlanBounds (ofCode)

/-- Every operation-only retained position already carries its source
signature declaration, so its absent-bound snapshot is structurally admitted. -/
theorem interfaces_absent_admitted [DeclarationPolicy]
    (interfaces : SourceScheduledRetainedInterfaces.Interfaces world forest) :
    (SourceBoundSnapshots.Retained.absent forest (world := world)).Admitted := by
  induction interfaces with
  | nil => exact .nil
  | plain rest required footprint declared next ih => exact .plain (.absent declared) ih
  | handler rest next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup rest required footprint declared next ih => exact .cleanup (.absent declared) ih
  | running next ih => exact .running ih
  | live rest saved next ihSaved ih => exact .live ihSaved ih
  | spent next ih => exact .spent ih

inductive RetainedBounds [DeclarationPolicy] : {world : List Nat} →
    {beforeScope outsideScope : SourceDependencyCapture.Scope} →
    {beforeHints : Hints beforeScope} → {outsideHints : Hints outsideScope} →
    {before : Forest beforeHints} → {outside : Forest outsideHints} →
    Retained world before outside →
    {afterScope : SourceDependencyCapture.Scope} → {afterHints : Hints afterScope} →
    {after : Forest afterHints} → SourceBoundSnapshots.Retained world after → Prop where
  | same : RetainedBounds source (ofCapability source)
  | operations (target : SourceScheduledRetainedInterfaces.Interfaces world after) :
      RetainedBounds (.operations (world := world) interfaces) (.absent after)
  | plain : RetainedBounds tail next → RetainedBounds (.plain code tail) (.plain (ofCode code) next)
  | handler : RetainedBounds tail next →
      RetainedBounds (.handler (effect := effect) (table := table) (families := families) (required := required) tail)
        (.handler (effect := effect) (table := table) (families := families) (required := required) next)
  | cell : RetainedBounds tail next → RetainedBounds (.cell (identity := identity) tail) (.cell (identity := identity) next)
  | cleanup : RetainedBounds tail next →
      RetainedBounds (.cleanup (needs := needs) code tail) (.cleanup (needs := needs) (ofCode code) next)
  | running : RetainedBounds tail next → RetainedBounds (.running tail) (.running next)
  | live : RetainedBounds saved nextSaved → RetainedBounds tail next →
      RetainedBounds (.live (owner := owner) saved tail) (.live (owner := owner) nextSaved next)
  | spent : RetainedBounds tail next → RetainedBounds (.spent (owner := owner) tail) (.spent (owner := owner) next)
  | install : RetainedBounds source
      (.handler (effect := effect) (table := table) (families := families) (required := required) (ofCapability source))
  | installCleanup {source : Retained world before outside} (declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature callback)) :
      RetainedBounds source (.cleanup (needs := needs) (.absent (plan := callback)) (ofCapability source))
  | dropPlain : RetainedBounds tail next → RetainedBounds (.plain code tail) next
  | dropHandler : RetainedBounds tail next →
      RetainedBounds (.handler (effect := effect) (table := table) (families := families) (required := required) tail) next
  | dropSpent : RetainedBounds tail next → RetainedBounds (.spent (owner := owner) tail) next
  | protect : RetainedBounds source next → RetainedBounds source (.running next)
  | closeLive : RetainedBounds saved nextSaved → RetainedBounds tail next →
      RetainedBounds (.live (owner := owner) saved tail) (nextSaved.append (.running next))

/-- Retained metadata admission follows the same structural movement. New
operation-only positions use their original declaration data; no future source
admission or target validity is assumed. -/
theorem RetainedBounds.admitted [DeclarationPolicy]
    {source : Retained world before outside} {target : SourceBoundSnapshots.Retained world after}
    (changed : RetainedBounds source target)
    (original : (ofCapability source).Admitted) : target.Admitted := by
  induction changed with
  | same => exact original
  | operations interfaces => exact interfaces_absent_admitted interfaces
  | plain next ih => cases original with | plain code rest => exact .plain code (ih rest)
  | handler next ih => cases original with | handler rest => exact .handler (ih rest)
  | cell next ih => cases original with | cell rest => exact .cell (ih rest)
  | cleanup next ih => cases original with | cleanup code rest => exact .cleanup code (ih rest)
  | running next ih => cases original with | running rest => exact .running (ih rest)
  | live saved next ihSaved ih => cases original with | live inside rest => exact .live (ihSaved inside) (ih rest)
  | spent next ih => cases original with | spent rest => exact .spent (ih rest)
  | install => exact .handler original
  | installCleanup declared => exact .cleanup (.absent declared) original
  | dropPlain next ih => cases original with | plain code rest => exact ih rest
  | dropHandler next ih => cases original with | handler rest => exact ih rest
  | dropSpent next ih => cases original with | spent rest => exact ih rest
  | protect next ih => exact .running (ih original)
  | closeLive saved next ihSaved ih => cases original with
    | live inside rest => exact (ihSaved inside).append (.running (ih rest))

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.interfaces_absent_admitted
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RetainedBounds.admitted
