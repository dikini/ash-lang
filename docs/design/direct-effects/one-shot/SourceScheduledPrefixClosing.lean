import SourceScheduledClosingOwners
import SourceScheduledReceiverRechecking

/-! Close a prefix of an original caller while retaining its suffix. This is
source evidence for callback invocations during cleanup: ordinary caller code
inside the closing prefix is discarded, while the surviving caller is checked
at its actual receiver. Existing closing and receiver compilers are reused. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy DeclarationLaws)
open SourceScheduledNeutral (OwnerCut)
open SourceBoundSnapshots.Retained (ofCapability)

/-- The prefix index fixes precisely where closing stops. Every constructor
inspects the original retained source. Callback and dormant-branch obligations
refer to its original children; the suffix uses ordinary receiver rechecking.
Expanded source exposes these constructors. The stopping rule may retain
an operation-only suffix; a protected stop inserts the disposal running marker. -/
inductive PrefixClosing [DeclarationPolicy] (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) :
    {world : List Nat} → {prefixScope suffixScope outsideScope targetScope nextScope : Scope} →
    {prefixHints : Hints prefixScope} → {suffixHints : Hints suffixScope} →
    {outsideHints : Hints outsideScope} → {targetHints : Hints targetScope} → {nextHints : Hints nextScope} →
    (leading : Forest prefixHints) → {suffix : Forest suffixHints} → {outside : Forest outsideHints} →
    Retained world (leading.append suffix) outside → Forest targetHints → Forest nextHints → Prop where
  | nil {source : Retained world suffix outside}
      (changed : ReceiverChange outward actions phases source next) :
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside) .nil source suffix next
  | protect {source : Retained world suffix outside}
      (changed : ReceiverChange outward actions phases source next) :
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside) .nil source (.running suffix) next
  | plain {plan : SourceDeclarationPlans.Plan dependencies}
      {frontHints : Hints frontScope} {front : Forest frontHints}
      {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
      {code : Code world plan ((front.append suffix).append outside)}
      {tail : Retained world (front.append suffix) outside} :
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside) front tail target next →
      PrefixClosing outward actions phases (world := world) (prefixHints := .plain frontHints)
        (suffix := suffix) (outside := outside) (.plain plan front) (.plain code tail) target next
  | handler {frontHints : Hints frontScope} {front : Forest frontHints}
      {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
      {tail : Retained world (front.append suffix) outside} :
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside) front tail target next →
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside)
        (.handler (effect := effect) (table := table) (families := families) (required := required) front)
        (.handler (effect := effect) (table := table) (families := families) (required := required) tail) target next
  | cell {frontHints : Hints frontScope} {front : Forest frontHints}
      {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
      {tail : Retained world (front.append suffix) outside} :
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside) front tail target next →
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside)
        (.cell (identity := identity) front) (.cell (identity := identity) tail) target next
  | cleanup {plan : SourceDeclarationPlans.Plan dependencies}
      {frontHints : Hints frontScope} {front : Forest frontHints}
      {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
      {target : Forest targetHints} {next : Forest nextHints}
      {code : Code world plan (.running ((front.append suffix).append outside))}
      {tail : Retained world (front.append suffix) outside}
      (callback : Expression outward actions phases code (.running ((front.forClosing.append target).append next))) :
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside) front tail target next →
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside)
        (prefixHints := .cleanup (needs := needs) frontHints)
        (.cleanup (needs := needs) plan front) (.cleanup (needs := needs) code tail) target next
  | running {frontHints : Hints frontScope} {front : Forest frontHints}
      {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
      {tail : Retained world (front.append suffix) outside} :
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside) front tail target next →
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside) (.running front) (.running tail) target next
  | live {savedHints : Hints savedScope} {saved : Forest savedHints}
      {frontHints : Hints frontScope} {front : Forest frontHints}
      {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
      {target : Forest targetHints} {next : Forest nextHints}
      {inside : Retained world saved ((front.append suffix).append outside)}
      {tail : Retained world (front.append suffix) outside}
      (dormant : Closing outward actions phases inside (.running ((front.forClosing.append target).append next))) :
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside) front tail target next →
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside)
        (prefixHints := .live (owner := owner) savedHints frontHints)
        (.live (owner := owner) saved front) (.live (owner := owner) inside tail) target next
  | spent {frontHints : Hints frontScope} {front : Forest frontHints}
      {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
      {tail : Retained world (front.append suffix) outside} :
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside) front tail target next →
      PrefixClosing outward actions phases (world := world) (suffix := suffix) (outside := outside)
        (.spent (owner := owner) front) (.spent (owner := owner) tail) target next

variable [declarations : DeclarationPolicy]

/-- Partial closing is an existing retained source transformation. The live
case uses the established append associativity, preserving dormant-first order. -/
theorem PrefixClosing.rechecking
    {prefixHints : Hints prefixScope} {suffixHints : Hints suffixScope}
    {leading : Forest prefixHints} {suffix : Forest suffixHints}
    {source : Retained world (leading.append suffix) outside}
    (closing : PrefixClosing outward actions phases (world := world)
      (suffix := suffix) (outside := outside) leading source target next) :
    RetainedChange outward actions phases source (leading.forClosing.append target) next := by
  induction closing with
  | nil changed => exact changed.rechecking
  | protect changed => exact .protect changed.rechecking
  | plain tail ih => exact .dropPlain ih
  | handler tail ih => exact .dropHandler ih
  | cell tail ih => exact .cell ih
  | cleanup callback tail ih => exact .cleanup callback ih
  | running tail ih => exact .running ih
  | spent tail ih => exact .dropSpent ih
  | live dormant closing ih =>
      rename_i owner savedHints saved frontHints front suffixHints suffix target next inside tail
      apply (SourceScheduledRecomposition.predicate_congr
        (SourceDependencyChecks.scope_append_assoc _ _ _)
        (SourcePlannedRecomposition.hints_append_assoc _ _ _)
        (SourceScheduledRecomposition.forest_append_assoc saved.forClosing (.running front.forClosing) target)
        (fun result => RetainedChange outward actions phases (.live (owner := owner) inside tail) result next)).mpr
      exact .closeLive dormant.rechecking ih

/-- The stopping rule preserves the suffix's live owners. The optional
running marker introduces no owner; every owner in the closing prefix retires. -/
theorem PrefixClosing.surviving_owners
    {prefixHints : Hints prefixScope} {suffixHints : Hints suffixScope}
    {targetHints : Hints targetScope} {leading : Forest prefixHints} {suffix : Forest suffixHints}
    {target : Forest targetHints} {source : Retained world (leading.append suffix) outside}
    (closing : PrefixClosing outward actions phases (suffix := suffix) leading source target next) :
    SourceDependencyOwners.owners (prefixScope.forClosing.append targetScope) =
      SourceDependencyOwners.owners suffixScope := by
  have surviving : SourceDependencyOwners.owners targetScope = SourceDependencyOwners.owners suffixScope := by
    induction closing <;> first | rfl | assumption
  simpa only [SourceScheduledPhaseRestriction.owners_append,
    SourceScheduledPhaseRestriction.owners_closing_empty, List.nil_append] using surviving

/-- Recheck resumption across a closing caller prefix. The original outside
selection determines the new cut. Its saved body and tail are unchanged; only
the saved body's receiver and the original caller's closing prefix are checked. -/
theorem Expression.resume_closing_caller
    {prefixHints : Hints prefixScope} {wholeHints : Hints wholeScope}
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    (leading : Forest prefixHints) {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail)
    (absent : owner ∉ SourceDependencyOwners.owners prefixScope)
    {oldInside : Retained world saved ((leading.append front).append (.spent (owner := owner) tail))}
    {oldBefore : Retained world (leading.append front) (.spent (owner := owner) tail)}
    {oldAfter : Retained world tail .nil}
    (inside : ReceiverChange outward actions (OwnerPhaseTransitions.spend phases owner) oldInside
      ((leading.forClosing.append (.running front)).append (.spent (owner := owner) tail)))
    (caller : PrefixClosing outward actions (OwnerPhaseTransitions.spend phases owner)
      (suffix := front) leading oldBefore (.running front) (.spent (owner := owner) tail)) :
    Expression outward actions phases
      (.resume (cut.prefix_without_owner leading absent) oldInside oldBefore oldAfter)
      (leading.forClosing.append (.running whole)) :=
  .resume ((OwnerCut.running cut).closing_prefix leading) inside.rechecking caller.rechecking .same

/-- Disposal of the same surviving owner uses its original stored closing
body. The caller transformation is shared with resumption, including the
running marker inserted at the closing boundary. -/
theorem Expression.dispose_closing_caller
    {prefixHints : Hints prefixScope} {wholeHints : Hints wholeScope}
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    (leading : Forest prefixHints) {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail)
    (absent : owner ∉ SourceDependencyOwners.owners prefixScope)
    {oldClosing : Retained world saved.forClosing
      (.running ((leading.append front).append (.spent (owner := owner) tail)))}
    {oldBefore : Retained world (leading.append front) (.spent (owner := owner) tail)}
    {oldAfter : Retained world tail .nil}
    (closing : ReceiverChange outward actions (OwnerPhaseTransitions.spend phases owner) oldClosing
      (.running ((leading.forClosing.append (.running front)).append (.spent (owner := owner) tail))))
    (caller : PrefixClosing outward actions (OwnerPhaseTransitions.spend phases owner)
      (suffix := front) leading oldBefore (.running front) (.spent (owner := owner) tail)) :
    Expression outward actions phases
      (.dispose (cut.prefix_without_owner leading absent) oldClosing oldBefore oldAfter)
      (leading.forClosing.append (.running whole)) :=
  .dispose ((OwnerCut.running cut).closing_prefix leading) closing.rechecking caller.rechecking .same

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- The existing compiler preserves structural metadata provenance. No
independently valid successor caller or replacement source is supplied. -/
theorem PrefixClosing.compile_admitted
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {prefixHints : Hints prefixScope} {suffixHints : Hints suffixScope}
    {leading : Forest prefixHints} {suffix : Forest suffixHints}
    {source : Retained world (leading.append suffix) outside}
    (closing : PrefixClosing outward actions phases (world := world)
      (suffix := suffix) (outside := outside) leading source target next)
    (ready : source.Valid outward actions phases) (admitted : (ofCapability source).Admitted) :
    ∃ annotation : Retained world (leading.forClosing.append target) next,
      annotation.Valid outward actions phases ∧ RetainedBounds source (ofCapability annotation) ∧
      (ofCapability annotation).Admitted :=
  closing.rechecking.compile_admitted laws project ready admitted

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosing.rechecking
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosing.compile_admitted

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.resume_closing_caller
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.dispose_closing_caller

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosing.surviving_owners
