import SourceConsumingBoundGeneration
import SourceBoundSnapshots
import SourceScheduledAnnotationWorldLaws

/-! Structural correspondence between a consuming source body and emitted code.
The immutable retained bounds describe its bound continuation. They are data,
not another admission predicate or a successful target-validity assumption. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledRetainedInterfaces (Interfaces)

/-- Each permitted action has the original retained projection. The waiting
projection is shared by both actions. Resource allocation maps these data. -/
structure ContinuationBounds (world : List Nat) (owner : Nat) (actions : Syntax.UsageTickets)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    (saved : Forest savedHints) (waiting : Forest waitingHints) where
  resumption : (actions owner).any (fun rights => rights.resume) = true → SourceBoundSnapshots.Retained world saved
  closing : (actions owner).any (fun rights => rights.dispose) = true → SourceBoundSnapshots.Retained world saved.forClosing
  after : SourceBoundSnapshots.Retained world waiting

def ContinuationBounds.world_weaken (bounds : ContinuationBounds world owner actions saved waiting)
    (larger : world ⊆ next) : ContinuationBounds next owner actions saved waiting where
  resumption := fun permission => (bounds.resumption permission).world_weaken larger
  closing := fun permission => (bounds.closing permission).world_weaken larger
  after := bounds.after.world_weaken larger

variable [declarations : DeclarationPolicy]

/-- Follow every consuming leaf through the source constructors. At a leaf,
the actual owner cut has the original saved/waiting forests, the emitted saved
or closing and waiting projections are exact, and the caller uses its operation
interface. Handler order, callbacks and fresh-resource bodies remain explicit. -/
inductive Generated (actions : Syntax.UsageTickets) :
    {world : List Nat} → {owner : Nat} →
    {savedScope waitingScope : SourceDependencyCapture.Scope} →
    {savedHints : Hints savedScope} → {waitingHints : Hints waitingScope} →
    {saved : Forest savedHints} → {waiting : Forest waitingHints} →
    ContinuationBounds world owner actions saved waiting →
    {dependencies : SourceDependencyAnnotations.Dependencies} → {plan : Plan dependencies} →
    {wholeScope : SourceDependencyCapture.Scope} → {wholeHints : Hints wholeScope} → {whole : Forest wholeHints} →
    Body world owner plan → Code world plan whole → Prop where
  | resume {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {bounds : ContinuationBounds world owner actions saved waiting}
      {cut : OwnerCut owner whole front saved waiting}
      {inside : Retained world saved (front.append (.spent (owner := owner) waiting))}
      {before : Interfaces world front} {after : Retained world waiting .nil}
      (permission : (actions owner).any (fun rights => rights.resume) = true)
      (savedKept : ofCapability inside = bounds.resumption permission)
      (waitingKept : ofCapability after = bounds.after) :
      Generated actions bounds .resume (.resume cut inside (.operations before) after)
  | dispose {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {bounds : ContinuationBounds world owner actions saved waiting}
      {cut : OwnerCut owner whole front saved waiting}
      {closing : Retained world saved.forClosing (.running (front.append (.spent (owner := owner) waiting)))}
      {before : Interfaces world front} {after : Retained world waiting .nil}
      (permission : (actions owner).any (fun rights => rights.dispose) = true)
      (closingKept : ofCapability closing = bounds.closing permission)
      (waitingKept : ofCapability after = bounds.after) :
      Generated actions bounds .dispose (.dispose cut closing (.operations before) after)
  | sequence : Generated actions bounds body code →
      Generated actions bounds (.sequence required footprint declared body)
        (.sequence (.operations required footprint declared) code)
  | choice : Generated actions bounds first firstCode → Generated actions bounds second secondCode →
      Generated actions bounds (.choice first second) (.choice firstCode secondCode)
  | handler {plans : ClausePlans clauses families} {clauseBounds : ClauseBounds plans}
      {declared : declarations.accepts required plans}
      {body : Body world owner plan} {code : Code world plan
        (.handler (effect := effect) (table := table) (families := families) (required := required) whole)} :
      Generated actions bounds body code →
      Generated actions bounds (.handler clauseBounds declared body) (.handler declared code (some clauseBounds))
  | cleanup {code : Code world plan (.cleanup (needs := needs) callback whole)} :
      Generated actions bounds body code →
      Generated actions bounds (.cleanup (needs := needs) required footprint declared body)
        (.cleanup code (.operations required footprint declared))
  | resource {families : Nat → SourceDependencyAnnotations.Dependencies}
      {plans : ∀ identity, Plan (families identity)}
      {bounds : ContinuationBounds world owner actions saved waiting}
      {body : ∀ identity, identity ∉ world → Body (world ++ [identity]) owner (plans identity)}
      {code : ∀ identity, identity ∉ world → Code (world ++ [identity]) (plans identity) (.cell (identity := identity) whole)}
      (each : ∀ identity fresh, Generated actions (bounds.world_weaken (List.subset_append_left world [identity]))
        (body identity fresh) (code identity fresh)) :
      Generated actions bounds (.resource body) (.resource code)

/-- Current-expression bounds are a projection of structural generated-source
correspondence, including the explicit bounds of every nested handler. -/
theorem Generated.current_bounds
    {body : Body world owner plan} {code : Code world plan whole}
    (generated : Generated actions bounds body code) :
    SourcePlanBounds.ofCode code = body.boundAnnotation := by
  induction generated with
  | resume | dispose => rfl
  | sequence rest ih => simp only [SourcePlanBounds.ofCode, Body.boundAnnotation, ih]
  | choice first second ihFirst ihSecond => simp only [SourcePlanBounds.ofCode, Body.boundAnnotation, ihFirst, ihSecond]
  | handler inner ih => simp only [SourcePlanBounds.ofCode, Body.boundAnnotation, ih]
  | cleanup inner ih => simp only [SourcePlanBounds.ofCode, Body.boundAnnotation, ih]
  | resource each ih =>
      simp only [SourcePlanBounds.ofCode, Body.boundAnnotation]
      congr 1
      funext identity fresh
      exact ih identity fresh

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Generated.current_bounds
