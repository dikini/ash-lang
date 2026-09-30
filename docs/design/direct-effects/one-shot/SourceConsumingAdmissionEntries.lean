import SourceConsumingAdmissionDescent
import SourceBoundHandlerEntry
import SourceBoundExits
import SourceBoundResources

/-! Structural child admission for the existing bound-snapshot entry relations.
The supplied event fixes the successor; source descent derives its child's
admission and checks and identifies its exact current bounds. These lemmas do
not derive source evidence at every reachable entry or execute a prefix. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body ClauseBounds)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)
open SourceBoundSnapshots (Snapshot EnteredHandler EnteredCleanup EnteredResource)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}
  {wholeScope frontScope savedScope waitingScope : Scope}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {plan : Plan dependencies} {body : Body world owner plan}
  {current : Context world owner outward actions phases whole front saved waiting}

/-- The actual installed handler may have a different clause-plan witness with
the same signatures. Its entry still exposes the exact admitted source body. -/
theorem At.handler_entered
    {plans : ClausePlans clauses families} {actual : ClausePlans actualClauses families}
    {bounds : ClauseBounds plans} {declared : declarations.accepts required plans}
    (admitted : At laws project (.handler (effect := effect) (table := table) bounds declared body) current)
    (checked : (Body.handler (effect := effect) (table := table) bounds declared body).BoundCheck
      resumeRequired closeRequired actions phases wholeScope waitingScope current.before)
    (pending : SourceBoundSnapshots.Retained world whole) {next : Snapshot world}
    (entered : EnteredHandler effect table required actual
      ⟨_, _, (Body.handler (effect := effect) (table := table) bounds declared body).boundAnnotation,
        _, _, whole, pending⟩ next) :
    ∃ child : Context world owner outward actions phases
      (.handler (effect := effect) (table := table) (families := families) (required := required) whole)
      (.handler (effect := effect) (table := table) (families := families) (required := required) front) saved waiting,
      At laws project body child ∧
      body.BoundCheck resumeRequired closeRequired actions phases
        (.handler effect table families wholeScope) waitingScope child.before ∧
      next = ⟨_, _, body.boundAnnotation, _, _,
        .handler (effect := effect) (table := table) (families := families) (required := required) whole,
        .handler pending⟩ := by
  obtain ⟨child, _, source, ready⟩ := admitted.handler_body checked
  refine ⟨child, source, ready, ?_⟩
  cases entered
  rfl

/-- Cleanup entry retains the child and queues precisely the source callback's
bound annotation. The initial expression is already at the runtime entry point. -/
theorem At.cleanup_entered
    {initial : Plan initialDependencies} {callback : Plan callbackDependencies}
    {initialFootprint : RequestFootprint initial initialRequired} {initialDeclared : Declared world (signature initial)}
    {footprint : RequestFootprint callback required} {declared : Declared world (signature callback)}
    (admitted : At laws project (.sequence initialRequired initialFootprint initialDeclared
      (.cleanup (needs := needs) required footprint declared body)) current)
    (checked : (Body.sequence initialRequired initialFootprint initialDeclared
      (.cleanup (needs := needs) required footprint declared body)).BoundCheck
      resumeRequired closeRequired actions phases wholeScope waitingScope current.before)
    (pending : SourceBoundSnapshots.Retained world whole) {next : Snapshot world}
    (entered : EnteredCleanup
      ⟨_, _, (Body.sequence initialRequired initialFootprint initialDeclared
        (.cleanup (needs := needs) required footprint declared body)).boundAnnotation, _, _, whole, pending⟩ next) :
    ∃ child : Context world owner outward actions phases
      (.cleanup (needs := needs) callback whole) (.cleanup (needs := needs) callback front) saved waiting,
      At laws project body child ∧
      body.BoundCheck resumeRequired closeRequired actions phases
        (.cleanup needs callbackDependencies wholeScope) waitingScope child.before ∧
      next = ⟨_, _, body.boundAnnotation, _, _, .cleanup (needs := needs) callback whole,
        .cleanup .absent pending⟩ := by
  obtain ⟨child, _, source, ready⟩ := admitted.sequence_rest.cleanup_body checked.2
  refine ⟨child, source, ready, ?_⟩
  cases entered
  rfl

/-- Resource entry specializes the universally admitted body at the same fresh
identity as the event and preserves the world-weakened pending bounds. -/
theorem At.resource_entered
    {initial : Plan initialDependencies}
    {initialFootprint : RequestFootprint initial initialRequired} {initialDeclared : Declared world (signature initial)}
    {families : Nat → SourceDependencyAnnotations.Dependencies}
    {plans : ∀ identity, Plan (families identity)}
    {code : ∀ identity, identity ∉ world → Body (world ++ [identity]) owner (plans identity)}
    (admitted : At laws project (.sequence initialRequired initialFootprint initialDeclared (.resource code)) current)
    (checked : (Body.sequence initialRequired initialFootprint initialDeclared (.resource code)).BoundCheck
      resumeRequired closeRequired actions phases wholeScope waitingScope current.before)
    (pending : SourceBoundSnapshots.Retained world whole) {next : Snapshot (world ++ [identity])}
    (fresh : identity ∉ world)
    (entered : EnteredResource identity
      ⟨_, _, (Body.sequence initialRequired initialFootprint initialDeclared (.resource code)).boundAnnotation,
        _, _, whole, pending⟩ next) :
    ∃ child : Context (world ++ [identity]) owner outward actions phases
      (.cell (identity := identity) whole) (.cell (identity := identity) front) saved waiting,
      At laws project (code identity fresh) child ∧
      (code identity fresh).BoundCheck resumeRequired closeRequired actions phases
        (.cell identity wholeScope) waitingScope child.before ∧
      next = ⟨_, _, (code identity fresh).boundAnnotation, _, _, .cell (identity := identity) whole,
        .cell (pending.world_weaken (List.subset_append_left _ _))⟩ := by
  obtain ⟨child, _, source, ready⟩ := admitted.sequence_rest.resource_body checked.2 fresh
  refine ⟨child, source, ready, ?_⟩
  cases entered
  rfl

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.handler_entered
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.cleanup_entered
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.resource_entered
