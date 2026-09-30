import SourceConsumingUseReceiver
import SourceConsumingAdmissionComputation
import SourceConsumingAdmissionEntries

/-! Source-directed computation and boundary descent reuse the original
body reductions and snapshot relations. The captured context stays fixed;
resource allocation maps that context into the same larger world. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy Code)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot Computed EnteredResource)

variable [DeclarationPolicy]
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {original : Context world owner outward actions phases base baseFront saved waiting}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {cut : OwnerCut owner whole front saved waiting} {before : Interfaces world front}
    {targetHints : Hints targetScope} {target : Forest targetHints}

theorem AtUse.choice_branches {left : Body world owner leftPlan} {right : Body world owner rightPlan}
    (source : AtUse outward actions phases original (.choice left right) front) :
    AtUse outward actions phases original left front ∧ AtUse outward actions phases original right front := by
  cases source with | choice left right => exact ⟨left, right⟩

/-- Reuse the existing four reduction constructors. Each selects an already
admitted source subtree and its independent finite check. -/
theorem AtUse.reduce {body : Body world owner plan} {next : Body world owner nextPlan}
    (source : AtUse outward actions phases original body front)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope before)
    (step : body.Reduction rule next) :
    AtUse outward actions phases original next front ∧
    next.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope before := by
  cases step with
  | bind => exact ⟨source.sequence_rest, checked.2⟩
  | beta => exact ⟨source.sequence_rest.sequence_rest, checked.2.2⟩
  | ifTrue => exact ⟨source.sequence_rest.choice_branches.1, checked.2.1⟩
  | ifFalse => exact ⟨source.sequence_rest.choice_branches.2, checked.2.2⟩

theorem UseQueuedBody.reduced {plan : Plan dependencies} {bounds : Annotation world plan}
    (record : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    {nextPlan : Plan nextDependencies} {nextBounds : Annotation world nextPlan}
    (step : SourcePlanBounds.Reduced world rule bounds nextBounds) :
    ∃ next : UseQueuedBody resumeRequired closeRequired original cut before nextBounds,
      record.body.Reduction rule next.body := by
  obtain ⟨body, reduced, origin⟩ := record.body.reduced_source (record.origin ▸ step)
  obtain ⟨source, checked⟩ := record.source.reduce record.checked reduced
  exact ⟨⟨body, origin, source, reduced.nested record.nested, checked⟩, reduced⟩

/-- The actual computation snapshot selects the successor record. Its neutral
receiver path and original captured source remain unchanged. -/
theorem UseReceiverBody.computed {plan : Plan dependencies} {bounds : Annotation world plan}
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds)
    (pending : SourceBoundSnapshots.Retained world target) {next : Snapshot world}
    (step : Computed rule ⟨_, plan, bounds, _, _, target, pending⟩ next) :
    ∃ child : UseReceiverBody resumeRequired closeRequired original cut before target next.current,
      record.source.body.Reduction rule child.source.body ∧
      next = ⟨_, next.plan, child.source.body.boundAnnotation, _, _, target, pending⟩ := by
  cases step with
  | step current nextBounds selected =>
      obtain ⟨source, reduced⟩ := record.source.reduced selected
      refine ⟨⟨source, record.receiver⟩, reduced, ?_⟩
      exact congrArg (fun bounds => (⟨_, _, bounds, _, _, target, pending⟩ : Snapshot world)) source.origin

def UseQueuedBody.sequence_rest {first : Plan firstDependencies} {rest : Plan restDependencies}
    {bounds : Annotation world (.sequence first rest)}
    (record : UseQueuedBody resumeRequired closeRequired original cut before bounds) :
    UseQueuedBody resumeRequired closeRequired original cut before bounds.second := by
  rcases record with ⟨body, rfl, source, nested, checked⟩
  cases body with
  | sequence required footprint declared rest =>
      refine ⟨rest, rfl, source.sequence_rest, ?_, checked.2⟩
      cases nested with | sequence inner => exact inner

def UseReceiverBody.sequence_rest {first : Plan firstDependencies} {rest : Plan restDependencies}
    {bounds : Annotation world (.sequence first rest)}
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds) :
    UseReceiverBody resumeRequired closeRequired original cut before target bounds.second :=
  ⟨record.source.sequence_rest, record.receiver⟩

/-- Cleanup entry derives the child and the exact operation interface of its
callback. The callback check is transported to the actual running receiver. -/
theorem UseReceiverBody.cleanup_body {callback : Plan callbackDependencies} {bodyPlan : Plan dependencies}
    {bounds : Annotation world (.cleanup (needs := needs) callback bodyPlan)}
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds) :
    ∃ required, ∃ footprint : RequestFootprint callback required, ∃ declared : Declared world (signature callback),
    ∃ _child : UseReceiverBody resumeRequired closeRequired original
      (.cleanup (needs := needs) (plan := callback) cut)
      (.cleanup front required footprint declared before) (.cleanup (needs := needs) callback target) bounds.cleanupBody,
      (Code.operations (forest := .running target) required footprint declared).Valid outward actions phases ∧
      bounds.cleanupCallback = Annotation.absent ∧
      (∀ request ∈ required, request.1 ∈ needs) := by
  rcases record with ⟨⟨body, rfl, source, nested, checked⟩, receiver⟩
  cases body with
  | cleanup required footprint declared child =>
      have inner : AtUse outward actions phases original child (.cleanup (needs := needs) callback front) := by
        cases source with | cleanup covered source => exact source
      have covered : ∀ request ∈ required, request.1 ∈ needs := by
        cases source with | cleanup covered source => exact covered
      have nestedChild : child.Nested := by cases nested with | cleanup inner => exact inner
      refine ⟨required, footprint, declared,
        ⟨⟨child, rfl, inner, nestedChild, checked.1⟩, .cleanup receiver⟩, ?_, rfl, covered⟩
      change SourceContextualHints.checkRequirements (.running targetScope) required = true
      exact (SourceScheduledNeutral.Expansion.running receiver).erase.requirements ▸ checked.2

/-- Actual cleanup installation determines the child, callback and queued
metadata. The callback is operation-annotated by the existing Body grammar. -/
theorem UseReceiverBody.cleanup_entered {plan : Plan dependencies} {bounds : Annotation world plan}
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds)
    (pending : SourceBoundSnapshots.Retained world target) {next : Snapshot world}
    (step : SourceBoundSnapshots.EnteredCleanup ⟨_, plan, bounds, _, _, target, pending⟩ next) :
    ∃ needs callbackDependencies, ∃ callback : Plan callbackDependencies,
    ∃ required, ∃ footprint : RequestFootprint callback required, ∃ declared : Declared world (signature callback),
    ∃ child : UseReceiverBody resumeRequired closeRequired original
      (.cleanup (needs := needs) (plan := callback) cut)
      (.cleanup front required footprint declared before) (.cleanup (needs := needs) callback target) next.current,
      next = ⟨_, next.plan, child.source.body.boundAnnotation, _, _, .cleanup (needs := needs) callback target,
        .cleanup Annotation.absent pending⟩ ∧
      (Code.operations (forest := .running target) required footprint declared).Valid outward actions phases ∧
      (∀ request ∈ required, request.1 ∈ needs) := by
  cases step
  obtain ⟨required, footprint, declared, child, ready, callbackBounds, covered⟩ := record.sequence_rest.cleanup_body
  refine ⟨_, _, _, required, footprint, declared, child, ?_, ready, covered⟩
  rw [callbackBounds, ← child.source.origin]

/-- Allocation instantiates the original universally fresh body, retaining
the same saved source mapped into the larger world. -/
def UseQueuedBody.resource_body
    {families : Nat → SourceDependencyAnnotations.Dependencies} {plans : ∀ identity, Plan (families identity)}
    {bounds : Annotation world (.resource plans)}
    (record : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    (fresh : identity ∉ world) :
    UseQueuedBody resumeRequired closeRequired (original.world_weaken (List.subset_append_left _ [identity]))
      (.cell (identity := identity) cut) (.cell (before.world_weaken (List.subset_append_left _ [identity])))
      (bounds.resourceBody fresh) := by
  rcases record with ⟨body, rfl, source, nested, checked⟩
  cases body with
  | resource bodies =>
      refine ⟨bodies identity fresh, rfl, ?_, ?_, checked identity fresh⟩
      · cases source with | resource each => exact each identity fresh
      · cases nested with | resource each => exact each identity fresh

def UseReceiverBody.resource_body
    {families : Nat → SourceDependencyAnnotations.Dependencies} {plans : ∀ identity, Plan (families identity)}
    {bounds : Annotation world (.resource plans)}
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds)
    (fresh : identity ∉ world) :
    UseReceiverBody resumeRequired closeRequired (original.world_weaken (List.subset_append_left _ [identity]))
      (.cell (identity := identity) cut) (.cell (before.world_weaken (List.subset_append_left _ [identity])))
      (.cell (identity := identity) target) (bounds.resourceBody fresh) :=
  ⟨record.source.resource_body fresh, .cell record.receiver⟩

/-- The resource event fixes both the selected body and the world-weakened
pending snapshot. Successor source is obtained by descent, not supplied. -/
theorem UseReceiverBody.resource_entered {plan : Plan dependencies} {bounds : Annotation world plan}
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds)
    (pending : SourceBoundSnapshots.Retained world target) (fresh : identity ∉ world)
    {next : Snapshot (world ++ [identity])}
    (step : EnteredResource identity ⟨_, plan, bounds, _, _, target, pending⟩ next) :
    ∃ child : UseReceiverBody resumeRequired closeRequired (original.world_weaken (List.subset_append_left _ [identity]))
      (.cell (identity := identity) cut) (.cell (before.world_weaken (List.subset_append_left _ [identity])))
      (.cell (identity := identity) target) next.current,
      next = ⟨_, next.plan, child.source.body.boundAnnotation, _, _, .cell (identity := identity) target,
        .cell (pending.world_weaken (List.subset_append_left _ [identity]))⟩ := by
  cases step
  refine ⟨record.sequence_rest.resource_body fresh, ?_⟩
  rw [← (record.sequence_rest.resource_body fresh).source.origin]

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.choice_branches
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.reduce
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.reduced
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.computed
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.sequence_rest
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.sequence_rest
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.cleanup_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.cleanup_entered
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.resource_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.resource_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.resource_entered
