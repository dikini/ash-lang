import SourceConsumingUseReceiver
import SourceBoundHandlerEntry

/-! Handler entry consumes the corresponding structural source constructor.
The original captured context stays fixed, including beneath a temporarily
masking handler; the child carries its prescribed caller and neutral path. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body ClauseBounds)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot EnteredHandler)

variable [declarations : DeclarationPolicy]
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {original : Context world owner outward actions phases base baseFront saved waiting}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {cut : OwnerCut owner whole front saved waiting} {before : Interfaces world front}
    {targetHints : Hints targetScope} {target : Forest targetHints}

/-- Handler source already contains its child at the prescribed new caller.
No check of dormant saved code at that intermediate caller is introduced. -/
theorem AtUse.handler_body
    {plans : ClausePlans clauses families} {bounds : ClauseBounds plans}
    {declared : declarations.accepts required plans} {body : Body world owner plan}
    (source : AtUse outward actions phases original
      (.handler (effect := effect) (table := table) bounds declared body) front) :
    AtUse outward actions phases original body
      (.handler (effect := effect) (table := table) (families := families) (required := required) front) := by
  cases source with | handler inner => exact inner

/-- Select the actual source body and retain its nested declaration proof and
finite checks. The saved/closing source context is the same original value. -/
def UseQueuedBody.handler_body
    {plans : ClausePlans clauses families} {bodyPlan : Plan dependencies}
    {bounds : Annotation world (.handler (effect := effect) (table := table) required plans bodyPlan)}
    (record : UseQueuedBody resumeRequired closeRequired original cut before bounds) :
    UseQueuedBody resumeRequired closeRequired original
      (.handler (effect := effect) (table := table) (families := families) (required := required) cut)
      (.handler _ before) bounds.handlerBody := by
  rcases record with ⟨body, rfl, source, nested, checked⟩
  cases body with
  | handler bounds declared child =>
      refine ⟨child, rfl, source.handler_body, ?_, checked.2⟩
      cases nested with | handler declarations admitted inner => exact inner

/-- The entered handler is added to both the source receiver and its actual
neutral expansion. Existing expansion congruence preserves the path. -/
def UseReceiverBody.handler_body
    {plans : ClausePlans clauses families} {bodyPlan : Plan dependencies}
    {bounds : Annotation world (.handler (effect := effect) (table := table) required plans bodyPlan)}
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds) :
    UseReceiverBody resumeRequired closeRequired original
      (.handler (effect := effect) (table := table) (families := families) (required := required) cut)
      (.handler _ before)
      (.handler (effect := effect) (table := table) (families := families) (required := required) target)
      bounds.handlerBody := ⟨record.source.handler_body, .handler record.receiver⟩

/-- The runtime entry determines the child and its exact snapshot. Actual
clause-plan witnesses may differ by the existing signature equality; the body
source and original captured context are not replaced. -/
theorem UseReceiverBody.handler_entered
    {plans : ClausePlans clauses families} {plan : Plan dependencies}
    {bounds : Annotation world plan}
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds)
    (pending : SourceBoundSnapshots.Retained world target) {next : Snapshot world}
    (entered : EnteredHandler effect table required plans
      ⟨_, plan, bounds, _, _, target, pending⟩ next) :
    ∃ child : UseReceiverBody resumeRequired closeRequired original
      (.handler (effect := effect) (table := table) (families := families) (required := required) cut)
      (.handler _ before)
      (.handler (effect := effect) (table := table) (families := families) (required := required) target)
      next.current,
      next = ⟨_, next.plan, child.source.body.boundAnnotation, _, _,
        .handler (effect := effect) (table := table) (families := families) (required := required) target,
        .handler pending⟩ := by
  cases entered
  refine ⟨record.handler_body, ?_⟩
  rw [← record.handler_body.source.origin]

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.handler_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.handler_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.handler_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.handler_entered
