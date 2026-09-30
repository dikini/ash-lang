import SourceConsumingUseQueued
import SourceScheduledNeutralComposition

/-! Retain the source record and a structural neutral path to its actual
receiver. This reuses neutral compilation instead of requiring fresh AtUse
derivations after administrative frames are inserted. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)
open SourceScheduledNeutral (OwnerCut Expansion)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot Returned)

variable [declarations : DeclarationPolicy]

/-- Original source and actual receiver are related by an explicit structural
expansion. This evidence cannot insert a different interpretation. -/
structure UseReceiverBody (resumeRequired closeRequired : List SourceContextualHints.Requirement)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (original : Context world owner outward actions phases base baseFront saved waiting)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    (cut : OwnerCut owner whole front saved waiting) (before : Interfaces world front)
    {targetHints : Hints targetScope} (target : Forest targetHints)
    {plan : Plan dependencies} (bounds : Annotation world plan) where
  source : UseQueuedBody resumeRequired closeRequired original cut before bounds
  receiver : Expansion whole target

variable
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {original : Context world owner outward actions phases base baseFront saved waiting}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {cut : OwnerCut owner whole front saved waiting} {before : Interfaces world front}
    {targetHints : Hints targetScope} {target : Forest targetHints}
    {plan : Plan dependencies} {bounds : Annotation world plan}

def UseQueuedBody.at_receiver
    (source : UseQueuedBody resumeRequired closeRequired original cut before bounds) :
    UseReceiverBody resumeRequired closeRequired original cut before whole bounds := ⟨source, .refl⟩

/-- Successive neutral changes compose using the established stack relation. -/
def UseReceiverBody.expand
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds)
    {nextHints : Hints nextScope} {next : Forest nextHints} (changed : Expansion target next) :
    UseReceiverBody resumeRequired closeRequired original cut before next bounds :=
  ⟨record.source, record.receiver.trans changed⟩

def UseReceiverBody.plug
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds)
    (position : SourceAnnotatedCode.Context) :
    UseReceiverBody resumeRequired closeRequired original cut before target (bounds.plug position).2.2 :=
  ⟨record.source.plug position, record.receiver⟩

theorem UseReceiverBody.returned
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds)
    (position : SourceAnnotatedCode.Context)
    {currentPlan : Plan currentDependencies} (current : Annotation world currentPlan)
    (pending : SourceBoundSnapshots.Retained world target) {next : Snapshot world}
    (step : Returned position
      ⟨_, currentPlan, current, _, _, .plain plan target, .plain bounds pending⟩ next) :
    ∃ nextRecord : UseReceiverBody resumeRequired closeRequired original cut before target (bounds.plug position).2.2,
      next = ⟨_, _, nextRecord.source.body.boundAnnotation, _, _, target, pending⟩ := by
  refine ⟨record.plug position, ?_⟩
  cases step
  rw [← (record.plug position).source.origin]
  rfl

theorem UseReceiverBody.generate
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds) :
    ∃ annotation : Code world plan target,
      annotation.Valid outward actions phases ∧ SourcePlanBounds.ofCode annotation = bounds :=
  record.source.generate_expanding laws project record.receiver

/-- The existing focus split is kept together with its actual receiver path. -/
structure UseReceiverFocused (resumeRequired closeRequired : List SourceContextualHints.Requirement)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (original : Context world owner outward actions phases base baseFront saved waiting)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    (cut : OwnerCut owner whole front saved waiting) (before : Interfaces world front)
    {targetHints : Hints targetScope} (target : Forest targetHints)
    {child : Plan childDependencies} {rest : Plan restDependencies}
    (childBounds : Annotation world child) (restBounds : Annotation world rest) : Prop where
  source : UseFocusedSource resumeRequired closeRequired original cut before childBounds restBounds
  receiver : Expansion whole target

theorem UseReceiverBody.focused
    (record : UseReceiverBody resumeRequired closeRequired original cut before target bounds)
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (step : SourcePlanBounds.Focused world bounds childBounds restBounds) :
    UseReceiverFocused resumeRequired closeRequired original cut before target childBounds restBounds :=
  ⟨record.source.focused step, record.receiver⟩

theorem UseReceiverFocused.queued_body
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (focused : UseReceiverFocused resumeRequired closeRequired original cut before target childBounds restBounds)
    (restBody : Body world owner rest) :
    Nonempty (UseReceiverBody resumeRequired closeRequired original cut before target restBounds) := by
  obtain ⟨source⟩ := focused.source.queued_body restBody
  exact ⟨source, focused.receiver⟩

/-- In the current-body case the actual child runs beneath a pure pending
frame. That frame is retained in the receiver relation of its source record. -/
theorem UseReceiverFocused.current_body
    {child : Plan childDependencies} {childBounds : Annotation world child}
    (focused : UseReceiverFocused resumeRequired closeRequired original cut before target
      childBounds (.absent (plan := .pure))) :
    Nonempty (UseReceiverBody resumeRequired closeRequired original cut before (.plain .pure target) childBounds) := by
  obtain ⟨source⟩ := focused.source.current_body
  exact ⟨source, .extra focused.receiver⟩

theorem UseReceiverFocused.child_valid
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (focused : UseReceiverFocused resumeRequired closeRequired original cut before target childBounds restBounds) :
    ∃ annotation : Code world child (.plain rest target),
      annotation.Valid outward actions phases ∧ SourcePlanBounds.ofCode annotation = childBounds := by
  obtain ⟨code, ready, aligned⟩ := focused.source.child_valid laws project
  obtain ⟨annotation, valid, kept⟩ := code.expand_retaining laws project ready (.plain focused.receiver)
  exact ⟨annotation, valid, kept.trans aligned⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.at_receiver
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.expand
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.plug
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.returned
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.generate
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverBody.focused
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverFocused.queued_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverFocused.current_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseReceiverFocused.child_valid
