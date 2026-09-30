import SourceConsumingReceiverAdmission

/-! Restore consuming source at a non-neutral caller and waiting forest.
Original retained annotations are transformed by structural rechecking rules;
the existing compilers derive validity and metadata provenance. Runtime source
coverage must still derive these rules for each actual restoration. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledSourceRechecking (ReceiverChange RetainedChange RetainedBounds)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceConsumingClauseAnnotations (Generated)
open OwnerPhaseTransitions (spend)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
  {nextWaitingHints : Hints nextWaitingScope}
  {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
  {nextWaiting : Forest nextWaitingHints}

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
include laws project in
/-- The cut fixes the original saved forest. Its resumption and closing bounds
stay exact, while changed waiting metadata follows the existing structural
provenance relation. No target Context, At or Valid is an input. -/
theorem Context.recheck_waiting_retaining
    (original : Context world owner outward actions phases whole front saved waiting)
    (cut : SourceScheduledNeutral.OwnerCut owner nextWhole nextFront saved nextWaiting)
    (caller : Interfaces world nextFront)
    (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (original.resumption permission).val (nextFront.append (.spent (owner := owner) nextWaiting)))
    (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (original.closing permission).val (.running (nextFront.append (.spent (owner := owner) nextWaiting))))
    (tail : RetainedChange outward actions (spend phases owner) original.after nextWaiting .nil) :
    ∃ current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting,
      current.before = caller ∧ original.SavedAgree current ∧
      RetainedBounds original.after (ofCapability current.after) := by
  have resumeGenerated := fun permission =>
    (resumption permission).compile_retaining laws project (original.resumption permission).property
  have closeGenerated := fun permission =>
    (closing permission).compile_retaining laws project (original.closing permission).property
  obtain ⟨after, ready, provenance⟩ := tail.compile_retaining laws project original.tailReady
  let current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting := {
    cut := cut
    before := caller
    resumption := fun permission => ⟨Classical.choose (resumeGenerated permission), (Classical.choose_spec (resumeGenerated permission)).1⟩
    closing := fun permission => ⟨Classical.choose (closeGenerated permission), (Classical.choose_spec (closeGenerated permission)).1⟩
    disposal := original.disposal
    after := after
    tailReady := ready }
  exact ⟨current, rfl, ⟨fun permission => (Classical.choose_spec (resumeGenerated permission)).2,
    fun permission => (Classical.choose_spec (closeGenerated permission)).2⟩, provenance⟩

/-- General source-record reconstruction permits a changed waiting forest.
Entry interference and finite operation/owner checks stay explicit structural
obligations. Metadata alone is deliberately insufficient for admission. -/
def QueuedBody.recheck_waiting
    {original : Context world owner outward actions phases whole front saved waiting}
    {current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting}
    {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired original bounds)
    (metadata : original.SavedAgree current)
    (tail : RetainedBounds original.after (ofCapability current.after))
    (checks : ReceiverChecks laws (@project) actions phases queued.body current)
    (checked : queued.body.BoundCheck resumeRequired closeRequired actions phases
      nextWholeScope nextWaitingScope current.before) :
    { next : QueuedBody laws project resumeRequired closeRequired current bounds //
      next.body = queued.body ∧ original.SavedAgree current ∧
      RetainedBounds original.after (ofCapability current.after) } :=
  ⟨⟨queued.body, queued.origin, checks.reconstruct queued.source, queued.nested, checked⟩,
    rfl, metadata, tail⟩

/-- The reconstructed body generates at the actual current continuation bounds.
The changed waiting bounds are not identified with the old waiting bounds. -/
theorem QueuedBody.generate_rechecked_waiting
    {original : Context world owner outward actions phases whole front saved waiting}
    {current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting}
    {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired original bounds)
    (metadata : original.SavedAgree current)
    (tail : RetainedBounds original.after (ofCapability current.after))
    (checks : ReceiverChecks laws (@project) actions phases queued.body current)
    (checked : queued.body.BoundCheck resumeRequired closeRequired actions phases
      nextWholeScope nextWaitingScope current.before) :
    ∃ annotation : Code world plan nextWhole,
      annotation.Valid outward actions phases ∧
      Generated actions current.continuationBounds queued.body annotation :=
  (queued.recheck_waiting metadata tail checks checked).val.source.generate_source checked

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.recheck_waiting_retaining
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.recheck_waiting
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.generate_rechecked_waiting
