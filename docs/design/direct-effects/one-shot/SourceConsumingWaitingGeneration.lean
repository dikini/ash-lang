import SourceConsumingWaitingContext

/-! Admit and generate consuming source at a neutrally changed waiting tail.
Saved continuation metadata stays exact; target tail provenance is supplied by
the structural context transport, not by equality of different forest indices. -/
namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledNeutral (Expansion)

/-- Choose the interface already constructed by structural neutral transport.
This choice introduces no target-check or target-admission premise. -/
noncomputable def Interfaces.expand_neutral_source
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    (source : Interfaces world before) (changed : Expansion before after) :
    Interfaces world after := Classical.choose (source.expand_neutral changed)

/-- Expand a retained caller and its outside together, reusing the separate
interface and outside-check transport theorems. Equality includes failed checks. -/
theorem Interfaces.expand_neutral_source_check
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {outside : Forest outsideHints} {next : Forest nextHints}
    (source : Interfaces world before) (changed : Expansion before after)
    (receiver : Expansion outside next) :
    source.check outsideScope = (source.expand_neutral_source changed).check nextScope := by
  exact (source.check_neutral receiver).trans
    (Classical.choose_spec (source.expand_neutral changed) next).symm

end Ash.OneShot.SourceScheduledRetainedInterfaces

namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body Generated)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)
open SourceScheduledNeutral (Expansion OwnerCut)
open SourceScheduledRetainedInterfaces (Interfaces)

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

/-- The structural waiting rule constructs target source evidence from the
original derivation and the context transport's proved metadata relations. -/
theorem At.expand_waiting
    {body : Body world owner plan}
    {original : Context world owner outward actions phases whole front saved waiting}
    (source : At laws project body original)
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWaitingHints : Hints nextWaitingScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    {nextWaiting : Forest nextWaitingHints}
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (before : Interfaces world nextFront)
    (receiver : Expansion whole nextWhole) (caller : Expansion front nextFront)
    (waitingChange : Expansion waiting nextWaiting) :
    At laws project body (original.expand_waiting laws project cut before caller waitingChange) :=
  .waitingNeutral receiver caller waitingChange
    (original.expand_waiting_saved laws project cut before caller waitingChange)
    (original.expand_waiting_tail laws project cut before caller waitingChange) source

/-- Preserve the entire queued source record at the new waiting forest.
Independent finite checks follow from the original record and actual caller
check equality, without target admission or target code-validity premises. -/
noncomputable def QueuedBody.expand_waiting
    {original : Context world owner outward actions phases whole front saved waiting}
    {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired original bounds)
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWaitingHints : Hints nextWaitingScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    {nextWaiting : Forest nextWaitingHints}
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (before : Interfaces world nextFront)
    (receiver : Expansion whole nextWhole) (caller : Expansion front nextFront)
    (waitingChange : Expansion waiting nextWaiting)
    (sameCheck : original.before.check (.spent owner waitingScope) = before.check (.spent owner nextWaitingScope)) :
    QueuedBody laws project resumeRequired closeRequired
      (original.expand_waiting laws project cut before caller waitingChange) bounds :=
  ⟨queued.body, queued.origin, queued.source.expand_waiting cut before receiver caller waitingChange,
    queued.nested, queued.body.boundCheck_neutral_waiting waitingChange.erase receiver.erase caller.erase sameCheck queued.checked⟩

theorem QueuedBody.expand_waiting_body
    {original : Context world owner outward actions phases whole front saved waiting}
    {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired original bounds)
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWaitingHints : Hints nextWaitingScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    {nextWaiting : Forest nextWaitingHints}
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (before : Interfaces world nextFront)
    (receiver : Expansion whole nextWhole) (caller : Expansion front nextFront)
    (waitingChange : Expansion waiting nextWaiting)
    (sameCheck : original.before.check (.spent owner waitingScope) = before.check (.spent owner nextWaitingScope)) :
    (queued.expand_waiting cut before receiver caller waitingChange sameCheck).body = queued.body := rfl

/-- Reconstruct the actual context with a derived caller interface. Only the
physical cut and structural expansions are supplied at the new receiver. -/
noncomputable def Context.restore_neutral
    (original : Context world owner outward actions phases whole front saved waiting)
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWaitingHints : Hints nextWaitingScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    {nextWaiting : Forest nextWaitingHints}
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (caller : Expansion front nextFront) (waitingChange : Expansion waiting nextWaiting) :
    Context world owner outward actions phases nextWhole nextFront saved nextWaiting :=
  original.expand_waiting laws project cut (original.before.expand_neutral_source caller) caller waitingChange

/-- Full source restoration needs neither a supplied target caller interface
nor an equality of its checks. Both follow from the existing neutral transport. -/
noncomputable def QueuedBody.restore_neutral
    {original : Context world owner outward actions phases whole front saved waiting}
    {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired original bounds)
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWaitingHints : Hints nextWaitingScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    {nextWaiting : Forest nextWaitingHints}
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (receiver : Expansion whole nextWhole) (caller : Expansion front nextFront)
    (waitingChange : Expansion waiting nextWaiting) :
    QueuedBody laws project resumeRequired closeRequired
      (original.restore_neutral (laws := laws) (project := project) cut caller waitingChange) bounds :=
  queued.expand_waiting cut (original.before.expand_neutral_source caller) receiver caller waitingChange
    (original.before.expand_neutral_source_check caller (.spent waitingChange))

/-- Derive the target context, finite checks and valid source from the original
derivation. Saved/closing bounds are exact and tail bounds have an explicit
neutral provenance relation. The source rule above retains target admission. -/
theorem At.generate_expanded_waiting
    {body : Body world owner plan}
    {original : Context world owner outward actions phases whole front saved waiting}
    (source : At laws project body original)
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWaitingHints : Hints nextWaitingScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    {nextWaiting : Forest nextWaitingHints}
    (cut : OwnerCut owner nextWhole nextFront saved nextWaiting)
    (before : Interfaces world nextFront)
    (receiver : Expansion whole nextWhole) (caller : Expansion front nextFront)
    (waitingChange : Expansion waiting nextWaiting)
    (sameCheck : original.before.check (.spent owner waitingScope) = before.check (.spent owner nextWaitingScope))
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope original.before) :
    let current := original.expand_waiting laws project cut before caller waitingChange
    original.SavedAgree current ∧
      SourceBoundSnapshots.Retained.Neutral world (SourceBoundSnapshots.Retained.ofCapability original.after)
        (SourceBoundSnapshots.Retained.ofCapability current.after) ∧
      ∃ annotation : Code world plan nextWhole, annotation.Valid outward actions phases ∧
        Generated actions current.continuationBounds body annotation := by
  let current := original.expand_waiting laws project cut before caller waitingChange
  have kept := original.expand_waiting_saved laws project cut before caller waitingChange
  refine ⟨kept, original.expand_waiting_tail laws project cut before caller waitingChange, ?_⟩
  exact source.generate_waiting_source current caller waitingChange kept
    (body.boundCheck_neutral_waiting waitingChange.erase receiver.erase caller.erase sameCheck checked)

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate_expanded_waiting
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.expand_waiting
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.expand_waiting
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.expand_waiting_body

#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.expand_neutral_source
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.expand_neutral_source_check
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.restore_neutral
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.restore_neutral
