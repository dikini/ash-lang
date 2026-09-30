import SourceConsumingPassiveReceiver
import SourceConsumingNeutralContext

/-! A pure focus frame preserves full contextual source admission when the
saved forest has no code positions or handler requirements. Both receiver
obligations and finite clause checks are derived from the original record.
SourceConsumingNeutralGeneration supplies the general pure-focus result for
saved code, callbacks and nonempty handler requirements. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
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
  {context : Context world owner outward actions phases whole front saved waiting}

/-- The entire current-source record is constructed at the expanded receiver.
No target ReceiverChecks, BoundCheck or source-admission premise is supplied. -/
noncomputable def QueuedBody.focus_passive {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired context bounds) (passive : PassiveSaved saved) :
    QueuedBody laws project resumeRequired closeRequired (context.pure_frame laws project) bounds :=
  (queued.recheck (context.pure_frame_bounds (laws := laws) (project := project))
    (ReceiverChecks.passive_saved queued.body passive (context.pure_frame laws project))
    (context.pure_frame_checked queued.checked)).val

theorem QueuedBody.focus_passive_body {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired context bounds) (passive : PassiveSaved saved) :
    (queued.focus_passive passive).body = queued.body := rfl

/-- The original focus split determines that the child remains consuming under
a pure pending frame. Its original record now yields contextual admission at
that ACTUAL child receiver, as well as its existing bound annotation. -/
theorem FocusedSource.current_passive
    {child : Plan childDependencies} {childBounds : SourcePlanBounds.Annotation world child}
    (focused : FocusedSource laws project resumeRequired closeRequired context
      childBounds (.absent (plan := Plan.pure))) (passive : PassiveSaved saved) :
    Nonempty (QueuedBody laws project resumeRequired closeRequired (context.pure_frame laws project) childBounds) := by
  obtain ⟨original⟩ := focused.current_body
  exact ⟨original.focus_passive passive⟩

/-- Generation after focus still corresponds to the original continuation
metadata. It reuses the established source compiler at the constructed context. -/
theorem QueuedBody.focus_passive_generated {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired context bounds) (passive : PassiveSaved saved) :
    ∃ annotation : SourceScheduledCapabilityAnnotations.Code world plan (.plain Plan.pure whole),
      annotation.Valid outward actions phases ∧
      SourceConsumingClauseAnnotations.Generated actions context.continuationBounds queued.body annotation := by
  obtain ⟨annotation, ready, generated⟩ := (queued.focus_passive passive).source.generate_source (queued.focus_passive passive).checked
  exact ⟨annotation, ready, by
    simpa only [queued.focus_passive_body passive, (context.pure_frame_bounds (laws := laws) (project := project)).continuationBounds_eq] using generated⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.focus_passive
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.focus_passive_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.FocusedSource.current_passive
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.focus_passive_generated
