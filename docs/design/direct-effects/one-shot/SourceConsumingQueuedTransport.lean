import SourceConsumingQueuedAdmission
import SourceConsumingAdmissionTransport

/-! Queued source records survive independent permission, phase and world
changes by reusing the established source transport. The receiving forest is
fixed; capture/restoration under a different receiver is a separate obligation. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceDependencyOwners (owners)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (ClausePlans)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
open SourcePlanBounds (Annotation)
open SourceScheduledPhaseRestriction (AvailableOn)

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

/-- The annotation on the queued frame and its actual source body are weakened
together. Every original owner remains available where its evidence requires it. -/
def QueuedBody.transport {bounds : Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired context bounds)
    (permissions : Syntax.UsageExtension actions nextActions) (same : actions owner = nextActions owner)
    (extension : AvailableOn (owners wholeScope) phases nextPhases) (larger : world ⊆ nextWorld) :
    QueuedBody laws project resumeRequired closeRequired
      (((context.extend_permissions permissions same).restrict_phases extension).world_weaken larger)
      (bounds.world_weaken larger) := by
  refine ⟨queued.body.world_weaken larger, ?_, queued.source.transport permissions same extension larger,
    queued.nested.world_weaken larger, ?_⟩
  · exact (congrArg (fun bounds => bounds.world_weaken larger) queued.origin).trans
      (queued.body.boundAnnotation_world_weaken larger).symm
  · have available := extension owner (SourceScheduledPhaseRestriction.selected_owner
      (SourceContextualInvocationHints.selected_cut context.cut.found))
    exact queued.body.boundCheck_world_weaken larger
      (queued.body.boundCheck_owner_transport queued.checked same available)

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.transport
