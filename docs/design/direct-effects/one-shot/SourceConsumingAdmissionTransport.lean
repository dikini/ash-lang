import SourceConsumingAdmissionPermissions
import SourceConsumingAdmissionWorld

/-! Compose independent capability and resource-world transport. These results
retain the physical receiver and original source bounds; receiver changes have
separate structural obligations. No new induction or target validity premise
is needed. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceDependencyOwners (owners)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)
open SourceScheduledPhaseRestriction (AvailableOn)

variable [declarations : DeclarationPolicy]
  {wholeScope frontScope savedScope waitingScope : Scope}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}
  {plan : Plan dependencies} {body : Body world owner plan}
  {context : Context world owner outward actions phases whole front saved waiting}

/-- Each independent transport keeps the same cut and source derivation. -/
theorem At.transport (admitted : At laws project body context)
    (permissions : Syntax.UsageExtension actions nextActions) (same : actions owner = nextActions owner)
    (extension : AvailableOn (owners wholeScope) phases nextPhases) (larger : world ⊆ nextWorld) :
    At laws project (body.world_weaken larger)
      (((context.extend_permissions permissions same).restrict_phases extension).world_weaken larger) :=
  ((admitted.extend_permissions permissions same).restrict_phases extension).world_weaken larger

/-- Reuse a witness at the same receiver with the weakened original caller and
retained metadata. Source admission at that witness follows from transport. -/
theorem At.transport_to (admitted : At laws project body context)
    (permissions : Syntax.UsageExtension actions nextActions) (same : actions owner = nextActions owner)
    (extension : AvailableOn (owners wholeScope) phases nextPhases) (larger : world ⊆ nextWorld)
    (current : Context nextWorld owner outward nextActions nextPhases whole front saved waiting)
    (caller : context.before.world_weaken larger = current.before)
    (metadata : (((context.extend_permissions permissions same).restrict_phases extension).world_weaken larger).BoundsAgree current) :
    At laws project (body.world_weaken larger) current :=
  .sameReceiver caller metadata (admitted.transport permissions same extension larger)

/-- A checked body supplies its own known permission entry. Generate validity
and exact bound metadata after all three changes without assuming either at
the target. -/
theorem At.generate_transport_retaining (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before)
    (permissions : Syntax.UsageExtension actions nextActions)
    (extension : AvailableOn (owners wholeScope) phases nextPhases) (larger : world ⊆ nextWorld) :
    ∃ annotation : Code nextWorld plan whole,
      annotation.Valid outward nextActions nextPhases ∧
      SourcePlanBounds.ofCode annotation = body.boundAnnotation.world_weaken larger := by
  obtain ⟨rights, known⟩ := (body.boundCheck_owner checked).1
  have same := known.trans (permissions owner rights known).symm
  have available := extension owner (SourceScheduledPhaseRestriction.selected_owner
    (SourceContextualInvocationHints.selected_cut context.cut.found))
  exact ((admitted.extend_permissions permissions same).restrict_phases extension).generate_world_retaining
    (body.boundCheck_owner_transport checked same available) larger

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.transport
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.transport_to
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate_transport_retaining
