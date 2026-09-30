import SourceScheduledReceiverTransport
import SourceConsumingEntryBounds
import SourceConsumingBoundTransport
import SourceScheduledRecheckingWorld

/-! Contextual consuming-source admission is stable under resource-world
extension. Structural cleanup and handler rules transport their actual source
rechecking derivations; no newly chosen conditional checks are assumed. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations

/-- The source bound projection follows the same world extension as the
runtime snapshot metadata, including nested fresh-resource bodies. -/
theorem Body.boundAnnotation_world_weaken [SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {plan : SourceDeclarationPlans.Plan dependencies} (body : Body world owner plan) (larger : world ⊆ next) :
    (body.world_weaken larger).boundAnnotation = body.boundAnnotation.world_weaken larger := by
  induction body generalizing next <;>
    simp_all only [Body.world_weaken, Body.boundAnnotation, SourcePlanBounds.Annotation.world_weaken]

end Ash.OneShot.SourceConsumingClauseAnnotations

namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
open SourceScheduledRetainedInterfaces (Interfaces)

variable [declarations : DeclarationPolicy]
  {wholeScope frontScope savedScope waitingScope : Scope}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}

/-- Map the exact original annotations into a larger declaration world. The
physical owner cut, permissions, phases and disposal protection are unchanged. -/
def Context.world_weaken
    (context : Context world owner outward actions phases whole front saved waiting) (larger : world ⊆ next) :
    Context next owner outward actions phases whole front saved waiting where
  cut := context.cut
  before := context.before.world_weaken larger
  resumption := fun permission => ⟨(context.resumption permission).val.world_weaken larger,
    (context.resumption permission).val.world_weaken_valid larger (context.resumption permission).property⟩
  closing := fun permission => ⟨(context.closing permission).val.world_weaken larger,
    (context.closing permission).val.world_weaken_valid larger (context.closing permission).property⟩
  disposal := context.disposal
  after := context.after.world_weaken larger
  tailReady := context.after.world_weaken_valid larger context.tailReady

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}
  {plan : Plan dependencies} {body : Body world owner plan}
  {context : Context world owner outward actions phases whole front saved waiting}

/-- Every source constructor retains admission. Fresh-resource bodies reuse
world inclusion and interface weakening composition; handler/cleanup witnesses
are reconciled by the existing same-receiver rule. -/
theorem At.world_weaken (admitted : At laws project body context) (larger : world ⊆ next) :
    At laws project (body.world_weaken larger) (context.world_weaken larger) := by
  induction admitted generalizing next with
  | resume => exact .resume
  | dispose => exact .dispose
  | sequence body ih => exact .sequence (ih larger)
  | choice first second ihFirst ihSecond => exact .choice (ihFirst larger) (ihSecond larger)
  | handler bounds declared resumption closing body ih =>
      rename_i current
      apply At.handler (context := current.world_weaken larger) bounds declared
        (fun permission => (resumption permission).world_weaken larger)
        (fun permission => (closing permission).world_weaken larger)
      refine At.sameReceiver
        (original := (current.handler laws project _ _ _ _ resumption closing).world_weaken larger)
        rfl ?_ (ih larger)
      constructor <;> (first | intro permission | skip) <;>
        simp only [Context.world_weaken, SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken, Context.handler_resumption_bounds, Context.handler_closing_bounds, Context.handler_tail_bounds]

  | cleanupSource covered resumption closing body ih =>
      rename_i current footprint declared
      apply At.cleanupSource (context := current.world_weaken larger) covered
        (fun permission => (resumption permission).world_weaken larger)
        (fun permission => (closing permission).world_weaken larger)
      refine At.sameReceiver
        (original := (current.cleanupSource laws project footprint declared _ resumption closing).world_weaken larger)
        rfl ?_ (ih larger)
      constructor <;> (first | intro permission | skip) <;>
        simp only [Context.world_weaken, SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken, Context.cleanupSource_resumption_bounds, Context.cleanupSource_closing_bounds, Context.cleanupSource_tail_bounds]

  | sameReceiver caller metadata source ih =>
      refine At.sameReceiver (congrArg (fun before => before.world_weaken larger) caller) ?_ (ih larger)
      constructor
      · intro permission
        exact (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).trans
          ((congrArg (fun bounds => bounds.world_weaken larger) (metadata.resumption permission)).trans
            (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).symm)
      · intro permission
        exact (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).trans
          ((congrArg (fun bounds => bounds.world_weaken larger) (metadata.closing permission)).trans
            (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).symm)
      · exact (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).trans
          ((congrArg (fun bounds => bounds.world_weaken larger) metadata.tail).trans
            (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).symm)
  | neutral receiver caller metadata source ih =>
      refine At.neutral receiver caller ?_ (ih larger)
      constructor
      · intro permission
        exact (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).trans
          ((congrArg (fun bounds => bounds.world_weaken larger) (metadata.resumption permission)).trans
            (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).symm)
      · intro permission
        exact (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).trans
          ((congrArg (fun bounds => bounds.world_weaken larger) (metadata.closing permission)).trans
            (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).symm)
      · exact (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).trans
          ((congrArg (fun bounds => bounds.world_weaken larger) metadata.tail).trans
            (SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken _ _).symm)
  | waitingNeutral receiver caller waitingChange metadata tail source ih =>
      refine .waitingNeutral receiver caller waitingChange ?_ ?_ (ih larger)
      · constructor
        · intro permission
          simp only [Context.world_weaken, SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken]
          exact congrArg (fun bounds => bounds.world_weaken larger) (metadata.resumption permission)
        · intro permission
          simp only [Context.world_weaken, SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken]
          exact congrArg (fun bounds => bounds.world_weaken larger) (metadata.closing permission)
      · simpa only [Context.world_weaken, SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken]
          using tail.world_weaken larger
  | resource body ih =>
      rename_i current
      apply At.resource
      intro identity fresh
      have oldFresh := fun member => fresh (larger member)
      have extended := ScopedExpressions.append_subset larger (List.Subset.refl [identity])
      refine At.sameReceiver
        (original := (current.resource laws project identity).world_weaken extended) ?_ ?_ (ih identity oldFresh extended)
      · simp only [Context.world_weaken, Context.resource, Interfaces.world_weaken, Interfaces.world_weaken_trans]
      · constructor <;> (first | intro permission | skip) <;>
          simp only [Context.world_weaken, SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken,
            Context.resource_resumption_bounds, Context.resource_closing_bounds, Context.resource_tail_bounds] <;>
          simp only [← SourceScheduledCapabilityAnnotations.Retained.ofCapability_world_weaken,
            SourceScheduledCapabilityAnnotations.Retained.world_weaken_trans]

/-- A different witness at the same receiver can be used after world extension
when its caller and retained metadata agree with the weakened original. -/
theorem At.world_weaken_to (admitted : At laws project body context) (larger : world ⊆ next)
    (current : Context next owner outward actions phases whole front saved waiting)
    (caller : context.before.world_weaken larger = current.before)
    (metadata : (context.world_weaken larger).BoundsAgree current) :
    At laws project (body.world_weaken larger) current :=
  .sameReceiver caller metadata (admitted.world_weaken larger)

theorem At.scheduled_world_weaken (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before)
    (larger : world ⊆ next) : SourceScheduledChecks.Local outward actions phases next plan whole :=
  (admitted.world_weaken larger).scheduled (body.boundCheck_world_weaken larger checked)

/-- Generation in the larger world emits precisely the transported original
source bounds, which can be compared directly with an existing snapshot. -/
theorem At.generate_world_retaining (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before)
    (larger : world ⊆ next) :
    ∃ annotation : SourceScheduledCapabilityAnnotations.Code next plan whole,
      annotation.Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = body.boundAnnotation.world_weaken larger := by
  obtain ⟨annotation, valid, same⟩ :=
    (admitted.world_weaken larger).generate_retaining (body.boundCheck_world_weaken larger checked)
  exact ⟨annotation, valid, same.trans (body.boundAnnotation_world_weaken larger)⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.world_weaken
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.world_weaken_to
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.scheduled_world_weaken

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.boundAnnotation_world_weaken
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.generate_world_retaining
