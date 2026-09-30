import SourceScheduledReceiverTransport
import SourceConsumingEntryBounds
import SourceConsumingBoundTransport
import SourceNeutralScopes
import SourceScheduledRecheckingPhases

/-! Phase preservation for contextual consuming-source admission. Existing
owner-cut inclusions delimit which availability facts matter. Exact annotation
and rechecking transport retain structural evidence at the new phases. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceDependencyOwners (owners)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws resumed_phases disposed_phases)
open SourceScheduledPhaseRestriction (AvailableOn)
open OwnerPhaseTransitions (spend)

-- realized_available is defined upstream in SourceDependencySchemes and is
-- shared with the lexical unwind preservation proof.

/-- Spending an owner outside the recursively retained source cannot alter
availability at any owner that this source can observe. -/
theorem absent_available (absent : retired ∉ owners scope) :
    AvailableOn (owners scope) phases (spend phases retired) := by
  intro name member ready
  rw [OwnerPhaseTransitions.spend_other (show name ≠ retired from fun same => absent (same ▸ member))]
  exact ready

variable [declarations : DeclarationPolicy]
  {wholeScope frontScope savedScope waitingScope : Scope}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}

/-- Keep every original annotation value and change only its phase-validity
proof. Cut, caller, protection and operation checks remain identical. -/
def Context.restrict_phases
    (context : Context world owner outward actions phases whole front saved waiting)
    (extension : AvailableOn (owners wholeScope) phases next) :
    Context world owner outward actions next whole front saved waiting where
  cut := context.cut
  before := context.before
  resumption := fun permission => ⟨(context.resumption permission).val,
    (context.resumption permission).val.restrict_phases (context.resumption permission).property
      (resumed_phases context.cut extension)⟩
  closing := fun permission => ⟨(context.closing permission).val,
    (context.closing permission).val.restrict_phases (context.closing permission).property
      (disposed_phases context.cut extension)⟩
  disposal := context.disposal
  after := context.after
  tailReady := by
    apply context.after.restrict_phases context.tailReady
    apply (resumed_phases context.cut extension).weaken
    simp only [SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil]
    intro name member
    exact List.mem_append_right _ (List.mem_append_right _ member)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}
  {plan : Plan dependencies} {body : Body world owner plan}
  {context : Context world owner outward actions phases whole front saved waiting}

/-- Structural admission survives phase changes preserving availability of the
actual retained live owners. Rechecking transport handles rich callbacks;
annotation-witness congruence reconciles existing existential compilers. -/
theorem At.restrict_phases (admitted : At laws project body context)
    (extension : AvailableOn (owners wholeScope) phases next) :
    At laws project body (context.restrict_phases extension) := by
  induction admitted with
  | resume => exact .resume
  | dispose => exact .dispose
  | sequence body ih => exact .sequence (ih extension)
  | choice first second ihFirst ihSecond => exact .choice (ihFirst extension) (ihSecond extension)
  | handler bounds declared resumption closing body ih =>
      rename_i current
      apply At.handler (context := current.restrict_phases extension) bounds declared
        (fun permission => (resumption permission).restrict_phases (resumed_phases current.cut extension))
        (fun permission => (closing permission).restrict_phases (disposed_phases current.cut extension))
      refine At.sameReceiver
        (original := (current.handler laws project _ _ _ _ resumption closing).restrict_phases extension)
        rfl ?_ (ih extension)
      constructor <;> (first | intro permission | skip) <;>
        simp only [Context.restrict_phases, Context.handler_resumption_bounds, Context.handler_closing_bounds, Context.handler_tail_bounds]

  | cleanupSource covered resumption closing body ih =>
      rename_i current footprint declared
      apply At.cleanupSource (context := current.restrict_phases extension) covered
        (fun permission => (resumption permission).restrict_phases (resumed_phases current.cut extension))
        (fun permission => (closing permission).restrict_phases (disposed_phases current.cut extension))
      refine At.sameReceiver
        (original := (current.cleanupSource laws project footprint declared _ resumption closing).restrict_phases extension)
        rfl ?_ (ih extension)
      constructor <;> (first | intro permission | skip) <;>
        simp only [Context.restrict_phases, Context.cleanupSource_resumption_bounds, Context.cleanupSource_closing_bounds, Context.cleanupSource_tail_bounds]

  | sameReceiver caller metadata source ih =>
      refine .sameReceiver caller ?_ (ih extension)
      exact ⟨fun permission => metadata.resumption _, fun permission => metadata.closing _, metadata.tail⟩
  | neutral receiver caller metadata source ih =>
      refine .neutral receiver caller ?_ (ih (by simpa only [receiver.erase.owners] using extension))
      exact ⟨fun permission => metadata.resumption _, fun permission => metadata.closing _, metadata.tail⟩
  | waitingNeutral receiver caller waitingChange metadata tail source ih =>
      refine .waitingNeutral receiver caller waitingChange ?_ tail (ih (by simpa only [receiver.erase.owners] using extension))
      exact ⟨fun permission => metadata.resumption _, fun permission => metadata.closing _⟩
  | resource body ih =>
      rename_i current
      apply At.resource
      intro identity fresh
      refine At.sameReceiver
        (original := (current.resource laws project identity).restrict_phases extension)
        rfl ?_ (ih identity fresh extension)

      constructor <;> (first | intro permission | skip) <;>
        simp only [Context.restrict_phases, Context.resource_resumption_bounds, Context.resource_closing_bounds, Context.resource_tail_bounds]

/-- Phase transport also permits a different valid annotation witness at the
same physical receiver, unchanged caller interface and equal retained metadata. -/
theorem At.restrict_to (admitted : At laws project body context)
    (extension : AvailableOn (owners wholeScope) phases next)
    (current : Context world owner outward actions next whole front saved waiting)
    (caller : context.before = current.before)
    (metadata : (context.restrict_phases extension).BoundsAgree current) : At laws project body current :=
  .sameReceiver caller metadata (admitted.restrict_phases extension)

/-- Reuse the finite-bound transport and existing generation theorem. Both
source admission and finite checks are now derived at the changed phases. -/
theorem At.scheduled_restrict (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before)
    (extension : AvailableOn (owners wholeScope) phases next) :
    SourceScheduledChecks.Local outward actions next world plan whole := by
  apply (admitted.restrict_phases extension).scheduled
  exact body.boundCheck_owner_transport checked rfl
    (extension owner (SourceScheduledPhaseRestriction.selected_owner
      (SourceContextualInvocationHints.selected_cut context.cut.found)))

/-- Use actual stack ownership to preserve admission at the runtime's phase
map. The same source forest must realize that stack; this cannot retire an
owner still reachable by the saved source. -/
theorem At.at_runtime_phases (admitted : At laws project body context)
    (realized : SourceDependencyCapture.Realizes tables families wholeScope stack) :
    At laws project body (context.restrict_phases (realized_available realized)) :=
  admitted.restrict_phases (realized_available realized)

theorem At.scheduled_at_runtime_phases (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before)
    (realized : SourceDependencyCapture.Realizes tables families wholeScope stack) :
    SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ScopedExecution.ownedTickets stack))
      world plan whole :=
  admitted.scheduled_restrict checked (realized_available realized)

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.restrict_phases
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.restrict_to
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.scheduled_restrict

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.at_runtime_phases
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.scheduled_at_runtime_phases

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.absent_available
