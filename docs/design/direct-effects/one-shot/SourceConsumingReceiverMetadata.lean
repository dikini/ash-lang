import SourceConsumingCleanupAdmission
import SourceScheduledReceiverRechecking

/-! Contextual rechecking with exact retained metadata. Physical receiver
changes are checked structurally; metadata agreement is independent of scope
shape and is not inferred from validity alone. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Retained DeclarationPolicy DeclarationLaws)
open SourceScheduledSourceRechecking (ReceiverChange)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceBoundSnapshots.Retained (ofCapability)
open OwnerPhaseTransitions (spend)

variable [declarations : DeclarationPolicy]

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- A source-derived context at a changed caller keeps all its retained bounds.
Only actual source rechecking and the target physical cut/caller interface are
inputs; target code validity is constructed by the existing compilers. -/
theorem Context.recheck_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (original : Context world owner outward actions phases whole front saved waiting)
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    (cut : SourceScheduledNeutral.OwnerCut owner nextWhole nextFront saved waiting)
    (caller : Interfaces world nextFront)
    (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (original.resumption permission).val (nextFront.append (.spent (owner := owner) waiting)))
    (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
      (original.closing permission).val (.running (nextFront.append (.spent (owner := owner) waiting)))) :
    ∃ current : Context world owner outward actions phases nextWhole nextFront saved waiting,
      current.before = caller ∧ original.BoundsAgree current := by
  have resumeGenerated := fun permission =>
    (resumption permission).compile_retaining laws project (original.resumption permission).property
  have closeGenerated := fun permission =>
    (closing permission).compile_retaining laws project (original.closing permission).property
  let current : Context world owner outward actions phases nextWhole nextFront saved waiting := {
    cut := cut
    before := caller
    resumption := fun permission => ⟨Classical.choose (resumeGenerated permission), (Classical.choose_spec (resumeGenerated permission)).1⟩
    closing := fun permission => ⟨Classical.choose (closeGenerated permission), (Classical.choose_spec (closeGenerated permission)).1⟩
    disposal := original.disposal
    after := original.after
    tailReady := original.tailReady }
  exact ⟨current, rfl, fun permission => (Classical.choose_spec (resumeGenerated permission)).2,
    fun permission => (Classical.choose_spec (closeGenerated permission)).2, rfl⟩


end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.recheck_retaining
