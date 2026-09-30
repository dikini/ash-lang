import SourceConsumingStoredBounds
import SourceAnnotatedRuntimeResumption

/-! Resumption moves the original handler packets with their saved and caller
segments. The selected live boundary becomes spent; bounds and declaration
routes are not reconstructed from fresh witnesses. -/
namespace Ash.OneShot.SourceConsumingStoredBounds
open SourceAnnotatedRuntime (Stack)

variable {families : SourceDependencyCapture.Families}
variable {front saved tail : Stack}

def StackBounds.resume
    (source : StackBounds families (front.append (.live owner input answer saved caller tail))) :
    StackBounds families (saved.append (front.append (.spent owner answer caller tail))) :=
  let pieces := source.splitAt front (.live owner input answer saved caller tail)
  match pieces.2 with
  | .live captured after => captured.append (pieces.1.append (.spent after))

/-- Exact data recomposition also preserves all dormant branches and proof
routes. It applies to any finite caller prefix, not just an immediate owner. -/
theorem StackBounds.resume_reconstructs
    (source : StackBounds families (front.append (.live owner input answer saved caller tail))) :
    ∃ before : StackBounds families front, ∃ captured : StackBounds families saved,
      ∃ after : StackBounds families tail,
        before.append (.live captured after) = source ∧
        source.resume = captured.append (before.append (.spent after)) := by
  have reconstruct := source.splitAt_append front (.live owner input answer saved caller tail)
  unfold StackBounds.resume
  generalize piecesKnown : source.splitAt front (.live owner input answer saved caller tail) = pieces at *
  rcases pieces with ⟨before, remaining⟩
  cases remaining with
  | live captured after => exact ⟨before, captured, after, reconstruct, rfl⟩

section
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem StackBounds.Admitted.resume
    {source : StackBounds families (front.append (.live owner input answer saved caller tail))}
    (admitted : source.Admitted world required) : source.resume.Admitted world required := by
  obtain ⟨before, remaining⟩ := admitted.splitAt front (.live owner input answer saved caller tail)
  unfold StackBounds.resume
  generalize piecesKnown : source.splitAt front (.live owner input answer saved caller tail) = pieces at *
  rcases pieces with ⟨first, second⟩
  cases second with
  | live captured after => cases remaining with
    | live savedChecked tailChecked => exact savedChecked.append (before.append (.spent tailChecked))

/-- The existing raw rule consumes the same owner and uses exactly the stack
whose packet admission was reconstructed above. Other runtime invariants are
supplied by the established resumption theorem, not asserted here. -/
theorem StackBounds.Admitted.resume_executes
    {source : StackBounds families (front.append (.live owner input answer saved caller tail))}
    (admitted : source.Admitted world required)
    (value : SourceAnnotatedCode.Term) (closed : ScopedExpressions.ClosedValue value.erase)
    (resolve : scope.resolve binder = some owner) :
    ScopedExecution.RawStep
      ⟨.resume binder value.erase, scope, (front.append (.live owner input answer saved caller tail)).erase⟩
      ⟨value.erase, scope, (saved.append (front.append (.spent owner answer caller tail))).erase⟩ [] [.ticket owner] ∧
    source.resume.Admitted world required := by
  constructor
  · simpa only [Stack.erase_append, Stack.erase] using
      ScopedExecution.RawStep.resume binder owner scope caller input answer front.erase saved.erase tail.erase
        value.erase closed resolve
  · exact admitted.resume

end
end Ash.OneShot.SourceConsumingStoredBounds

namespace Ash.OneShot.SourceAnnotatedRuntimeResumption
open SourceScheduledSavedPlans (Saved)
open SourceConsumingStoredBounds (StackBounds)
open ScopedExecution (ownedTickets)
open OwnerPhaseTransitions (Trace available)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
variable {front capture tail : SourceAnnotatedRuntime.Stack}

/-- Combine exact packet transport with the established full-state resumption
proof. The source, ownership trace and metadata refer to the same successor. -/
theorem resume_cut_preserves_bounds [SourceScheduledChecks.DeclarationProjection admission certification]
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.resume hint binder value) (front.append (.live owner inputType answerType capture caller tail))
      forest output demand row evidence)
    (stored : StackBounds families (front.append (.live owner inputType answerType capture caller tail)))
    (admitted : stored.Admitted world required)
    (resolved : scope.resolve binder = some owner) (closed : ScopedExpressions.ClosedValue value.erase) :
    ∃ remaining, ∃ nextForest : Saved,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        scope value (capture.append (front.append (.spent owner answerType caller tail))) nextForest.forest output remaining row evidence ∧
      stored.resume.Admitted world required ∧
      demand = owner :: remaining ∧
      Trace (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase caller tail.erase)))) [owner]
        (available (ownedTickets (capture.erase.append (front.erase.append (.spent owner answerType caller tail.erase))))) := by
  obtain ⟨remaining, nextForest, next, demandSame, trace⟩ := resume_cut_preserves state resolved closed
  exact ⟨remaining, nextForest, next, admitted.resume, demandSame, trace⟩

end Ash.OneShot.SourceAnnotatedRuntimeResumption

#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.resume_reconstructs
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.resume
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.resume_executes
#print axioms Ash.OneShot.SourceAnnotatedRuntimeResumption.resume_cut_preserves_bounds
