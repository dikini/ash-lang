import SourceConsumingReceiverGeneration
import SourceConsumingContextualCaptureExamples
import SourceConsumingAdmissionWorldExamples

/-! Receiver changes retain nonempty current-code bounds, nested fresh-resource
bodies and the exact capture snapshot. Rechecking also covers rich interception. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceScheduledSourceRechecking (Expression)

/-- Change the physical receiver with all three neutral insertion forms. The
source includes nested handlers, cleanup, resources and both consumption modes. -/
def receiver := Forest.spent (owner := 88) (.plain .pure (.cleanup (needs := []) .pure Examples.whole))

theorem nested_generated : ∃ annotation : Code [4] HandlerExamples.wrapped receiver,
    annotation.Valid [] Examples.actions Examples.phases ∧
    SourcePlanBounds.ofCode annotation = HandlerExamples.wrappedBody.boundAnnotation :=
  HandlerExamples.wrapped_admitted.generate_expanding
    (HandlerExamples.wrapped_source.at_capture rfl rfl rfl) (.history (.extra (.completion .refl)))

/-- Rechecking a resource body under a changed outside receiver keeps the
explicit handler bounds for every future fresh identity. -/
def annotated : Code [] (.resource (fun _ => Plan.handler (effect := CaptureExamples.inner)
    (table := []) [] (.nil : SourceDeclarationPlans.ClausePlans .nil []) .pure)) .nil :=
  .resource (fun _ _ => .handler .nil (.operations [] .pure .pure) (some .nil))

theorem annotation_ready : annotated.Valid [] Examples.actions Examples.phases := fun _ _ => ⟨rfl, rfl⟩

theorem annotation_changed : Expression [] Examples.actions Examples.phases annotated
    (.spent (owner := 88) .nil) :=
  .resource (fun _ _ => .handler rfl (.operations rfl))

theorem rechecked_bounds : ∃ annotation : Code [] (.resource (fun _ => Plan.handler (effect := CaptureExamples.inner)
    (table := []) [] (.nil : SourceDeclarationPlans.ClausePlans .nil []) .pure)) (.spent (owner := 88) .nil),
    annotation.Valid [] Examples.actions Examples.phases ∧
    SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode annotated :=
  annotation_changed.compile_retaining (recipeLaws []) (fun evidence => evidence) annotation_ready

/-- Fresh interception with a continuation-using callback uses the strengthened
compiler as well. Current request bounds are absent; closing evidence is derived. -/
theorem rich_rechecked_bounds : ∃ annotation : Code [] (.request
    (effect := SourceDependencyCapture.Examples.effectE) (operation := 0)) SourceScheduledSourceRechecking.Examples.after,
    annotation.Valid [] SourceScheduledSourceRechecking.Examples.actions SourceScheduledSourceRechecking.Examples.phases ∧
    SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode SourceScheduledSourceRechecking.Examples.request :=
  SourceScheduledSourceRechecking.Examples.rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence)
    SourceScheduledSourceRechecking.Examples.request_valid

def waiting := Forest.spent (owner := 88) (.plain .pure .nil)
def captureForest := CaptureExamples.saved.append waiting

def snapshot : SourceBoundSnapshots.Snapshot [] := ⟨_, .request (effect := CaptureExamples.outer) (operation := 0),
  .absent, _, _, captureForest, .handler (.spent (.plain .absent .nil))⟩

theorem snapshot_ready : snapshot.Admitted := ⟨.absent .request, .handler (.spent (.plain (.absent .pure) .nil))⟩

theorem cut : SourceScheduledNeutral.Cut CaptureExamples.outer 0 CaptureExamples.offered
    (some CaptureExamples.family, some CaptureExamples.family) captureForest CaptureExamples.saved waiting := .hit rfl rfl

/-- Start with the earlier admitted receiver, not a target At assumption.
The actual request now has extra pending code and spent history in its tail. -/
theorem capture_generated : ∃ annotation : Code [] (CaptureExamples.bodies 19)
    (.live (owner := 19) CaptureExamples.saved waiting),
    (SourceScheduledCaptureAnnotations.Capture.site cut CaptureExamples.selected annotation).Valid []
      CaptureExamples.actions CaptureExamples.phases ∧
    SourcePlanBounds.ofCode annotation = (CaptureExamples.body 19).boundAnnotation ∧
    (SourcePlanBounds.ofCode annotation).Admitted ∧
    SourceBoundSnapshots.CapturedBounds snapshot 19 (CaptureExamples.bodies 19)
      (.live (owner := 19) CaptureExamples.saved waiting) := by
  apply SelectedSource.capture_expanding snapshot snapshot_ready CaptureExamples.bounded cut
    CaptureExamples.selected CaptureExamples.selected_source CaptureExamples.contextual
    (resumeRequired := []) (closeRequired := [])
  · rw [Context.before_nil]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact .live (.history (.extra .refl))

/-- A masking handler changes operation interpretation and cannot be justified
as a neutral receiver expansion. -/
theorem masking_not_neutral : ¬ SourceScheduledNeutral.Expansion
    (Forest.spent (owner := 19) HandlerExamples.waiting)
    (.handler (effect := SourceDependencyCapture.Examples.effectE) (table := []) (families := []) (required := [])
      (.spent (owner := 19) HandlerExamples.waiting)) := by
  intro changed
  have impossible := changed.erase.requirements (required := [(SourceDependencyCapture.Examples.effectE, 0)])
  change true = false at impossible
  cases impossible

end Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples.nested_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples.annotation_ready
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples.annotation_changed
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples.rechecked_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples.rich_rechecked_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples.snapshot_ready
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples.cut
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples.capture_generated

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverExamples.masking_not_neutral
