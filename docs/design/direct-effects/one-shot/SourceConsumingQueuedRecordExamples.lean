import SourceBoundRecords
import SourceConsumingQueuedAdmissionExamples

/-! Exact record movement with actual queued source derivations. Distinct tags
make order observable even when positions have identical bound annotations.
These are decorated snapshot examples, not whole typed executions: the stored
contexts remain original and are not asserted valid at the moving positions. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples
open SourceDeclarationPlans (Plan)
open SourceBoundSnapshots
open SourceScheduledCapabilityAnnotations (recipeLaws)

/-- Obtain the source record from the existing effectful focus proof. -/
noncomputable def source := Classical.choice
  (QueuedExamples.effectful_focus.queued_body HandlerExamples.body)

abbrev Payload : RecordFamily [] := fun bounds => Nat × Option
  (QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] HandlerExamples.context bounds)

def bodyBounds : Retained [] (.plain HandlerExamples.clause .nil) :=
  .plain HandlerExamples.body.boundAnnotation .nil
noncomputable def bodyRecord (tag : Nat) : bodyBounds.Records Payload :=
  .plain (tag, some source) .nil

/-- The saved side includes a dormant capture and an operation-free callback.
The callback's optional payload is absent; this is not a source-coverage claim. -/
def savedBounds : Retained []
    (.live (owner := 41) (.plain HandlerExamples.clause .nil)
      (.cleanup (needs := []) Plan.pure (.plain HandlerExamples.clause .nil))) :=
  .live bodyBounds (.cleanup .absent bodyBounds)
noncomputable def savedRecords : savedBounds.Records Payload :=
  .live (bodyRecord 11) (.cleanup (12, none) (bodyRecord 22))

def before : Snapshot [] :=
  ⟨_, Plan.pure, .absent, _, _, _, savedBounds.append bodyBounds⟩
def captured : Snapshot [] :=
  ⟨_, Plan.pure, .absent, _, _, _, .live (owner := 73) savedBounds bodyBounds⟩
noncomputable def beforeRecords : before.pending.Records Payload := savedRecords.append (bodyRecord 33)
noncomputable def capturedRecords : captured.pending.Records Payload := .live savedRecords (bodyRecord 33)

theorem capture_shape : Captured 73 before captured := .cut _ _ _ _
theorem exact_capture : RecordCapture 73 Payload beforeRecords capturedRecords := .cut _ _ _ _

theorem capture_constructs_records :
    ∃ records : captured.pending.Records Payload, RecordCapture 73 Payload beforeRecords records :=
  capture_shape.carry_records beforeRecords

def resumeBefore : Snapshot [] :=
  ⟨_, Plan.pure, .absent, _, _, _, bodyBounds.append (.live (owner := 73) savedBounds bodyBounds)⟩
def resumed : Snapshot [] :=
  Snapshot.value (savedBounds.append (bodyBounds.append (.spent (owner := 73) bodyBounds)))
noncomputable def resumeRecords : resumeBefore.pending.Records Payload := (bodyRecord 44).append capturedRecords
noncomputable def restoredRecords : resumed.pending.Records Payload :=
  savedRecords.append ((bodyRecord 44).append (.spent (bodyRecord 33)))

theorem resumption_shape : Resumed 73 resumeBefore resumed := .cut _ _ _ _
theorem exact_resumption : RecordResumption 73 Payload resumeRecords restoredRecords := .cut _ _ _ _
theorem resumption_constructs_records :
    ∃ records : resumed.pending.Records Payload, RecordResumption 73 Payload resumeRecords records :=
  resumption_shape.carry_records resumeRecords

/-- The same original payloads survive, including values in the dormant branch. -/
theorem captured_values : capturedRecords.entries = beforeRecords.entries := exact_capture.entries
theorem restored_values : resumeRecords.entries.Perm restoredRecords.entries := exact_resumption.entries

def tags (records : List (RecordEntry Payload)) : List Nat := records.map (fun record => record.payload.1)

theorem before_order : tags resumeRecords.entries = [44, 11, 12, 22, 33] := rfl
theorem restored_order : tags restoredRecords.entries = [11, 12, 22, 44, 33] := rfl

/-- Callback positions remain callbacks even though their optional source
payload is absent. Dormant and caller code positions remain pending code. -/
theorem restored_positions : restoredRecords.entries.map (fun record => record.position) =
    [.pending, .callback, .pending, .pending, .pending] := rfl

/-- The actual source record recovered from the first restored dormant branch
can be used by the existing return theorem at its ORIGINAL context. No renewed
source admission is supplied and no changed-context admission is asserted. -/
noncomputable def restoredPayload : Payload HandlerExamples.body.boundAnnotation :=
  match restoredRecords with
  | .live (.plain payload .nil) _ => payload

noncomputable def restoredSource : QueuedBody (recipeLaws []) (fun evidence => evidence) [] []
    HandlerExamples.context HandlerExamples.body.boundAnnotation := restoredPayload.2.get (by rfl)

theorem restored_source_identity : restoredSource = source := rfl

theorem restored_return {next : Snapshot []}
    (pending : Retained [] HandlerExamples.whole)
    (step : Returned QueuedExamples.bindingPosition
      ⟨_, Plan.pure, .absent, _, _, _, .plain HandlerExamples.body.boundAnnotation pending⟩ next) :
    ∃ nextQueued : QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] HandlerExamples.context
        (HandlerExamples.body.boundAnnotation.plug QueuedExamples.bindingPosition).2.2,
      next = ⟨_, _, nextQueued.body.boundAnnotation, _, _, HandlerExamples.whole, pending⟩ :=
  restoredSource.returned QueuedExamples.bindingPosition (.absent (plan := Plan.pure)) pending step

end Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.capture_shape
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.exact_capture
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.capture_constructs_records
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.resumption_shape
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.exact_resumption
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.resumption_constructs_records
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.captured_values
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.restored_values
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.before_order
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.restored_order
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.restored_positions
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.restored_source_identity
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecordExamples.restored_return
