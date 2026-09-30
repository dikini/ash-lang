import SourceConsumingWaitingGeneration
import SourceConsumingQueuedRecordExamples
import SourceConsumingNeutralGenerationExamples

/-! Capture/resumption changes an existing owner's waiting tail while preserving
its saved forest. Recover an actual queued source payload, then generate it at
the restored tail. These are exact snapshot/source examples, not a typed run. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples
open SourceDeclarationPlans (Plan)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceConsumingClauseAnnotations (Body Generated)
open SourceBoundSnapshots
open SourceDependencyCapture.Examples (effectE resumeTable resumeDependencies)
open SourceScheduledNeutral (Expansion)

def nextWaiting : Forest (Hints.handler (effect := effectE) (table := resumeTable)
    (families := resumeDependencies) [] (.spent (owner := 88) .nil)) := .handler (.spent .nil)
def nextWhole := Forest.live (owner := 19) HandlerExamples.saved nextWaiting

theorem waiting_change : Expansion HandlerExamples.waiting nextWaiting := .handler (.history .refl)
theorem receiver_change : Expansion HandlerExamples.whole nextWhole := .live waiting_change

noncomputable def current := HandlerExamples.context.expand_waiting (recipeLaws []) (fun evidence => evidence)
  (nextWhole := nextWhole) .hit .nil .refl waiting_change

def remaining : Retained [] HandlerExamples.whole := .live (.plain .absent .nil) (.handler .nil)
def capturedBounds : Retained [] (.plain HandlerExamples.clause HandlerExamples.whole) :=
  .plain HandlerExamples.body.boundAnnotation remaining
def before : Snapshot [] := ⟨_, Plan.request (effect := effectE) (operation := 0), .absent, _, _, _, capturedBounds⟩
def captured : Snapshot [] :=
  ⟨_, Plan.invoke (key := ⟨88, .resume⟩), .absent, _, _, _, .live (owner := 88) capturedBounds .nil⟩
def resumed : Snapshot [] := Snapshot.value (capturedBounds.append (.spent (owner := 88) .nil))

theorem actual_handler_cut : ∃ contract modes, SourceScheduledNeutral.Cut effectE 0 contract modes before.forest
    (.plain HandlerExamples.clause HandlerExamples.whole) .nil := ⟨_, _, .plain (.live (.hit rfl rfl))⟩

theorem capture_shape : Captured 88 before captured :=
  .cut (SourcePlanBounds.Annotation.absent (plan := Plan.request (effect := effectE) (operation := 0)))
    (SourcePlanBounds.Annotation.absent (plan := Plan.invoke (key := ⟨88, .resume⟩))) capturedBounds Retained.nil
theorem resumption_shape : Resumed 88 captured resumed := .cut _ .nil _ .nil

abbrev Payload : RecordFamily [] := fun bounds => Option
  (QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] HandlerExamples.context bounds)
def beforeRecords : before.pending.Records Payload :=
  .plain (some QueuedExamples.queued) (.live (.plain none .nil) (.handler .nil))
def capturedRecords : captured.pending.Records Payload := .live beforeRecords .nil
def resumedRecords : resumed.pending.Records Payload := beforeRecords.append (.spent .nil)

theorem exact_capture : RecordCapture 88 Payload beforeRecords capturedRecords :=
  .cut (SourcePlanBounds.Annotation.absent (plan := Plan.request (effect := effectE) (operation := 0)))
    (SourcePlanBounds.Annotation.absent (plan := Plan.invoke (key := ⟨88, .resume⟩))) beforeRecords .nil
theorem exact_resumption : RecordResumption 88 Payload capturedRecords resumedRecords := .cut _ .nil _ .nil

def restoredPayload : Payload HandlerExamples.body.boundAnnotation :=
  match resumedRecords with
  | .plain record _ => record

def restoredSource : QueuedBody (recipeLaws []) (fun evidence => evidence) [] []
    HandlerExamples.context HandlerExamples.body.boundAnnotation := restoredPayload.get (by rfl)

theorem restored_source_identity : restoredSource = QueuedExamples.queued := rfl

/-- This original source was recovered from the moved record. No new source or
finite-check premise is supplied at the changed waiting forest. -/
theorem restored_generated : ∃ annotation : Code [] HandlerExamples.clause nextWhole,
    annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
    Generated HandlerExamples.actions current.continuationBounds HandlerExamples.body annotation := by
  exact (restoredSource.source.generate_expanded_waiting (nextWhole := nextWhole)
    .hit .nil receiver_change .refl waiting_change rfl restoredSource.checked).2.2

theorem exact_waiting_bounds : Retained.ofCapability current.after =
    (Retained.handler (Retained.spent (owner := 88) Retained.nil) : Retained [] nextWaiting) := by
  cases Retained.ofCapability current.after with
  | handler tail => cases tail with
      | spent rest => cases rest; rfl

def returned : Snapshot [] :=
  ⟨_, Plan.sequence Plan.pure HandlerExamples.clause,
    .sequence .absent HandlerExamples.body.boundAnnotation, _, _, nextWhole,
    .live (.plain .absent .nil) (.handler (.spent (owner := 88) .nil))⟩

theorem return_shape : Returned QueuedExamples.bindingPosition resumed returned := .plain _ _ _

/-- Generation after the actual return has exactly that snapshot's current
bound annotation. Waiting metadata also agree by exact_waiting_bounds. -/
theorem returned_generated : ∃ annotation : Code [] returned.plan returned.forest,
    annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
    SourcePlanBounds.ofCode annotation = returned.current := by
  let source := restoredSource.plug QueuedExamples.bindingPosition
  obtain ⟨annotation, ready, generated⟩ :=
    (source.source.generate_expanded_waiting (nextWhole := nextWhole)
      .hit .nil receiver_change .refl waiting_change rfl source.checked).2.2
  exact ⟨annotation, ready, generated.current_bounds⟩

/-- The same construction accepts the independently proved permission and
phase changes in which owner 88 has actually been spent and owner 19 is live. -/
theorem generated_after_spending : ∃ annotation : Code [] HandlerExamples.clause nextWhole,
    annotation.Valid [] QueuedExamples.nextActions QueuedExamples.nextPhases := by
  have source := (restoredSource.source.extend_permissions QueuedExamples.permission_extension rfl).restrict_phases
    QueuedExamples.availability
  have checked := HandlerExamples.body.boundCheck_owner_transport restoredSource.checked
    (nextActions := QueuedExamples.nextActions) (nextPhases := QueuedExamples.nextPhases) rfl (fun _ => rfl)
  obtain ⟨annotation, ready, generated⟩ :=
    (source.generate_expanded_waiting (nextWhole := nextWhole)
      .hit .nil receiver_change .refl waiting_change rfl checked).2.2
  exact ⟨annotation, ready⟩

/-- Rich original metadata is not erased by expanding the retained forest. -/
theorem rich_waiting_expansion : ∃ target : SourceScheduledCapabilityAnnotations.Retained []
    (.spent (owner := 88) ReceiverMetadataExamples.saved) (.spent (owner := 19) .nil),
    target.Valid [] ReceiverMetadataExamples.actions
      (OwnerPhaseTransitions.spend ReceiverMetadataExamples.phases 19) ∧
    Retained.Neutral [] (Retained.ofCapability ReceiverMetadataExamples.rich) (Retained.ofCapability target) :=
  SourceScheduledCapabilityAnnotations.Retained.expand_neutral (recipeLaws []) (fun evidence => evidence)
    (.history .refl) .refl ReceiverMetadataExamples.rich ReceiverMetadataExamples.rich_valid

/-- The independent operation check still rejects an unavailable owner after
the waiting tail changes; a structural expansion does not grant availability. -/
theorem spent_owner_rejected : ¬ HandlerExamples.body.BoundCheck [] [] HandlerExamples.actions
    (OwnerPhaseTransitions.spend HandlerExamples.phases 19)
    (.live 19 (.plain (.request effectE 0) .nil)
      (.handler effectE resumeTable resumeDependencies (.spent 88 .nil)))
    (.handler effectE resumeTable resumeDependencies (.spent 88 .nil)) current.before := by
  intro checked
  have impossible := checked.2.1.2.1
  cases impossible

/-- Recover full source admission at the changed tail from the actual moved
record, including its original annotation and nested declaration evidence. -/
noncomputable def activated := restoredSource.expand_waiting (nextWhole := nextWhole)
  .hit .nil receiver_change .refl waiting_change rfl

theorem activated_body : activated.body = HandlerExamples.body := rfl

theorem activated_source : At (recipeLaws []) (fun evidence => evidence) HandlerExamples.body current := activated.source

theorem activated_children : ExactDescendants (recipeLaws []) (fun evidence => evidence)
    HandlerExamples.body current := activated.source.descendants_exact

theorem activated_return :
    ∃ nextQueued : QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] current
        (HandlerExamples.body.boundAnnotation.plug QueuedExamples.bindingPosition).2.2,
      returned = ⟨_, _, nextQueued.body.boundAnnotation, _, _, nextWhole,
        Retained.live (.plain .absent .nil) (.handler (.spent (owner := 88) .nil))⟩ :=
  activated.returned QueuedExamples.bindingPosition (.absent (plan := Plan.pure))
    (Retained.live (.plain .absent .nil) (.handler (.spent (owner := 88) .nil))) return_shape

theorem activated_return_then_compute : At (recipeLaws []) (fun evidence => evidence) HandlerExamples.body current := by
  let recomposed := activated.plug QueuedExamples.bindingPosition
  exact (recomposed.source.reduce recomposed.checked
    (show recomposed.body.Reduction .bind HandlerExamples.body from .bind)).1

theorem activated_focus_again : At (recipeLaws []) (fun evidence => evidence) HandlerExamples.body
    (current.pure_frame (recipeLaws []) (fun evidence => evidence)) := activated.focus_neutral.source

/-- Restore the recovered record under both a changed waiting tail and a new
pure caller frame. The caller interface and all check equalities are derived. -/
noncomputable def derivedContext := HandlerExamples.context.restore_neutral
  (laws := recipeLaws []) (project := fun evidence => evidence)
  (nextWhole := Forest.plain Plan.pure nextWhole) (.plain .hit) (.extra .refl) waiting_change

noncomputable def derivedSource := restoredSource.restore_neutral
  (nextWhole := Forest.plain Plan.pure nextWhole) (.plain .hit)
  (.extra receiver_change) (.extra .refl) waiting_change

theorem derived_source : At (recipeLaws []) (fun evidence => evidence)
    HandlerExamples.body derivedContext := derivedSource.source

theorem derived_generation : ∃ annotation : Code [] HandlerExamples.clause (.plain Plan.pure nextWhole),
    annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
    Generated HandlerExamples.actions derivedContext.continuationBounds HandlerExamples.body annotation :=
  derivedSource.source.generate_source derivedSource.checked

/-- The same restored record survives recomposition and computation without
rechecking target source admission. -/
theorem derived_recomposition : At (recipeLaws []) (fun evidence => evidence)
    HandlerExamples.body derivedContext := by
  let recomposed := derivedSource.plug QueuedExamples.bindingPosition
  exact (recomposed.source.reduce recomposed.checked
    (show recomposed.body.Reduction .bind HandlerExamples.body from .bind)).1

end Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.waiting_change
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.receiver_change
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.actual_handler_cut
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.capture_shape
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.resumption_shape
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.exact_capture
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.exact_resumption
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.restored_source_identity
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.restored_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.exact_waiting_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.return_shape
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.returned_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.generated_after_spending
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.rich_waiting_expansion
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.spent_owner_rejected

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.activated_body

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.activated_source

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.activated_children

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.activated_return

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.activated_return_then_compute

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.activated_focus_again

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.derived_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.derived_generation
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingExamples.derived_recomposition
