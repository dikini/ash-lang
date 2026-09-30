import SourceConsumingReceiverMetadataExamples
import SourceConsumingHandlerAdmissionExamples
import SourceConsumingContextualCaptureExamples

/-! Generated-source correspondence excludes the former erased witness and
composes through handlers, cleanup, branches, fresh resources and actual capture. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.GeneratedSourceExamples
open SourceConsumingClauseAnnotations (Body Generated)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)

/-- The earlier witness still has valid/current bounds, but cannot satisfy the
stronger generated-source judgment for the rich saved context. -/
theorem erased_witness_rejected : ¬ Generated ReceiverMetadataExamples.actions
    ReceiverMetadataExamples.richContext.continuationBounds
    (Body.resume : Body [] 19 (Plan.invoke (key := ⟨19, .resume⟩))) ReceiverMetadataExamples.oldWitness := by
  intro generated
  cases generated with
  | resume permission kept waiting => cases kept

theorem rich_resumption_generated :
    ∃ annotation : Code [] (Plan.invoke (key := ⟨19, .resume⟩))
        (.live (owner := 19) ReceiverMetadataExamples.saved .nil),
      annotation.Valid [] ReceiverMetadataExamples.actions ReceiverMetadataExamples.phases ∧
      Generated ReceiverMetadataExamples.actions ReceiverMetadataExamples.richContext.continuationBounds
        .resume annotation :=
  ReceiverMetadataExamples.admitted_at_rich.generate_source (resumeRequired := []) (closeRequired := [])
    ⟨rfl, rfl, rfl, rfl⟩

def richResourceBody : Body [] 19 (Plan.resource (fun _ => Plan.invoke (key := ⟨19, .resume⟩))) :=
  .resource (fun _ _ => .resume)

/-- Every fresh identity maps the nonempty original saved bounds before the
emitted resumption, rather than merely preserving current expression bounds. -/
theorem rich_resource_generated :
    ∃ annotation : Code [] (Plan.resource (fun _ => Plan.invoke (key := ⟨19, .resume⟩)))
        (.live (owner := 19) ReceiverMetadataExamples.saved .nil),
      annotation.Valid [] ReceiverMetadataExamples.actions ReceiverMetadataExamples.phases ∧
      Generated ReceiverMetadataExamples.actions ReceiverMetadataExamples.richContext.continuationBounds
        richResourceBody annotation := by
  have admitted : At (recipeLaws []) (fun evidence => evidence) richResourceBody ReceiverMetadataExamples.richContext :=
    .resource (fun _ _ => .resume)
  exact admitted.generate_source (resumeRequired := []) (closeRequired := []) (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)

/-- Two ordered handlers, effectful cleanup, resource allocation, sequencing
and both consuming branches use the same structural generation theorem. -/
theorem nested_generated :
    ∃ annotation : Code [4] HandlerExamples.wrapped Examples.whole,
      annotation.Valid [] Examples.actions Examples.phases ∧
      Generated Examples.actions (Examples.context Examples.phases).continuationBounds
        HandlerExamples.wrappedBody annotation :=
  HandlerExamples.wrapped_admitted.generate_source
    (HandlerExamples.wrapped_source.at_capture rfl rfl rfl)

/-- Selected-source compilation and runtime capture share the actual source
snapshot. This example has a nested handler around the selected resumption. -/
theorem selected_capture_agrees :
    ∃ annotation : Code [] (CaptureExamples.bodies 19) (.live (owner := 19) CaptureExamples.saved .nil),
      (SourceScheduledCaptureAnnotations.Capture.site CaptureExamples.cut CaptureExamples.selected annotation).Valid
        [] CaptureExamples.actions CaptureExamples.phases ∧
      Generated (CaptureExamples.actions.insert 19 CaptureExamples.raw.requiredActions)
        CaptureExamples.context.continuationBounds (CaptureExamples.body 19) annotation ∧
      ∃ savedBounds : SourceBoundSnapshots.Retained [] CaptureExamples.saved,
        let captured : SourceBoundSnapshots.Snapshot [] :=
          ⟨_, CaptureExamples.bodies 19, SourcePlanBounds.ofCode annotation, _, _,
            .live (owner := 19) CaptureExamples.saved .nil,
            .live savedBounds (SourceBoundSnapshots.Retained.ofCapability CaptureExamples.context.after)⟩
        SourceBoundSnapshots.Captured 19 CaptureExamples.snapshot captured ∧ captured.Admitted ∧
        ∀ permission, CaptureExamples.context.continuationBounds.resumption permission = savedBounds :=
  by
    obtain ⟨annotation, ready, generated, savedBounds, moved, admitted, kept, _⟩ :=
      SelectedSource.capture_source_snapshot (recipeLaws []) (fun evidence => evidence)
        CaptureExamples.snapshot CaptureExamples.snapshot_admitted CaptureExamples.bounded CaptureExamples.cut
        CaptureExamples.selected CaptureExamples.selected_source CaptureExamples.source
        CaptureExamples.captureSource CaptureExamples.permits rfl CaptureExamples.fresh
        CaptureExamples.absent CaptureExamples.contextual rfl
    exact ⟨annotation, ready, generated, savedBounds, moved, admitted, kept⟩

end Ash.OneShot.SourceConsumingCleanupAdmission.GeneratedSourceExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.GeneratedSourceExamples.erased_witness_rejected
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.GeneratedSourceExamples.rich_resumption_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.GeneratedSourceExamples.rich_resource_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.GeneratedSourceExamples.nested_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.GeneratedSourceExamples.selected_capture_agrees
