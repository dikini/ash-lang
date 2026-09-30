import SourceConsumingAdmissionWorld
import SourceConsumingAdmissionPhaseExamples
import SourceConsumingAdmissionDescent

/-! World transport composes with phase transport and source descent. Examples
reuse the established nested source and outside-owner cleanup derivations. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.WorldExamples
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceConsumingClauseAnnotations (Body)
open SourceDependencyCapture.Examples (effectE disposeTable disposeDependencies)
open SourceRetainedPlans (Forest)
open OwnerPhaseTransitions (spend)

theorem larger : [4] ⊆ [4, 8] := by decide

theorem structural_source : At (recipeLaws []) (fun evidence => evidence)
    (StructuralExamples.body.world_weaken larger) (StructuralExamples.context.world_weaken larger) :=
  StructuralExamples.admitted.world_weaken larger

/-- The independently checked axes compose: grow the resource world, then
consume an unrelated owner without losing the saved outside-owner invocation. -/
theorem world_and_phase_schedule :
    SourceScheduledChecks.Local [] StructuralExamples.actions (spend PhaseExamples.extraPhases 88) [4, 8]
      StructuralExamples.clause StructuralExamples.whole := by
  apply structural_source.scheduled_restrict (StructuralExamples.body.boundCheck_world_weaken larger StructuralExamples.checked)
  intro name member ready
  exact PhaseExamples.retire_unrelated name member (PhaseExamples.structural_extension name member ready)

/-- Compilation keeps the original handler packets across world growth. -/
theorem nested_bounds : ∃ annotation : Code [4, 8] HandlerExamples.wrapped Examples.whole,
    annotation.Valid [] Examples.actions Examples.phases ∧
      SourcePlanBounds.ofCode annotation = HandlerExamples.wrappedBody.boundAnnotation.world_weaken larger :=
  HandlerExamples.wrapped_admitted.generate_world_retaining
    (HandlerExamples.wrapped_source.at_capture rfl rfl rfl) larger

/-- After weakening, the same source-resource rule accepts every identity
fresh in the larger world. Descent then recovers both continuation branches. -/
theorem nested_fresh_branches (identity : Nat) (fresh : identity ∉ [4, 8]) :
    let forest := Forest.cell (identity := identity)
      (.cleanup (needs := [.cell 4]) (.request (effect := .cell 4) (operation := 0))
        (.handler (effect := .user 99 []) (table := disposeTable) (families := disposeDependencies) (required := [])
          (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) Examples.whole)))
    SourceScheduledChecks.Local [] Examples.actions Examples.phases ([4, 8] ++ [identity])
      (.invoke (key := ⟨19, .resume⟩)) forest ∧
    SourceScheduledChecks.Local [] Examples.actions Examples.phases ([4, 8] ++ [identity])
      (.invoke (key := ⟨19, .dispose⟩)) forest := by
  have parent := HandlerExamples.wrapped_admitted.world_weaken larger
  have checked := HandlerExamples.wrappedBody.boundCheck_world_weaken larger
    (HandlerExamples.wrapped_source.at_capture (actions := Examples.actions) (phases := Examples.phases)
      (captured := SourceDependencyCapture.Scope.nil) (waiting := .cell 4 .nil) rfl rfl rfl)
  obtain ⟨outer, _, outerSource, outerChecked⟩ := parent.handler_body checked
  obtain ⟨inner, _, innerSource, innerChecked⟩ := outerSource.handler_body outerChecked
  obtain ⟨cleanup, _, cleanupSource, cleanupChecked⟩ := innerSource.cleanup_body innerChecked
  obtain ⟨resource, _, resourceSource, resourceChecked⟩ := cleanupSource.resource_body cleanupChecked fresh
  have branches := resourceSource.sequence_rest.choice_branches
  exact ⟨branches.1.scheduled resourceChecked.2.1, branches.2.scheduled resourceChecked.2.2⟩

theorem rich_callback_world : SourceScheduledSourceRechecking.Expression []
    SourceScheduledSourceRechecking.Examples.actions SourceScheduledSourceRechecking.Examples.phases
    (SourceScheduledSourceRechecking.Examples.request.world_weaken (List.nil_subset [8]))
    SourceScheduledSourceRechecking.Examples.after :=
  SourceScheduledSourceRechecking.Examples.rechecked.world_weaken (List.nil_subset [8])

end Ash.OneShot.SourceConsumingCleanupAdmission.WorldExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WorldExamples.larger
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WorldExamples.structural_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WorldExamples.world_and_phase_schedule
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WorldExamples.nested_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WorldExamples.nested_fresh_branches
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WorldExamples.rich_callback_world
