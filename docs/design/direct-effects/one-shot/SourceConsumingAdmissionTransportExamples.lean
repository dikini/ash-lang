import SourceConsumingAdmissionTransport
import SourceConsumingAdmissionWorldExamples

/-! Joint transport with real changes on all three axes, nested handler and
resource bodies, and rejection of permission replacement at a retained owner. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.TransportExamples
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceScheduledPhaseRestriction (AvailableOn)
open OwnerPhaseTransitions (available spend)

def actions := StructuralExamples.actions.insert 88 ⟨true, true⟩

theorem permission_extension : Syntax.UsageExtension StructuralExamples.actions actions :=
  Syntax.fresh_usage_insert_extends rfl

theorem phases_preserved : AvailableOn (SourceDependencyOwners.owners PhaseExamples.structuralScope)
    StructuralExamples.phases (spend PhaseExamples.extraPhases 88) :=
  fun name member ready => PhaseExamples.retire_unrelated name member
    (PhaseExamples.structural_extension name member ready)

/-- Both original owners retain their saved-source evidence while an unrelated
owner gains a permission entry and is consumed, and the resource world grows. -/
theorem structural_admission : At (recipeLaws []) (fun evidence => evidence)
    (StructuralExamples.body.world_weaken WorldExamples.larger)
    (((StructuralExamples.context.extend_permissions permission_extension rfl).restrict_phases phases_preserved).world_weaken WorldExamples.larger) :=
  StructuralExamples.admitted.transport permission_extension rfl phases_preserved WorldExamples.larger

theorem exact_bounds : ∃ annotation : Code [4, 8] StructuralExamples.clause StructuralExamples.whole,
    annotation.Valid [] actions (spend PhaseExamples.extraPhases 88) ∧
    SourcePlanBounds.ofCode annotation = StructuralExamples.body.boundAnnotation.world_weaken WorldExamples.larger :=
  StructuralExamples.admitted.generate_transport_retaining StructuralExamples.checked
    permission_extension phases_preserved WorldExamples.larger

/-- Establish that the permission premise is not an unchanged-map example. -/
theorem registry_changed : StructuralExamples.actions 88 = none ∧ actions 88 = some ⟨true, true⟩ := ⟨rfl, rfl⟩

/-- The same API covers two nested handlers, effectful cleanup, fresh resources
and both continuation-consumption branches in the original source. -/
theorem nested_exact_bounds : ∃ annotation : Code [4, 8] HandlerExamples.wrapped Examples.whole,
    annotation.Valid [] (Examples.actions.insert 88 ⟨true, true⟩) (available [19, 88]) ∧
    SourcePlanBounds.ofCode annotation = HandlerExamples.wrappedBody.boundAnnotation.world_weaken WorldExamples.larger := by
  apply HandlerExamples.wrapped_admitted.generate_transport_retaining
    (HandlerExamples.wrapped_source.at_capture rfl rfl rfl)
    (Syntax.fresh_usage_insert_extends rfl) _ WorldExamples.larger
  intro name member _
  change name ∈ [19] at member
  have same := List.mem_singleton.mp member
  subst name
  rfl

/-- Rich callback transport retains its original source-validity premise;
the recursive freshRich rule does not require newly assumed target validity. -/
theorem rich_callback : SourceScheduledSourceRechecking.Expression []
    (SourceScheduledSourceRechecking.Examples.actions.insert 88 ⟨true, true⟩)
    (spend (available [37, 88]) 88) SourceScheduledSourceRechecking.Examples.request
    SourceScheduledSourceRechecking.Examples.after := by
  apply SourceScheduledSourceRechecking.Examples.rechecked.transport (Syntax.fresh_usage_insert_extends rfl)
  intro name member _
  change name ∈ [37] at member
  have same := List.mem_singleton.mp member
  subst name
  rfl

/-- Registry extension cannot grant disposal to an already registered
resume-only owner. Such a change would need new closing evidence. -/
theorem cannot_add_disposal_right : ¬ Syntax.UsageExtension StructuralExamples.actions
    (StructuralExamples.actions.insert 19 ⟨true, true⟩) := by
  intro extension
  have impossible := extension 19 ⟨true, false⟩ rfl
  change some (⟨true, true⟩ : Syntax.OneShotRights) = some ⟨true, false⟩ at impossible
  cases impossible

end Ash.OneShot.SourceConsumingCleanupAdmission.TransportExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.TransportExamples.permission_extension
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.TransportExamples.phases_preserved
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.TransportExamples.structural_admission
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.TransportExamples.exact_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.TransportExamples.registry_changed
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.TransportExamples.nested_exact_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.TransportExamples.rich_callback
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.TransportExamples.cannot_add_disposal_right
