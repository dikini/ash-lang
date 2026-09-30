import SourceConsumingReceiverMetadataExamples
import SourceScheduledStructuralClosingExamples

/-! The actual resource context constructor retains explicit saved bounds,
callback/dormant metadata, canonical closing and outside-owner validity. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.ResourceRetentionExamples
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Retained recipeLaws)
open SourceScheduledSourceRechecking
open SourceBoundSnapshots.Retained (ofCapability)

noncomputable def richResource := ReceiverMetadataExamples.richContext.resource
  (recipeLaws []) (fun evidence => evidence) 4

theorem rich_saved_bounds : ofCapability (richResource.resumption (by rfl)).val =
    (ofCapability ReceiverMetadataExamples.rich).world_weaken (List.subset_append_left [] [4]) :=
  Context.resource_resumption_bounds (recipeLaws []) (fun evidence => evidence)
    ReceiverMetadataExamples.richContext 4 (by rfl)

theorem rich_saved_not_absent :
    ofCapability (richResource.resumption (by rfl)).val ≠
      SourceBoundSnapshots.Retained.absent ReceiverMetadataExamples.saved := by
  intro erased
  have impossible := rich_saved_bounds.symm.trans erased
  cases impossible

/-- Resource-world extension and provider insertion preserve the entire saved
forest, including explicit callback bounds and dormant saved code. -/
theorem callback_dormant_provider :
    ∃ annotation : Retained [4] RecompositionExamples.front
        (.cell (identity := 4) (RecompositionExamples.suffix.append .nil)),
      annotation.Valid [] ClosingExamples.actions ClosingExamples.phases ∧
      ofCapability annotation = (ofCapability RecompositionExamples.frontSource).world_weaken
        (List.subset_append_left [] [4]) :=
  RecompositionExamples.frontSource.provide_world_retaining (recipeLaws []) (fun evidence => evidence)
    RecompositionExamples.front_valid (List.subset_append_left [] [4]) .here

noncomputable def outsideOwnerResource := StructuralExamples.context.resource
  (recipeLaws []) (fun evidence => evidence) 8

theorem outside_owner_still_valid :
    (outsideOwnerResource.resumption (by rfl)).val.Valid [] StructuralExamples.actions
      (OwnerPhaseTransitions.spend StructuralExamples.phases 19) :=
  (outsideOwnerResource.resumption (by rfl)).property

theorem outside_owner_metadata : ofCapability (outsideOwnerResource.resumption (by rfl)).val =
    (ofCapability (StructuralExamples.context.resumption (by rfl)).val).world_weaken
      (List.subset_append_left [4] [8]) :=
  Context.resource_resumption_bounds (recipeLaws []) (fun evidence => evidence) StructuralExamples.context 8 (by rfl)

theorem outside_waiting_metadata : ofCapability outsideOwnerResource.after =
    (ofCapability StructuralExamples.context.after).world_weaken (List.subset_append_left [4] [8]) :=
  Context.resource_tail_bounds (recipeLaws []) (fun evidence => evidence) StructuralExamples.context 8

/-- The canonical closing obtained from original source remains canonical
through resource entry, rather than merely some valid closing of the same plans. -/
theorem canonical_closing_after_resource :
    ∃ context : Context [] 19 [] (ClosingExamples.actions.insert 19 ⟨true, true⟩)
        (OwnerPhaseTransitions.introduce ClosingExamples.phases 19)
        (.live (owner := 19) ClosingExamples.saved ClosingExamples.waiting) .nil
        ClosingExamples.saved ClosingExamples.waiting,
      (∀ permission, ofCapability ((context.resource (recipeLaws []) (fun evidence => evidence) 4).closing permission).val =
        ((ofCapability ClosingExamples.inside).world_weaken (List.subset_append_left [] [4])).forClosing) ∧
      ofCapability (context.resource (recipeLaws []) (fun evidence => evidence) 4).after =
        (ofCapability ClosingExamples.after).world_weaken (List.subset_append_left [] [4]) := by
  obtain ⟨context, _, closing, tail⟩ := Context.capture_structural (rights := ⟨true, true⟩) (owner := 19)
    (recipeLaws []) (fun evidence => evidence) ClosingExamples.inside ClosingExamples.after ClosingExamples.inside_valid
    (fun _ => ClosingExamples.inside_closing) (fun _ => ⟨by decide, by decide⟩) ClosingExamples.after_valid rfl (by decide)
  refine ⟨context, ?_, ?_⟩
  · intro permission
    rw [Context.resource_closing_bounds, closing permission]
    exact (SourceBoundSnapshots.Retained.forClosing_world_weaken _ (List.subset_append_left [] [4])).symm
  · rw [Context.resource_tail_bounds, tail]

end Ash.OneShot.SourceConsumingCleanupAdmission.ResourceRetentionExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ResourceRetentionExamples.rich_saved_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ResourceRetentionExamples.rich_saved_not_absent
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ResourceRetentionExamples.callback_dormant_provider
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ResourceRetentionExamples.outside_owner_still_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ResourceRetentionExamples.outside_owner_metadata
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ResourceRetentionExamples.outside_waiting_metadata
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ResourceRetentionExamples.canonical_closing_after_resource
