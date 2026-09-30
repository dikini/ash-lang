import SourceConsumingUseQueuedExamples
import SourceAnnotatedStoredUseComputation
import SourceAnnotatedStoredUseEntries
import SourceConsumingCleanupAdmissionExamples

/-! Reuse the rich masking and effectful-cleanup fixtures to check source
descent through computation, fresh allocation and callback registration. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.UseTransitionExamples
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourcePlanBounds (Annotation)
open SourceRetainedPlans (Forest)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledRetainedInterfaces (Interfaces)

namespace Computation
open UseQueuedExamples (queued parentBody parent position installed caller cut nested inner_source)
open UseAdmissionExamples (actions phases context)
open LeafAdmissionExamples (inner innerBody)

theorem bind_generated : ∃ annotation : Code [] inner installed,
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = innerBody.boundAnnotation := by
  obtain ⟨record, _⟩ := (queued.plug position).reduced (.bind _)
  obtain ⟨code, ready, kept, _⟩ := record.generate (recipeLaws []) (fun evidence => evidence)
  exact ⟨code, ready, kept⟩

def argument : SourceAnnotatedCode.Context := .appArgument .unit (.unit .unit)

theorem beta_generated : ∃ annotation : Code [] inner installed,
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = innerBody.boundAnnotation := by
  obtain ⟨record, _⟩ := (queued.plug argument).reduced (.beta _)
  obtain ⟨code, ready, kept, _⟩ := record.generate (recipeLaws []) (fun evidence => evidence)
  exact ⟨code, ready, kept⟩

def branchBody : Body [] 19 (.sequence .pure (.choice inner (.sequence .pure inner))) :=
  .sequence [] .pure .pure (.choice innerBody parentBody)

def branchRecord : UseQueuedBody [(SourceDependencyCapture.Examples.effectE, 0)] []
    context cut caller branchBody.boundAnnotation :=
  ⟨branchBody, rfl, .sequence (.choice inner_source (.sequence inner_source)),
    .sequence (.choice nested (.sequence nested)), ⟨rfl, queued.checked, rfl, queued.checked⟩⟩

theorem true_branch : ∃ annotation : Code [] inner installed,
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = innerBody.boundAnnotation := by
  obtain ⟨record, _⟩ := branchRecord.reduced (.ifTrue _)
  obtain ⟨code, ready, kept, _⟩ := record.generate (recipeLaws []) (fun evidence => evidence)
  exact ⟨code, ready, kept⟩

/-- The false branch has a different source/bound shape, so branch selection
cannot pass by accidentally retaining the true branch. -/
theorem false_branch : ∃ annotation : Code [] (.sequence .pure inner) installed,
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = parentBody.boundAnnotation := by
  obtain ⟨record, _⟩ := branchRecord.reduced (.ifFalse _)
  obtain ⟨code, ready, kept, _⟩ := record.generate (recipeLaws []) (fun evidence => evidence)
  exact ⟨code, ready, kept⟩

end Computation

namespace Resource
open UseAdmissionExamples (actions phases context whole)
open LeafAdmissionExamples.RichWaiting (resourceBody resourcePlan resource_admitted)
open SourceDependencyCapture.Examples (effectE)

def record : UseQueuedBody [(effectE, 0)] [] context OwnerCut.hit Interfaces.nil resourceBody.boundAnnotation where
  body := resourceBody
  origin := rfl
  source := UseAdmissionExamples.resource_at_use
  nested := .resource (fun identity _ =>
    .sequence (UseQueuedExamples.HandlerEntry.root.nested.world_weaken (List.subset_append_left [] [identity])))
  checked := resource_admitted.at_capture rfl rfl rfl

/-- Fresh-body descent and neutral restoration compose while preserving the
original richer captured source, including its outside continuation. -/
theorem allocated : ∃ annotation : Code [7]
    (.sequence (.sequence .pure (.request (effect := .cell 7) (operation := 0))) LeafAdmissionExamples.masked)
    (.cell (identity := 7) (.spent (owner := 73) whole)),
    annotation.Valid [] actions phases ∧
    SourcePlanBounds.ofCode annotation = (resourceBody.boundAnnotation.resourceBody (identity := 7) (by simp)) :=
  ((record.at_receiver.expand (.history (owner := 73) .refl)).resource_body (identity := 7) (by simp)).generate
    (recipeLaws []) (fun evidence => evidence)

end Resource

namespace Cleanup
open Ash.OneShot.SourceConsumingCleanupAdmission.Examples (actions phases context body clause clause_checked continuation whole)

theorem source : AtUse [] actions phases (context phases) (body [.cell 4]) .nil := by
  apply AtUse.cleanup
  · intro request member
    exact List.mem_singleton.mpr (congrArg Prod.fst (List.mem_singleton.mp member))
  · exact .sequence (.choice (.resume (fun _ => .empty)) (.dispose (fun _ => .empty)))

def record : UseQueuedBody [] [] (context phases) OwnerCut.hit Interfaces.nil (body [.cell 4]).boundAnnotation :=
  ⟨body [.cell 4], rfl, source, .cleanup (.sequence (.choice .resume .dispose)), clause_checked⟩

/-- Callback admission and child compilation use the same actual receiver
after restoration; the callback runs under its additional running marker. -/
theorem registered :
    ∃ child : Code [4] (.sequence (.request (effect := .cell 4) (operation := 1)) continuation)
      (.cleanup (needs := [.cell 4]) (.request (effect := .cell 4) (operation := 0)) (.spent (owner := 73) whole)),
    ∃ callback : Code [4] (.request (effect := .cell 4) (operation := 0)) (.running (.spent (owner := 73) whole)),
      child.Valid [] actions phases ∧ callback.Valid [] actions phases := by
  obtain ⟨required, footprint, declared, child, ready, _, _⟩ :=
    (record.at_receiver.expand (.history (owner := 73) .refl)).cleanup_body
  obtain ⟨code, valid, _⟩ := child.generate (recipeLaws []) (fun evidence => evidence)
  exact ⟨code, .operations required footprint declared, valid, ready⟩

theorem omitted_dependency_rejected : ¬ AtUse [] actions phases (context phases) (body []) .nil := by
  intro source
  cases source with
  | cleanup covered inner =>
      have impossible := covered (.cell 4, 0) (by simp)
      cases impossible

end Cleanup
end Ash.OneShot.SourceConsumingCleanupAdmission.UseTransitionExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseTransitionExamples.Computation.bind_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseTransitionExamples.Computation.beta_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseTransitionExamples.Computation.true_branch
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseTransitionExamples.Computation.false_branch
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseTransitionExamples.Resource.allocated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseTransitionExamples.Cleanup.source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseTransitionExamples.Cleanup.registered
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseTransitionExamples.Cleanup.omitted_dependency_rejected
