import SourceScheduledInternalRechecking
import SourceScheduledProtectedRecheckingExamples

/-! Internal selection keeps its actual capture while an outer receiver changes.
Conservative requirements may disappear; a local disposing request recursively
rechecks its original callback through the protected-only outside handler. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.InternalOperationExamples
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceDependencyCapture.Examples (effectE effectF resumeTable resumeDependencies resumeFamily)
open ProtectedRequestExamples (actions phases)

def front : Forest (Hints.handler (effect := effectE) (table := resumeTable)
    (families := resumeDependencies) [] .nil) := .handler .nil
def outside : Forest (Hints.handler (effect := effectF) (table := resumeTable)
    (families := resumeDependencies) [] .nil) := .handler .nil
theorem cut : SourceScheduledNeutral.Cut effectE 0 ⟨false, some [], some []⟩
    (some resumeFamily, some resumeFamily) front front .nil := .hit rfl rfl
def source : Code [] (.request (effect := effectE) (operation := 0)) (front.append outside) :=
  .operations [(effectE, 0), (effectF, 0)]
    (.weaken .request (by intro request member; cases List.mem_singleton.mp member; exact List.mem_cons_self)) .request

theorem original_valid : source.Valid [] actions phases := rfl

theorem old_requirements_unavailable : SourceContextualHints.checkRequirements
    (.handler effectE resumeTable resumeDependencies .nil) [(effectE, 0), (effectF, 0)] = false := rfl

/-- Recover the actual request's capability from its original footprint;
the unneeded outside requirement is not imposed on the new receiver. -/
theorem rechecked : Expression [] actions phases source (front.append .nil) :=
  .internal_operations cut .nil original_valid

theorem generated : ∃ annotation : Code [] (.request (effect := effectE) (operation := 0)) (front.append .nil),
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode source :=
  rechecked.compile_retaining (recipeLaws []) (fun checked => checked) original_valid

end Ash.OneShot.SourceScheduledSourceRechecking.InternalOperationExamples

namespace Ash.OneShot.SourceScheduledSourceRechecking.InternalDisposalExamples
open SourceDeclarationPlans (Plan)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceDependencyCapture.Examples (effectE effectF disposeTable disposeDependencies disposeFamily)
open ProtectedRequestExamples (actions phases)

def front := Forest.cleanup (needs := [effectE]) (.request (effect := effectE) (operation := 0))
  (.handler (effect := effectF) (table := disposeTable) (families := disposeDependencies) (required := []) .nil)
def outside := Forest.running ProtectedRequestExamples.before
def next := Forest.running ProtectedRequestExamples.after
theorem cut : SourceScheduledNeutral.Cut effectF 0 ⟨true, some [], none⟩
    (some disposeFamily, none) front front .nil := .cleanup (.hit rfl rfl)

def oldClosing : Retained [] front.forClosing (.running outside) :=
  .cleanup (.operations [(effectE, 0)] .request .request) (.operations .nil)
def source : Code [] (.request (effect := effectF) (operation := 0)) (front.append outside) :=
  .selected (cut.suffix outside) (fun _ => .cleanup (.handler .nil)) (fun _ => oldClosing)

theorem original_valid : source.Valid [effectE] actions phases :=
  ⟨by decide, fun _ => ⟨rfl, rfl⟩⟩

/-- Disposal is local: the selected capture stops before the running outside
receiver. Only its original callback's receiving suffix must be reconstructed. -/
theorem callback_rechecked : ReceiverChange [effectE] actions phases oldClosing (.running next) :=
  .cleanup (.crosses_cleanup_from_contract (Forest.running (Forest.running .nil)) rfl (.hit rfl rfl) rfl rfl rfl) .empty

theorem rechecked : Expression [effectE] actions phases source (front.append next) :=
  .internal_selected cut next original_valid (fun _ => callback_rechecked)

theorem generated : ∃ annotation : Code [] (.request (effect := effectF) (operation := 0)) (front.append next),
    annotation.Valid [effectE] actions phases ∧ SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode source :=
  rechecked.compile_retaining (recipeLaws [effectE]) (fun checked => checked) original_valid

/-- The recursive closing-source compiler retains the exact callback data. -/
theorem closing_metadata : ∃ annotation : Retained [] front.forClosing (.running next),
    annotation.Valid [effectE] actions phases ∧ SourceBoundSnapshots.Retained.ofCapability annotation =
      SourceBoundSnapshots.Retained.ofCapability oldClosing :=
  callback_rechecked.compile_retaining (recipeLaws [effectE]) (fun checked => checked) (original_valid.2 rfl)

end Ash.OneShot.SourceScheduledSourceRechecking.InternalDisposalExamples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalOperationExamples.original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalOperationExamples.old_requirements_unavailable
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalOperationExamples.rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalOperationExamples.generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalDisposalExamples.original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalDisposalExamples.callback_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalDisposalExamples.rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalDisposalExamples.generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalDisposalExamples.closing_metadata

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalOperationExamples.cut
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.InternalDisposalExamples.cut
