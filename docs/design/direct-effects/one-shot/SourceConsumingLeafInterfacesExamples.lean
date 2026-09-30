import SourceConsumingLeafCapture
import SourceConsumingContextualCaptureExamples
import SourceConsumingInterfaceNestingExamples
/-! Initial admission with temporary masking and exact rich waiting metadata. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples
open SourceConsumingClauseAnnotations (Body Admitted)
open SourceDeclarationPlans (Plan)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open SourceConsumingClauseAnnotations (Generated)
open SourceDependencyCapture.Examples (effectE resumeTable)
open HandlerExamples (actions phases waiting whole)
open HandlerInterfaceExamples (savedInterface bounds)
open SourceScheduledInvocationInterfaceExamples (declarations declaration_recipes)

def inner := Plan.handler (effect := effectE) (table := resumeTable) [] declarations
  (.invoke (key := ⟨19, .resume⟩))
def innerBody {world : List Nat} : Body world 19 inner := .handler bounds declaration_recipes .resume
def masked := Plan.handler (effect := effectE) (table := []) [] .nil inner
def maskedBody {world : List Nat} : Body world 19 masked := .handler .nil .nil innerBody

theorem admitted {world : List Nat} : Admitted ⟨true, true⟩ [(effectE, 0)] [] (maskedBody (world := world)) [] :=
  .handler (.handler (.resume rfl) rfl rfl) rfl rfl

theorem scheduled : SourceScheduledChecks.Local [] actions phases [] masked whole :=
  (admitted (world := [])).schedule (recipeLaws []) savedInterface .nil (.handler .nil .nil)
    rfl rfl rfl (fun _ => List.Subset.refl _) (fun _ => List.Subset.refl _)
    (resumeOutside := .handler effectE resumeTable SourceDependencyCapture.Examples.resumeDependencies .nil)
    (closeOutside := .nil) (fun _ => rfl) (fun _ => rfl) (fun _ => ⟨rfl, rfl⟩) rfl

theorem intermediate_rejected : savedInterface.check
    (.handler effectE [] [] (.spent 19 (.handler effectE resumeTable
      SourceDependencyCapture.Examples.resumeDependencies .nil))) = false := rfl

/-- The initial rule reaches full source correspondence, without eager handler
admission. Saved/closing/waiting snapshots are those of the original context. -/
theorem generated : ∃ annotation : Code [] masked whole,
    annotation.Valid [] actions phases ∧
    Generated actions HandlerExamples.context.continuationBounds maskedBody annotation :=
  InterfaceNestingExamples.originalSources.initial_source admitted rfl rfl rfl
    (fun _ => List.Subset.refl _) (fun _ => List.Subset.refl _)

/-- Deferred checking does not grant reuse of the consumed one-shot owner. -/
theorem consumed_rejected : ¬ (maskedBody (world := [])).BoundCheck [(effectE, 0)] [] actions
    (OwnerPhaseTransitions.spend phases 19)
    (.live 19 (.plain (.request effectE 0) .nil)
      (.handler effectE resumeTable SourceDependencyCapture.Examples.resumeDependencies .nil))
    (.handler effectE resumeTable SourceDependencyCapture.Examples.resumeDependencies .nil) .nil := by
  intro checked
  have available := checked.2.2.2.1
  change OwnerPhaseTransitions.spend phases 19 19 = .available at available
  simp [OwnerPhaseTransitions.spend] at available

namespace RichWaiting

/-- Waiting code contains an actual bounded handler, which operation-interface
compaction would erase from the persistent snapshot. -/
def pending := Plan.handler (effect := effectE) (table := resumeTable) [] declarations Plan.pure
def waiting := Forest.plain pending HandlerExamples.waiting
def whole := Forest.live (owner := 19) HandlerExamples.saved waiting

def after : Retained [] waiting .nil :=
  .plain (.handler declaration_recipes (.operations [] .pure .pure) (some bounds))
    (.handler (.operations .nil))

def context : Context [] 19 [] actions phases whole .nil HandlerExamples.saved waiting where
  cut := .hit
  before := .nil
  resumption := fun _ => ⟨.operations savedInterface, rfl⟩
  closing := fun _ => ⟨.operations .nil, rfl⟩
  disposal := fun _ => ⟨rfl, rfl⟩
  after := after
  tailReady := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

def source : context.OperationSources where
  resumption := fun _ => savedInterface
  resumeSource := fun _ => .operations
  closing := fun _ => .nil
  closeSource := fun _ => .operations

/-- The waiting source genuinely requires its richer representation. -/
theorem waiting_not_interface : SourceScheduledSourceRechecking.OperationSource.extract after = none := rfl

theorem waiting_bounds_not_absent : SourceBoundSnapshots.Retained.ofCapability after ≠
    SourceBoundSnapshots.Retained.absent waiting := by
  intro equal
  cases equal

theorem generated : ∃ annotation : Code [] masked whole,
    annotation.Valid [] actions phases ∧
    Generated actions context.continuationBounds maskedBody annotation :=
  source.initial_source admitted rfl rfl rfl
    (fun _ => List.Subset.refl _) (fun _ => List.Subset.refl _)

/-- The resource branch performs a read, then enters the temporarily masking
handler pair. The universal source rule covers every fresh resource identity. -/
def resourcePlan := Plan.resource (fun identity => Plan.sequence
  (.sequence .pure (.request (effect := .cell identity) (operation := 0))) masked)
def resourceBody : Body [] 19 resourcePlan := .resource (fun identity _ =>
  .sequence [(.cell identity, 0)] (.sequence .pure .request) (.sequence .pure .request) maskedBody)

theorem resource_admitted : Admitted ⟨true, true⟩ [(effectE, 0)] [] resourceBody [] := by
  apply Admitted.resource
  intro identity _fresh
  apply Admitted.weaken (Admitted.sequence admitted)
  intro request member
  simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  exact Or.inl member

theorem resource_generated : ∃ annotation : Code [] resourcePlan whole,
    annotation.Valid [] actions phases ∧
    Generated actions context.continuationBounds resourceBody annotation :=
  source.initial_source resource_admitted rfl rfl rfl
    (fun _ => List.Subset.refl _) (fun _ => List.Subset.refl _)

end RichWaiting
end Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples


#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples.admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples.scheduled
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples.intermediate_rejected
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples.generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples.RichWaiting.waiting_not_interface
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples.RichWaiting.waiting_bounds_not_absent
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples.RichWaiting.generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples.RichWaiting.resource_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples.RichWaiting.resource_generated

namespace Ash.OneShot.SourceConsumingCleanupAdmission.LeafCaptureExamples
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceScheduledSourceRechecking (OperationSource)
open SourceRetainedPlans (Forest)
open SourceConsumingClauseAnnotations (SelectedSource)
open CaptureExamples

/-- The original capture compiler may use either retained representation.
Both have the same operation-source view of this code-free saved delimiter. -/
theorem saved_view {outside : Forest outsideHints} (original : Retained [] saved outside) :
    OperationSource original (.handler .nil .nil) := by
  cases original with
  | operations interfaces => cases interfaces with
    | handler => rename_i tail; cases tail; exact .operations
  | handler tail =>
      rw [SourceScheduledSourceRechecking.retained_nil_eq tail]
      exact .handler .operations

def interfaces : context.OperationSources where
  resumption := fun _ => .handler .nil .nil
  resumeSource := fun permission => saved_view (context.resumption permission).val
  closing := fun _ => .nil
  closeSource := fun permission => by
    rw [SourceScheduledSourceRechecking.retained_nil_eq (context.closing permission).val]
    exact .operations

/-- Instantiate the stored-source theorem at an actual request and feed its
result to the existing allocator certificate type, without contextual At. -/
theorem allocator_certificate : ∃ certificate : SourceScheduledCaptureAnnotations.Capture [] 19 outer 0 offered
    (some family, some family) plans 1 9 raw saved, certificate.Valid [] actions phases := by
  obtain ⟨annotation, ready, _⟩ := SelectedSource.capture_leaf_interfaces
    (recipeLaws []) (fun evidence => evidence) snapshot snapshot_admitted bounded cut selected
    selected_source source captureSource permits rfl fresh absent interfaces ⟨[], []⟩ rfl
    (fun _ => List.Subset.refl _) (fun _ => List.Subset.refl _) rfl
  exact ⟨.site cut selected annotation, ready⟩

end Ash.OneShot.SourceConsumingCleanupAdmission.LeafCaptureExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafCaptureExamples.saved_view
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafCaptureExamples.allocator_certificate

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.LeafAdmissionExamples.consumed_rejected
