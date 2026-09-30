import SourceConsumingNeutralGeneration
import SourceConsumingPassiveFocusExamples

/-! General neutral admission with saved requests, saved callbacks, nonempty
handler requirements and explicit retained bounds. Repeated focus and source
descent use the same admission APIs as the original derivation. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body Generated)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open SourceScheduledSourceRechecking (ReceiverChange)
open SourcePlanBounds (Annotation)

theorem saved_request_focus : Nonempty (QueuedBody (recipeLaws []) (fun evidence => evidence) [] []
    (HandlerExamples.context.pure_frame (recipeLaws []) (fun evidence => evidence))
    HandlerExamples.body.boundAnnotation) := QueuedExamples.consuming_current.current_neutral

theorem saved_request_generated : ∃ annotation : Code [] HandlerExamples.clause
    (.plain Plan.pure HandlerExamples.whole),
    annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
    Generated HandlerExamples.actions HandlerExamples.context.continuationBounds HandlerExamples.body annotation :=
  QueuedExamples.queued.focus_neutral_generated

/-- Both constructors apply to the new neutral admission derivation, including
the handler that changes saved-request selection to disposal. -/
theorem repeated_focus : ∃ annotation : Code [] HandlerExamples.clause
    (.plain Plan.pure (.plain Plan.pure HandlerExamples.whole)),
    annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
    Generated HandlerExamples.actions HandlerExamples.context.continuationBounds HandlerExamples.body annotation := by
  obtain ⟨annotation, ready, generated⟩ := QueuedExamples.queued.focus_neutral.focus_neutral_generated
  change Generated HandlerExamples.actions
    (HandlerExamples.context.pure_frame (recipeLaws []) (fun evidence => evidence)).continuationBounds
    HandlerExamples.body annotation at generated
  exact ⟨annotation, ready, by
    simpa only [(HandlerExamples.context.pure_frame_bounds (laws := recipeLaws []) (project := fun evidence => evidence)).continuationBounds_eq]
      using generated⟩

theorem after_focus_children : Descendants (recipeLaws []) (fun evidence => evidence) HandlerExamples.body
    (HandlerExamples.context.pure_frame (recipeLaws []) (fun evidence => evidence)) :=
  QueuedExamples.queued.focus_neutral.source.descendants

def callback := Plan.request (effect := .cell 4) (operation := 0)
def waiting : Forest (Hints.cell (identity := 4) .nil) := .cell .nil
def saved : Forest (Hints.handler (effect := .user 81 []) (table := []) (families := [])
    [(.cell 4, 0)] (.cleanup (needs := [.cell 4])
      (callback := SourceDependencyAnnotations.Dependencies.request (.cell 4) 0) .nil)) :=
  .handler (.cleanup callback .nil)
def whole := Forest.live (owner := 19) saved waiting
def actions := ReceiverMetadataExamples.actions
def phases := ReceiverMetadataExamples.phases

def context : Context [4] 19 [] actions phases whole .nil saved waiting where
  cut := .hit
  before := .nil
  resumption := fun _ => ⟨.handler (.cleanup (.operations [(.cell 4, 0)] .request .request) (.operations .nil)),
    ⟨rfl, rfl, rfl⟩⟩
  closing := fun impossible => False.elim (Bool.noConfusion impossible)
  disposal := fun impossible => False.elim (Bool.noConfusion impossible)
  after := .cell (.operations .nil)
  tailReady := rfl

def clause := Plan.cleanup (needs := [.cell 4]) callback
  (Plan.resource (fun _ => .sequence Plan.pure
    (.choice (.invoke (key := ⟨19, .resume⟩)) (.invoke (key := ⟨19, .resume⟩)))))
def body : Body [4] 19 clause :=
  .cleanup [(.cell 4, 0)] .request .request
    (.resource (fun _ _ => .sequence [] .pure .pure (.choice .resume .resume)))

theorem original_source : At (recipeLaws []) (fun evidence => evidence) body context := by
  refine .cleanupSource ?_ ?_ ?_ (.resource (fun _ _ => .sequence (.choice .resume .resume)))
  · intro request member
    exact List.mem_singleton.mpr (congrArg Prod.fst (List.mem_singleton.mp member))
  · intro permission
    exact ReceiverChange.handler rfl (.cleanup (.operations rfl) .empty)
  · intro impossible
    exact False.elim (Bool.noConfusion impossible)

theorem original_checked : body.BoundCheck [] [] actions phases
    (.live 19 (.handler (.user 81 []) [] [] (.cleanup [.cell 4] (.request (.cell 4) 0) .nil))
      (.cell 4 .nil)) (.cell 4 .nil) context.before := by
  refine ⟨(fun _ _ => ⟨rfl, ?_, ?_⟩), rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩

def queued : QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] context body.boundAnnotation :=
  ⟨body, rfl, original_source,
    .cleanup (.resource (fun _ _ => .sequence (.choice .resume .resume))), original_checked⟩

theorem saved_callback_generated : ∃ annotation : Code [4] clause (.plain Plan.pure whole),
    annotation.Valid [] actions phases ∧ Generated actions context.continuationBounds body annotation :=
  queued.focus_neutral_generated

theorem saved_callback_children : Descendants (recipeLaws []) (fun evidence => evidence) body
    (context.pure_frame (recipeLaws []) (fun evidence => evidence)) := queued.focus_neutral.source.descendants

theorem saved_callback_not_passive : ¬ PassiveSaved saved := by
  intro passive
  cases passive

/-- The new rule still requires exact saved metadata. It cannot turn a valid
but metadata-erased witness into the original saved source. -/
theorem erased_metadata_rejected : ¬ ReceiverMetadataExamples.richContext.BoundsAgree
    (ReceiverMetadataExamples.erasedContext.pure_frame (recipeLaws []) (fun evidence => evidence)) := by
  intro changed
  have kept := ReceiverMetadataExamples.erasedContext.pure_frame_bounds
    (laws := recipeLaws []) (project := fun evidence => evidence)
  have impossible := (changed.resumption (by rfl)).symm.trans (kept.resumption (by rfl))
  cases impossible

end Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples.saved_request_focus
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples.saved_request_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples.repeated_focus
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples.after_focus_children
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples.original_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples.original_checked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples.saved_callback_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples.saved_callback_children
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples.saved_callback_not_passive
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.NeutralGenerationExamples.erased_metadata_rejected
