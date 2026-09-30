import SourceConsumingPassiveFocus
import SourceConsumingReceiverMetadataExamples
import SourceConsumingQueuedAdmissionExamples

/-! Derive focused contextual admission from original source alone for saved forests
without code or handler requirements. Rich source constructors, repeated focus,
return and negative phase evidence exercise the derived obligations. Nonempty
saved source separately tests the general context and finite-check transports. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body Generated)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot Returned)

noncomputable def current := (Examples.context Examples.phases).pure_frame (recipeLaws []) (fun evidence => evidence)

theorem resource_nested : Examples.resourceBody.Nested :=
  .cleanup (.resource (fun _ _ => .sequence (.choice .resume .dispose)))

def original : QueuedBody (recipeLaws []) (fun evidence => evidence) [] []
    (Examples.context Examples.phases) Examples.resourceBody.boundAnnotation :=
  ⟨Examples.resourceBody, rfl, Examples.resource_contextual_admitted, resource_nested,
    Examples.resource_source_admitted.at_capture rfl rfl rfl⟩

def parent : Body [4] 19 (.sequence Plan.pure Examples.resourceClause) :=
  .sequence [] .pure .pure Examples.resourceBody

theorem focused : FocusedSource (recipeLaws []) (fun evidence => evidence) [] []
    (Examples.context Examples.phases) Examples.resourceBody.boundAnnotation (.absent (plan := Plan.pure)) :=
  (At.sequence original.source).focused (.sequence resource_nested)
    (show parent.BoundCheck [] [] Examples.actions Examples.phases
      (.live 19 .nil (.cell 4 .nil)) (.cell 4 .nil) .nil from ⟨rfl, original.checked⟩) (.pairRight _)

/-- The record comes from the actual bound focus split; no receiver or finite
checks for the expanded context are supplied here. -/
theorem focused_source : Nonempty (QueuedBody (recipeLaws []) (fun evidence => evidence) [] []
    current Examples.resourceBody.boundAnnotation) := focused.current_passive .nil

noncomputable def twice := (original.focus_passive .nil).focus_passive .nil

theorem repeated_source : At (recipeLaws []) (fun evidence => evidence) twice.body
    (current.pure_frame (recipeLaws []) (fun evidence => evidence)) := twice.source

theorem repeated_original_body : twice.body = original.body := rfl

theorem generated_source : ∃ annotation : Code [4] Examples.resourceClause (.plain Plan.pure Examples.whole),
    annotation.Valid [] Examples.actions Examples.phases ∧
    Generated Examples.actions (Examples.context Examples.phases).continuationBounds original.body annotation :=
  original.focus_passive_generated .nil

/-- Full nested-handler source admission follows without caller-supplied
ReceiverChecks; its finite checks also follow from the original contract. -/
theorem wrapped_source :
    At (recipeLaws []) (fun evidence => evidence) HandlerExamples.wrappedBody current ∧
    ∃ annotation : Code [4] HandlerExamples.wrapped (.plain Plan.pure Examples.whole),
      annotation.Valid [] Examples.actions Examples.phases ∧
      Generated Examples.actions (Examples.context Examples.phases).continuationBounds HandlerExamples.wrappedBody annotation :=
  (ReceiverChecks.passive_saved HandlerExamples.wrappedBody .nil current).generate HandlerExamples.wrapped_admitted
    ((Examples.context Examples.phases).pure_frame_bounds)
    ((Examples.context Examples.phases).pure_frame_checked (HandlerExamples.wrapped_source.at_capture rfl rfl rfl))

theorem focused_return {next : Snapshot [4]}
    (pending : SourceBoundSnapshots.Retained [4] (.plain Plan.pure Examples.whole))
    (step : Returned QueuedExamples.bindingPosition
      ⟨_, Plan.pure, .absent, _, _, _, .plain Examples.resourceBody.boundAnnotation pending⟩ next) :
    ∃ nextQueued : QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] current
        (Examples.resourceBody.boundAnnotation.plug QueuedExamples.bindingPosition).2.2,
      next = ⟨_, _, nextQueued.body.boundAnnotation, _, _, .plain Plan.pure Examples.whole, pending⟩ := by
  obtain ⟨source⟩ := focused_source
  exact source.returned QueuedExamples.bindingPosition (.absent (plan := Plan.pure)) pending step

/-- Pure frames do not restore a consumed continuation permission phase. -/
theorem spent_owner_rejected : ¬ Examples.resourceBody.BoundCheck [] [] Examples.actions
    (OwnerPhaseTransitions.spend Examples.phases 19)
    (.plain .pure (.live 19 .nil (.cell 4 .nil))) (.cell 4 .nil) current.before := by
  intro checked
  have impossible := Examples.resourceBody.boundCheck_available checked
  simp only [OwnerPhaseTransitions.spend] at impossible
  cases impossible

/-- The context compiler is not restricted to empty saved work: its exact
metadata proof retains the prior example's explicit saved handler bounds. -/
theorem rich_metadata : ReceiverMetadataExamples.richContext.BoundsAgree
    (ReceiverMetadataExamples.richContext.pure_frame (recipeLaws []) (fun evidence => evidence)) :=
  ReceiverMetadataExamples.richContext.pure_frame_bounds

theorem nonempty_finite_checks : HandlerExamples.body.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
    (.plain .pure (.live 19 (.plain (.request SourceDependencyCapture.Examples.effectE 0) .nil)
      (.handler SourceDependencyCapture.Examples.effectE SourceDependencyCapture.Examples.resumeTable
        SourceDependencyCapture.Examples.resumeDependencies .nil)))
    (.handler SourceDependencyCapture.Examples.effectE SourceDependencyCapture.Examples.resumeTable
      SourceDependencyCapture.Examples.resumeDependencies .nil)
    (HandlerExamples.context.pure_frame (recipeLaws []) (fun evidence => evidence)).before :=
  HandlerExamples.context.pure_frame_checked HandlerExamples.checked

/-- The base case includes a nonempty capture at an actual handler delimiter. -/
def delimiter : SourceRetainedPlans.Forest (SourceContextualHints.Hints.handler
    (effect := SourceDependencyCapture.Examples.effectE)
    (table := SourceDependencyCapture.Examples.resumeTable)
    (families := SourceDependencyCapture.Examples.resumeDependencies) [] .nil) := .handler .nil

theorem delimiter_cut : ∃ contract modes, SourceScheduledNeutral.Cut
    SourceDependencyCapture.Examples.effectE 0 contract modes delimiter delimiter .nil :=
  ⟨_, _, .hit rfl rfl⟩

def delimiterContext : Context [] 19 [] ReceiverMetadataExamples.actions ReceiverMetadataExamples.phases
    (.live (owner := 19) delimiter .nil) .nil delimiter .nil where
  cut := .hit
  before := .nil
  resumption := fun _ => ⟨.handler (.operations .nil), ⟨rfl, rfl⟩⟩
  closing := fun impossible => False.elim (Bool.noConfusion impossible)
  disposal := fun impossible => False.elim (Bool.noConfusion impossible)
  after := .operations .nil
  tailReady := rfl

def delimiterBody : Body [] 19 (.sequence Plan.pure (Plan.invoke (key := ⟨19, .resume⟩))) :=
  .sequence [] .pure .pure .resume

def delimiterRecord : QueuedBody (recipeLaws []) (fun evidence => evidence) [] []
    delimiterContext delimiterBody.boundAnnotation :=
  ⟨delimiterBody, rfl, .sequence .resume, .sequence .resume, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem delimiter_capture : SourceBoundSnapshots.Captured 19
    ⟨_, Plan.request (effect := SourceDependencyCapture.Examples.effectE) (operation := 0),
      .absent, _, _, delimiter, .handler .nil⟩
    ⟨_, _, delimiterBody.boundAnnotation, _, _, .live (owner := 19) delimiter .nil, .live (.handler .nil) .nil⟩ :=
  SourceBoundSnapshots.Captured.cut
    (Annotation.absent (plan := Plan.request (effect := SourceDependencyCapture.Examples.effectE) (operation := 0)))
    delimiterBody.boundAnnotation
    (SourceBoundSnapshots.Retained.handler .nil : SourceBoundSnapshots.Retained [] delimiter)
    (SourceBoundSnapshots.Retained.nil : SourceBoundSnapshots.Retained [] .nil)

theorem delimiter_focused : ∃ annotation : Code []
    (.sequence Plan.pure (Plan.invoke (key := ⟨19, .resume⟩)))
    (.plain Plan.pure (.live (owner := 19) delimiter .nil)),
    annotation.Valid [] ReceiverMetadataExamples.actions ReceiverMetadataExamples.phases ∧
    Generated ReceiverMetadataExamples.actions delimiterContext.continuationBounds delimiterBody annotation :=
  delimiterRecord.focus_passive_generated (.handler .nil)

/-- The structural base case cannot silently admit saved pending code. -/
theorem pending_source_excluded : ¬ PassiveSaved HandlerExamples.saved := by
  intro passive
  cases passive

theorem callbacks_excluded : ¬ PassiveSaved
    (SourceRetainedPlans.Forest.cleanup (needs := [.cell 4])
      (Plan.request (effect := .cell 4) (operation := 0)) .nil) := by
  intro passive
  cases passive

end Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.resource_nested
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.focused
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.focused_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.repeated_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.repeated_original_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.generated_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.wrapped_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.focused_return
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.spent_owner_rejected
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.rich_metadata
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.nonempty_finite_checks

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.delimiter_cut
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.delimiter_capture
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.delimiter_focused
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.pending_source_excluded
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveFocusExamples.callbacks_excluded
