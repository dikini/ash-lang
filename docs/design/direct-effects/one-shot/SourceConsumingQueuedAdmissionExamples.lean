import SourceConsumingQueuedTransport
import SourceConsumingAdmissionComputationExamples

/-! Focus and return retain source evidence for a handler-bearing clause with
a nonempty saved request. The prefix itself performs an effect. Separate
examples cover argument focus, consuming-current focus, source recomposition,
world/phase/permission transport and rejection of erased queued bounds. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot Returned)
open SourceDependencyCapture.Examples (effectE resumeTable resumeDependencies)
open OwnerPhaseTransitions (available spend)

def prefixPlan := Plan.request (effect := effectE) (operation := 0)
def programPlan := Plan.sequence prefixPlan HandlerExamples.clause
def program : Body [] 19 programPlan := .sequence [(effectE, 0)] .request .request HandlerExamples.body

theorem program_source : At (recipeLaws []) (fun evidence => evidence) program HandlerExamples.context :=
  .sequence HandlerExamples.admitted
theorem program_nested : program.Nested := .sequence ComputationExamples.handler_nested
theorem program_checked : program.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
    (.live 19 (.plain (.request effectE 0) .nil) (.handler effectE resumeTable resumeDependencies .nil))
    (.handler effectE resumeTable resumeDependencies .nil) .nil := ⟨by decide, HandlerExamples.checked⟩

def queued : QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] HandlerExamples.context
    HandlerExamples.body.boundAnnotation :=
  ⟨HandlerExamples.body, rfl, HandlerExamples.admitted, ComputationExamples.handler_nested, HandlerExamples.checked⟩

/-- The effectful child is checked at the actual receiver with its consuming
rest queued. Its source record comes from the parent admission. -/
theorem effectful_focus : FocusedSource (recipeLaws []) (fun evidence => evidence) [] [] HandlerExamples.context
    (Annotation.absent (plan := prefixPlan)) HandlerExamples.body.boundAnnotation :=
  program_source.focused program_nested program_checked (.sequence _)

theorem effectful_child_valid :
    ∃ annotation : Code [] prefixPlan (.plain HandlerExamples.clause HandlerExamples.whole),
      annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
      SourcePlanBounds.ofCode annotation = Annotation.absent := effectful_focus.child_valid

def applicationPlan := Plan.sequence .pure programPlan
def applicationBody : Body [] 19 applicationPlan := .sequence [] .pure .pure program

/-- Argument focus queues the same consuming rest after the function value
has been selected. It does not ask for another queued-source derivation. -/
theorem argument_focus : FocusedSource (recipeLaws []) (fun evidence => evidence) [] [] HandlerExamples.context
    (Annotation.absent (plan := prefixPlan)) HandlerExamples.body.boundAnnotation :=
  (At.sequence program_source).focused (.sequence program_nested)
    (show applicationBody.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
      _ _ HandlerExamples.context.before from ⟨rfl, program_checked⟩) (.appArgument _)

/-- Pair-right leaves the consuming code current under a pure pending frame.
The current record deliberately retains its original contextual derivation. -/
theorem consuming_current : FocusedSource (recipeLaws []) (fun evidence => evidence) [] [] HandlerExamples.context
    HandlerExamples.body.boundAnnotation (Annotation.absent (plan := Plan.pure)) :=
  ComputationExamples.bind_source.focused (.sequence ComputationExamples.handler_nested)
    ⟨rfl, HandlerExamples.checked⟩ (.pairRight _)

theorem consuming_child_valid :
    ∃ annotation : Code [] HandlerExamples.clause (.plain Plan.pure HandlerExamples.whole),
      annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
      SourcePlanBounds.ofCode annotation = HandlerExamples.body.boundAnnotation := consuming_current.child_valid

def bindingPosition : SourceAnnotatedCode.Context := .bind .unit 3 (.unit .unit)
def argumentPosition : SourceAnnotatedCode.Context := .appArgument .unit (.unit .unit)

/-- The returned snapshot is fixed by the actual queued record. No independent
successful admission of its recomposed body is supplied. -/
theorem returned_source (pending : SourceBoundSnapshots.Retained [] HandlerExamples.whole)
    {next : Snapshot []}
    (step : Returned bindingPosition
      ⟨_, Plan.pure, .absent, _, _, .plain HandlerExamples.clause HandlerExamples.whole,
        .plain HandlerExamples.body.boundAnnotation pending⟩ next) :
    ∃ nextQueued : QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] HandlerExamples.context
        (HandlerExamples.body.boundAnnotation.plug bindingPosition).2.2,
      next = ⟨_, _, nextQueued.body.boundAnnotation, _, _, HandlerExamples.whole, pending⟩ :=
  by
    obtain ⟨savedSource⟩ := effectful_focus.queued_body HandlerExamples.body
    exact savedSource.returned bindingPosition (Annotation.absent (plan := Plan.pure)) pending step

/-- Recomposition followed by the ordinary bind or beta rule recovers the
original admitted handler body. Both steps reuse their generic proofs. -/
theorem return_then_compute :
    At (recipeLaws []) (fun evidence => evidence) HandlerExamples.body HandlerExamples.context ∧
    ∃ annotation : Code [] HandlerExamples.clause HandlerExamples.whole,
      annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
      SourcePlanBounds.ofCode annotation = HandlerExamples.body.boundAnnotation := by
  let bound := queued.plug bindingPosition
  have first := bound.source.reduce bound.checked
    (show bound.body.Reduction .bind HandlerExamples.body from .bind)
  let argument := queued.plug argumentPosition
  have second := argument.source.reduce argument.checked
    (show argument.body.Reduction .beta HandlerExamples.body from .beta)
  exact ⟨first.1, second.1.generate_retaining second.2⟩

def nextActions := HandlerExamples.actions.insert 88 ⟨true, true⟩
def nextPhases := spend (available [19, 88]) 88
theorem permission_extension : Syntax.UsageExtension HandlerExamples.actions nextActions :=
  Syntax.fresh_usage_insert_extends rfl
theorem availability : SourceScheduledPhaseRestriction.AvailableOn
    (SourceDependencyOwners.owners
      (.live 19 (.plain (.request effectE 0) .nil) (.handler effectE resumeTable resumeDependencies .nil)))
    HandlerExamples.phases nextPhases := by
  intro owner member _
  change owner ∈ [19] at member
  have same := List.mem_singleton.mp member
  subst owner
  rfl

/-- A queued record retains its actual source after an unrelated owner is
allocated and spent and the resource world grows. -/
def transported := queued.transport permission_extension rfl availability (show [] ⊆ [7] from by simp)

theorem transported_origin : transported.body.boundAnnotation =
    HandlerExamples.body.boundAnnotation.world_weaken (show [] ⊆ [7] from by simp) := transported.origin.symm

theorem transported_return :
    At (recipeLaws []) (fun evidence => evidence) (transported.plug argumentPosition).body
      (((HandlerExamples.context.extend_permissions permission_extension rfl).restrict_phases availability).world_weaken
        (show [] ⊆ [7] from by simp)) := (transported.plug argumentPosition).source

/-- No different source witness at this handler plan can justify erasing its
explicit queued handler packet. -/
theorem erased_queue_rejected :
    ¬ Nonempty (QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] HandlerExamples.context
      (Annotation.absent (plan := HandlerExamples.clause))) := by
  rintro ⟨source⟩
  rcases source with ⟨body, origin, _, _, _⟩
  cases body with
  | handler bounds declared body => cases origin

end Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.program_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.program_nested
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.program_checked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.effectful_focus
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.effectful_child_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.argument_focus
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.consuming_current
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.consuming_child_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.returned_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.return_then_compute
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.permission_extension
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.availability
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.transported_origin
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.transported_return
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedExamples.erased_queue_rejected
