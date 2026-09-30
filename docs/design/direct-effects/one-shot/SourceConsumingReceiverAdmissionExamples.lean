import SourceConsumingReceiverAdmission
import SourceConsumingQueuedRecordExamples

/-! Reconstruct source admission at a changed ordered caller. The main example
keeps a nonempty saved request and admits a nested disposing interpretation.
Separate examples cover all other source constructors and show that receiver
checks do not replace original cleanup dependency coverage. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples
open SourceConsumingClauseAnnotations (Body Generated)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceScheduledSourceRechecking (Expression ReceiverChange)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceDependencyCapture.Examples (effectE disposeTable disposeDependencies resumeTable resumeDependencies)
open OwnerPhaseTransitions (spend)

/-- A real additional interpretation is installed around the original caller.
The saved request still reaches its original resumptive interpretation until
the source body's inner disposing interpretation is entered. -/
def caller : Forest (SourceContextualHints.Hints.handler
    (effect := .user 99 []) (table := []) (families := []) [] .nil) := .handler .nil
def whole := Forest.handler (effect := .user 99 []) (table := []) (families := []) (required := []) HandlerExamples.whole

def current : Context [] 19 [] HandlerExamples.actions HandlerExamples.phases
    whole caller HandlerExamples.saved HandlerExamples.waiting where
  cut := .handler .hit
  before := .handler .nil .nil
  resumption := fun _ => ⟨.plain (.operations [(effectE, 0)] .request .request) (.operations .nil), ⟨rfl, rfl⟩⟩
  closing := fun _ => ⟨.operations .nil, rfl⟩
  disposal := HandlerExamples.context.disposal
  after := HandlerExamples.context.after
  tailReady := HandlerExamples.context.tailReady

theorem metadata : HandlerExamples.context.BoundsAgree current := ⟨fun _ => rfl, fun _ => rfl, rfl⟩

theorem resumption_rechecked (permission) : ReceiverChange [] HandlerExamples.actions
    (spend HandlerExamples.phases 19) (current.resumption permission).val
    (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := [])
      (caller.append (.spent (owner := 19) HandlerExamples.waiting))) := by
  apply ReceiverChange.plain
  · exact Expression.freshInterfaces (.hit rfl rfl) (.handler (.spent (.handler .nil)))
      (.handler (.spent (.handler .nil))) (.handler (.spent (.handler .nil)))
      (fun _ => rfl) (by decide) (fun _ => .handler .nil)
  · exact .empty

theorem receiver_checks : ReceiverChecks (recipeLaws []) (fun evidence => evidence)
    HandlerExamples.actions HandlerExamples.phases HandlerExamples.body current :=
  .handler resumption_rechecked (fun _ => .empty) (.choice .resume .dispose)

theorem finite_checks : HandlerExamples.body.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
    (.handler (.user 99 []) [] [] (.live 19 (.plain (.request effectE 0) .nil)
      (.handler effectE resumeTable resumeDependencies .nil)))
    (.handler effectE resumeTable resumeDependencies .nil) current.before := ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩⟩

theorem generated_at_changed_caller :
    At (recipeLaws []) (fun evidence => evidence) HandlerExamples.body current ∧
    ∃ annotation : Code [] HandlerExamples.clause whole,
      annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
      Generated HandlerExamples.actions HandlerExamples.context.continuationBounds HandlerExamples.body annotation :=
  receiver_checks.generate HandlerExamples.admitted metadata finite_checks

def activated := QueuedExamples.queued.recheck metadata receiver_checks finite_checks

theorem original_body_retained : activated.val.body = QueuedExamples.queued.body := activated.property.1

theorem activated_source : At (recipeLaws []) (fun evidence => evidence) activated.val.body current :=
  activated.val.source

theorem activated_return {next : SourceBoundSnapshots.Snapshot []}
    (pending : SourceBoundSnapshots.Retained [] whole)
    (step : SourceBoundSnapshots.Returned QueuedExamples.bindingPosition
      ⟨_, Plan.pure, .absent, _, _, _, .plain HandlerExamples.body.boundAnnotation pending⟩ next) :
    ∃ nextQueued : QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] current
        (HandlerExamples.body.boundAnnotation.plug QueuedExamples.bindingPosition).2.2,
      next = ⟨_, _, nextQueued.body.boundAnnotation, _, _, whole, pending⟩ :=
  activated.val.returned QueuedExamples.bindingPosition (.absent (plan := Plan.pure)) pending step

/-- The source recovered from the captured record can carry a different proof
witness. Its indexed source syntax supplies these same primitive checks. -/
theorem handler_body_checks (body : Body [] 19 HandlerExamples.clause) :
    ReceiverChecks (recipeLaws []) (fun evidence => evidence)
      HandlerExamples.actions HandlerExamples.phases body current ∧
    body.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
      (.handler (.user 99 []) [] [] (.live 19 (.plain (.request effectE 0) .nil)
        (.handler effectE resumeTable resumeDependencies .nil)))
      (.handler effectE resumeTable resumeDependencies .nil) current.before := by
  cases body with
  | handler bounds declared inner =>
      cases inner with
      | choice first second =>
          cases first
          cases second
          exact ⟨.handler resumption_rechecked (fun _ => .empty) (.choice .resume .dispose),
            rfl, ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩⟩

noncomputable def restoredActivation := RecordExamples.restoredSource.recheck metadata
  (handler_body_checks _).1 (handler_body_checks _).2

theorem restored_activation_source : At (recipeLaws []) (fun evidence => evidence)
    restoredActivation.val.body current := restoredActivation.val.source

theorem restored_original_body : restoredActivation.val.body = RecordExamples.restoredSource.body :=
  restoredActivation.property.1

theorem restored_activated_return {next : SourceBoundSnapshots.Snapshot []}
    (pending : SourceBoundSnapshots.Retained [] whole)
    (step : SourceBoundSnapshots.Returned QueuedExamples.bindingPosition
      ⟨_, Plan.pure, .absent, _, _, _, .plain HandlerExamples.body.boundAnnotation pending⟩ next) :
    ∃ nextQueued : QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] current
        (HandlerExamples.body.boundAnnotation.plug QueuedExamples.bindingPosition).2.2,
      next = ⟨_, _, nextQueued.body.boundAnnotation, _, _, whole, pending⟩ :=
  restoredActivation.val.returned QueuedExamples.bindingPosition (.absent (plan := Plan.pure)) pending step

/-- Reuse the earlier nested-handler, effectful-cleanup and fresh-resource
source under another caller. Empty saved work discharges only the receiver
interference obligations, not the source's cleanup dependency coverage. -/
noncomputable def resourceCurrent := (Examples.context Examples.phases).handler
  (recipeLaws []) (fun evidence => evidence) (.user 101 []) [] [] []
  (fun _ => .empty) (fun _ => .empty)

theorem resource_receiver_checks : ReceiverChecks (recipeLaws []) (fun evidence => evidence)
    Examples.actions Examples.phases HandlerExamples.wrappedBody resourceCurrent := by
  apply ReceiverChecks.handler (fun _ => .empty) (fun _ => .empty)
  apply ReceiverChecks.handler (fun _ => .empty) (fun _ => .empty)
  exact .cleanup (fun _ => .empty) (fun _ => .empty)
    (.resource (fun _ _ => .sequence (.choice .resume .dispose)))

theorem resource_source : At (recipeLaws []) (fun evidence => evidence)
    HandlerExamples.wrappedBody resourceCurrent :=
  resource_receiver_checks.reconstruct HandlerExamples.wrapped_admitted

/-- Receiver checks alone deliberately do not establish source admission. -/
theorem incomplete_coverage_checks : ReceiverChecks (recipeLaws []) (fun evidence => evidence)
    Examples.actions Examples.phases (Examples.body []) resourceCurrent :=
  .cleanup (fun _ => .empty) (fun _ => .empty) (.sequence (.choice .resume .dispose))

theorem incomplete_coverage_rejected : ¬ At (recipeLaws []) (fun evidence => evidence)
    (Examples.body []) resourceCurrent := by
  intro admitted
  have impossible := admitted.cleanup_dependencies (.cell 4, 0) (by simp)
  cases impossible

end Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.metadata
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.resumption_rechecked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.receiver_checks
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.finite_checks
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.generated_at_changed_caller
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.original_body_retained
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.activated_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.activated_return
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.resource_receiver_checks
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.resource_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.incomplete_coverage_checks
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.incomplete_coverage_rejected

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.handler_body_checks
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.restored_activation_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.restored_original_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.RecheckingExamples.restored_activated_return
