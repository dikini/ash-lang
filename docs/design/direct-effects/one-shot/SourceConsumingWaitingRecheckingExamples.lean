import SourceConsumingWaitingRechecking
import SourceConsumingQueuedAdmissionExamples

/-! Non-neutral waiting restoration can change a saved operation from resumption
to disposal. These are source/context examples, not a full runtime trace. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.WaitingRecheckingExamples
open SourceConsumingClauseAnnotations (Body Generated)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceScheduledSourceRechecking (Expression ReceiverChange RetainedBounds)
open SourceRetainedPlans (Forest)
open SourceDependencyCapture.Examples (effectE disposeTable disposeDependencies resumeTable resumeDependencies)
open OwnerPhaseTransitions (spend)

def nextWaiting : Forest (SourceContextualHints.Hints.handler
    (effect := effectE) (table := disposeTable) (families := disposeDependencies) []
    (SourceContextualHints.Hints.handler
      (effect := effectE) (table := resumeTable) (families := resumeDependencies) [] .nil)) :=
  .handler HandlerExamples.waiting
def nextWhole := Forest.live (owner := 19) HandlerExamples.saved nextWaiting

def body : Body [] 19 (.invoke (key := ⟨19, .resume⟩)) := .resume
def queued : QueuedBody (recipeLaws []) (fun evidence => evidence) [] []
    HandlerExamples.context body.boundAnnotation :=
  ⟨body, rfl, .resume, .resume, rfl, rfl, rfl, rfl⟩

/-- The nearer interpretation now disposes. Derive its actual selection and
closing checks from the existing fresh-interception rule. -/
theorem resumption_rechecked (permission) : ReceiverChange [] HandlerExamples.actions
    (spend HandlerExamples.phases 19) (HandlerExamples.context.resumption permission).val
    (.spent (owner := 19) nextWaiting) := by
  apply ReceiverChange.plain
  · exact Expression.freshInterfaces (.spent (.hit rfl rfl)) (.spent (.handler .nil))
      (.spent (.handler .nil)) (.spent (.handler .nil))
      (fun _ => rfl) (by decide) (fun _ => .spent (.handler .nil))
  · exact .empty

/-- This case is outside the neutral theorem: operation-only availability
changes when the new interpretation offers disposal. -/
theorem not_neutral : ¬ SourceScheduledNeutral.Expansion HandlerExamples.waiting nextWaiting := by
  intro changed
  have impossible := changed.erase.requirements (required := [(effectE, 0)])
  change true = false at impossible
  cases impossible

/-- Construct the changed context and complete source record from structural
rechecking, then generate its resumed code. Target validity is never supplied. -/
theorem restored_source :
    ∃ current : Context [] 19 [] HandlerExamples.actions HandlerExamples.phases
        nextWhole .nil HandlerExamples.saved nextWaiting,
      current.before = .nil ∧ HandlerExamples.context.SavedAgree current ∧
      RetainedBounds HandlerExamples.context.after (SourceBoundSnapshots.Retained.ofCapability current.after) ∧
      Nonempty (QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] current body.boundAnnotation) ∧
      ∃ annotation : Code [] (.invoke (key := ⟨19, .resume⟩)) nextWhole,
        annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
        Generated HandlerExamples.actions current.continuationBounds body annotation := by
  obtain ⟨current, caller, saved, tail⟩ := HandlerExamples.context.recheck_waiting_retaining
    (laws := recipeLaws []) (project := fun evidence => evidence)
    (nextWhole := nextWhole) .hit .nil resumption_rechecked (fun _ => .empty) (.install rfl)
  have checked : body.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
      (.live 19 (.plain (.request effectE 0) .nil)
        (.handler effectE disposeTable disposeDependencies (.handler effectE resumeTable resumeDependencies .nil)))
      (.handler effectE disposeTable disposeDependencies (.handler effectE resumeTable resumeDependencies .nil))
      current.before := by
    rw [caller]
    exact ⟨rfl, rfl, rfl, rfl⟩
  let restored := queued.recheck_waiting saved tail .resume checked
  exact ⟨current, caller, saved, tail, ⟨restored.val⟩,
    queued.generate_rechecked_waiting saved tail .resume checked⟩

def maskedWaiting : Forest (SourceContextualHints.Hints.handler
    (effect := effectE) (table := []) (families := []) []
    (SourceContextualHints.Hints.handler
      (effect := effectE) (table := resumeTable) (families := resumeDependencies) [] .nil)) :=
  .handler HandlerExamples.waiting
def maskedWhole := Forest.live (owner := 19) HandlerExamples.saved maskedWaiting

/-- Local owner and empty operation-interface checks still pass. They cannot
replace rechecking the saved request's actual interpretation. -/
theorem masking_finite_checks : body.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
    (.live 19 (.plain (.request effectE 0) .nil)
      (.handler effectE [] [] (.handler effectE resumeTable resumeDependencies .nil)))
    (.handler effectE [] [] (.handler effectE resumeTable resumeDependencies .nil))
    (SourceScheduledRetainedInterfaces.Interfaces.nil (world := [])) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- No annotation choice can construct the masked context: compilation would
give a request guard that the existing exact selection check rejects. -/
theorem masking_context_rejected : ¬ Nonempty
    (Context [] 19 [] HandlerExamples.actions HandlerExamples.phases
      maskedWhole .nil HandlerExamples.saved maskedWaiting) := by
  intro ⟨current⟩
  have scheduled := (current.resumption (by rfl)).val.compile_with (recipeLaws [])
    (current.resumption (by rfl)).property
  cases scheduled with
  | plain request tail => cases request with
    | request guard closing =>
      have impossible := SourceDependencySchemes.checked_request guard
      change false = true at impossible
      cases impossible

namespace Repeated

/-- A second waiting change restores a resumptive interpretation in front of
the disposer installed by the first change. -/
def waiting : Forest (SourceContextualHints.Hints.handler
    (effect := effectE) (table := resumeTable) (families := resumeDependencies) []
    (SourceContextualHints.Hints.handler
      (effect := effectE) (table := disposeTable) (families := disposeDependencies) []
      (SourceContextualHints.Hints.handler
        (effect := effectE) (table := resumeTable) (families := resumeDependencies) [] .nil))) :=
  .handler nextWaiting
def whole := Forest.live (owner := 19) HandlerExamples.saved waiting

/-- This accepts the first reconstruction's actual, existentially generated
annotation. It cannot rely on a particular compiler annotation constructor. -/
theorem resumption_rechecked
    (original : Context [] 19 [] HandlerExamples.actions HandlerExamples.phases
      nextWhole .nil HandlerExamples.saved nextWaiting) (permission) :
    ReceiverChange [] HandlerExamples.actions (spend HandlerExamples.phases 19)
      (original.resumption permission).val (.spent (owner := 19) waiting) :=
  .request (SourceContextualRequirements.check_capability_iff.mp rfl)

/-- Compose two non-neutral context reconstructions and produce a complete
queued source record at the second receiver. Saved bounds remain exact across
both changes; waiting bounds follow the existing provenance relation. -/
theorem restored_twice :
    ∃ current : Context [] 19 [] HandlerExamples.actions HandlerExamples.phases
        whole .nil HandlerExamples.saved waiting,
      HandlerExamples.context.SavedAgree current ∧
      Nonempty (QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] current body.boundAnnotation) ∧
      ∃ annotation : Code [] (.invoke (key := ⟨19, .resume⟩)) whole,
        annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
        Generated HandlerExamples.actions current.continuationBounds body annotation := by
  obtain ⟨original, originalCaller, originalSaved, _, _, _⟩ := restored_source
  have originalChecked : body.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
      (.live 19 (.plain (.request effectE 0) .nil) (.handler effectE disposeTable disposeDependencies (.handler effectE resumeTable resumeDependencies .nil)))
      (.handler effectE disposeTable disposeDependencies (.handler effectE resumeTable resumeDependencies .nil)) original.before := by
    rw [originalCaller]
    exact ⟨rfl, rfl, rfl, rfl⟩
  let originalQueued : QueuedBody (recipeLaws []) (fun evidence => evidence) [] [] original body.boundAnnotation :=
    ⟨body, rfl, .resume, .resume, originalChecked⟩
  obtain ⟨current, caller, saved, tail⟩ := original.recheck_waiting_retaining
    (laws := recipeLaws []) (project := fun evidence => evidence)
    (nextWhole := whole) .hit .nil (resumption_rechecked original) (fun _ => .empty) (.install rfl)
  have checked : body.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
      (.live 19 (.plain (.request effectE 0) .nil) (.handler effectE resumeTable resumeDependencies (.handler effectE disposeTable disposeDependencies (.handler effectE resumeTable resumeDependencies .nil))))
      (.handler effectE resumeTable resumeDependencies (.handler effectE disposeTable disposeDependencies (.handler effectE resumeTable resumeDependencies .nil))) current.before := by
    rw [caller]
    exact ⟨rfl, rfl, rfl, rfl⟩
  let restored := originalQueued.recheck_waiting saved tail .resume checked
  exact ⟨current, originalSaved.trans saved, ⟨restored.val⟩,
    originalQueued.generate_rechecked_waiting saved tail .resume checked⟩

end Repeated

end Ash.OneShot.SourceConsumingCleanupAdmission.WaitingRecheckingExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingRecheckingExamples.resumption_rechecked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingRecheckingExamples.not_neutral
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingRecheckingExamples.restored_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingRecheckingExamples.masking_finite_checks
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingRecheckingExamples.masking_context_rejected

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingRecheckingExamples.Repeated.resumption_rechecked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.WaitingRecheckingExamples.Repeated.restored_twice
