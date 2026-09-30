import SourceConsumingAdmissionEntries
import SourceConsumingBoundTransport
import SourceConsumingHandlerAdmissionExamples
import SourceConsumingStructuralCleanupExamples

/-! Reuse established source examples to descend through composed constructors.
The proofs obtain child admission from the parent; they do not reconstruct
child At derivations or supply future annotation validity. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.DescentExamples
open SourceScheduledCapabilityAnnotations (recipeLaws)
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body)
open SourceRetainedPlans (Forest)
open SourceDependencyCapture.Examples (effectE disposeTable disposeDependencies)
open SourceBoundSnapshots (Snapshot EnteredHandler EnteredCleanup EnteredResource)

/-- Descent composes through two ordered handlers, cleanup, a fresh resource,
and then the syntactic sequence and choice. Both branches remain schedulable
for every fresh resource and every valid initial annotation witness. This does
not claim that execution of the sequence prefix preserves admission. -/
theorem nested_branches
    (other : Context [4] 19 [] Examples.actions Examples.phases Examples.whole .nil .nil Examples.waiting)
    (identity : Nat) (fresh : identity ∉ [4]) :
    let forest := Forest.cell (identity := identity)
      (.cleanup (needs := [.cell 4]) (.request (effect := .cell 4) (operation := 0))
        (.handler (effect := .user 99 []) (table := disposeTable) (families := disposeDependencies) (required := [])
          (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) Examples.whole)))
    SourceScheduledChecks.Local [] Examples.actions Examples.phases ([4] ++ [identity])
      (.invoke (key := ⟨19, .resume⟩)) forest ∧
    SourceScheduledChecks.Local [] Examples.actions Examples.phases ([4] ++ [identity])
      (.invoke (key := ⟨19, .dispose⟩)) forest := by
  have parent := At.sameReceiver (Context.before_nil other).symm (Examples.every_annotation_bounds other) HandlerExamples.wrapped_admitted
  have checked : HandlerExamples.wrappedBody.BoundCheck [] [] Examples.actions Examples.phases
      (.live 19 .nil (.cell 4 .nil)) (.cell 4 .nil) other.before := by
    rw [Context.before_nil]
    exact HandlerExamples.wrapped_source.at_capture rfl rfl rfl
  obtain ⟨outer, _, outerSource, outerChecked⟩ := parent.handler_body checked
  obtain ⟨inner, _, innerSource, innerChecked⟩ := outerSource.handler_body outerChecked
  obtain ⟨cleanup, _, cleanupSource, cleanupChecked⟩ := innerSource.cleanup_body innerChecked
  obtain ⟨resource, _, resourceSource, resourceChecked⟩ := cleanupSource.resource_body cleanupChecked fresh
  have branches := resourceSource.sequence_rest.choice_branches
  exact ⟨branches.1.scheduled resourceChecked.2.1, branches.2.scheduled resourceChecked.2.2⟩

/-- The direct structural cleanup route also descends through arbitrary
annotation changes, with the original nonempty saved outside-owner call. -/
theorem nonempty_cleanup
    (other : Context [4] 19 [] StructuralExamples.actions StructuralExamples.phases
      StructuralExamples.whole .nil StructuralExamples.saved StructuralExamples.waiting) :
    SourceScheduledChecks.Local [] StructuralExamples.actions StructuralExamples.phases [4]
      (.invoke (key := ⟨19, .resume⟩))
      (.cleanup (needs := [.cell 4]) StructuralExamples.callback StructuralExamples.whole) := by
  have parent := StructuralExamples.at_every_annotation other
  have checked : StructuralExamples.body.BoundCheck [] [] StructuralExamples.actions StructuralExamples.phases
      (.live 19 (.plain (.invoke ⟨37, .resume⟩) .nil) (.live 37 .nil (.cell 4 .nil)))
      (.live 37 .nil (.cell 4 .nil)) other.before := by
    simpa only [Context.before_nil] using StructuralExamples.checked
  obtain ⟨child, _, source, ready⟩ := parent.cleanup_body checked
  exact source.scheduled ready

/-- Existing runtime entry evidence identifies the same child bounds. It is
not enough to substitute another annotation merely sharing the body's plan. -/
theorem handler_event
    (pending : SourceBoundSnapshots.Retained [] HandlerExamples.whole)
    {next : Snapshot []}
    (entered : EnteredHandler effectE disposeTable [] HandlerExamples.plans
      ⟨_, _, HandlerExamples.body.boundAnnotation, _, _, HandlerExamples.whole, pending⟩ next) :
    next = ⟨_, _, (Body.choice (Body.resume (world := []) (owner := 19)) Body.dispose).boundAnnotation,
      _, _, .handler (effect := effectE) (table := disposeTable) (families := disposeDependencies)
        (required := []) HandlerExamples.whole, .handler pending⟩ ∧
    SourceScheduledChecks.Local [] HandlerExamples.actions HandlerExamples.phases []
      (.choice (.invoke (key := ⟨19, .resume⟩)) (.invoke (key := ⟨19, .dispose⟩)))
      (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies)
        (required := []) HandlerExamples.whole) := by
  obtain ⟨child, source, ready, same⟩ :=
    HandlerExamples.admitted.handler_entered HandlerExamples.checked pending entered
  exact ⟨same, source.scheduled ready⟩

/-- Finite clause bounds survive unrelated phase changes and world extension,
but the saved outside-owner invocation independently rejects a spent owner.
Thus bound transport alone cannot justify contextual source preservation. -/
theorem finite_checks_do_not_validate_saved_source :
    (StructuralExamples.body.world_weaken (show [4] ⊆ [4, 8] from by decide)).BoundCheck [] []
      StructuralExamples.actions (OwnerPhaseTransitions.spend StructuralExamples.phases 37)
      (.live 19 (.plain (.invoke ⟨37, .resume⟩) .nil) (.live 37 .nil (.cell 4 .nil)))
      (.live 37 .nil (.cell 4 .nil)) .nil ∧
    ¬ StructuralExamples.resumedCode.Valid [] StructuralExamples.actions
      (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.spend StructuralExamples.phases 19) 37) := by
  refine ⟨?_, StructuralExamples.spent_outside_owner_rejected⟩
  have moved := StructuralExamples.body.boundCheck_owner_transport StructuralExamples.checked
    (nextActions := StructuralExamples.actions) rfl
    (nextPhases := OwnerPhaseTransitions.spend StructuralExamples.phases 37) (fun _ => rfl)
  exact StructuralExamples.body.boundCheck_world_weaken (by decide) moved

end Ash.OneShot.SourceConsumingCleanupAdmission.DescentExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.DescentExamples.nested_branches
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.DescentExamples.nonempty_cleanup
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.DescentExamples.handler_event

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.DescentExamples.finite_checks_do_not_validate_saved_source
