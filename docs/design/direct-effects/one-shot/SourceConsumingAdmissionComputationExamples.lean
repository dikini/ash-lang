import SourceConsumingAdmissionComputation
import SourceConsumingHandlerAdmissionExamples

/-! Ordinary reductions preserve a source body with explicit handler bounds,
including its nonempty saved continuation and handler-interference derivation.
Negative evidence rejects replacing the selected bounds with an absent packet. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceBoundSnapshots (Snapshot Computed)
open SourcePlanBounds (Annotation Reduced)

def bindPlan := Plan.sequence .pure HandlerExamples.clause
def bindBody : Body [] 19 bindPlan := .sequence [] .pure .pure HandlerExamples.body
def betaPlan := Plan.sequence .pure bindPlan
def betaBody : Body [] 19 betaPlan := .sequence [] .pure .pure bindBody
def branchPlan := Plan.sequence .pure (Plan.choice HandlerExamples.clause (.invoke (key := ⟨19, .dispose⟩)))
def branchBody : Body [] 19 branchPlan := .sequence [] .pure .pure (.choice HandlerExamples.body .dispose)

theorem bind_source : At (recipeLaws []) (fun evidence => evidence) bindBody HandlerExamples.context :=
  .sequence HandlerExamples.admitted
theorem beta_source : At (recipeLaws []) (fun evidence => evidence) betaBody HandlerExamples.context :=
  .sequence bind_source
theorem branch_source : At (recipeLaws []) (fun evidence => evidence) branchBody HandlerExamples.context :=
  .sequence (.choice HandlerExamples.admitted .dispose)

/-- One original source derivation exposes the same handler-bearing child at
bind and beta, without rebuilding its saved-request interception proof. -/
theorem bind_and_beta :
    At (recipeLaws []) (fun evidence => evidence) HandlerExamples.body HandlerExamples.context ∧
    HandlerExamples.body.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
      (.live 19 (.plain (.request SourceDependencyCapture.Examples.effectE 0) .nil)
        (.handler SourceDependencyCapture.Examples.effectE SourceDependencyCapture.Examples.resumeTable
          SourceDependencyCapture.Examples.resumeDependencies .nil))
      (.handler SourceDependencyCapture.Examples.effectE SourceDependencyCapture.Examples.resumeTable
        SourceDependencyCapture.Examples.resumeDependencies .nil) .nil := by
  have first := bind_source.reduce (show bindBody.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
    _ _ HandlerExamples.context.before from ⟨rfl, HandlerExamples.checked⟩) Body.Reduction.bind
  have second := beta_source.reduce (show betaBody.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
    _ _ HandlerExamples.context.before from ⟨rfl, rfl, first.2⟩) Body.Reduction.beta
  exact second

theorem both_branches :
    At (recipeLaws []) (fun evidence => evidence) HandlerExamples.body HandlerExamples.context ∧
    At (recipeLaws []) (fun evidence => evidence) (Body.dispose (world := []) (owner := 19)) HandlerExamples.context := by
  have checked : branchBody.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
      _ _ HandlerExamples.context.before := ⟨rfl, HandlerExamples.checked, rfl, rfl, rfl, rfl⟩
  exact ⟨(branch_source.reduce checked Body.Reduction.ifTrue).1,
    (branch_source.reduce checked Body.Reduction.ifFalse).1⟩

/-- The actual bound event, rather than a separate requested child, selects
the admitted source and exact pending metadata. -/
theorem bind_event (pending : SourceBoundSnapshots.Retained [] HandlerExamples.whole)
    {next : Snapshot []}
    (event : Computed .bind ⟨_, bindPlan, bindBody.boundAnnotation, _, _, HandlerExamples.whole, pending⟩ next) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBody : Body [] 19 nextPlan,
      At (recipeLaws []) (fun evidence => evidence) nextBody HandlerExamples.context ∧
      nextBody.BoundCheck [] [] HandlerExamples.actions HandlerExamples.phases
        (.live 19 (.plain (.request SourceDependencyCapture.Examples.effectE 0) .nil)
          (.handler SourceDependencyCapture.Examples.effectE SourceDependencyCapture.Examples.resumeTable
            SourceDependencyCapture.Examples.resumeDependencies .nil))
        (.handler SourceDependencyCapture.Examples.effectE SourceDependencyCapture.Examples.resumeTable
          SourceDependencyCapture.Examples.resumeDependencies .nil) HandlerExamples.context.before ∧
      bindBody.Reduction .bind nextBody ∧
      next = ⟨_, nextPlan, nextBody.boundAnnotation, _, _, HandlerExamples.whole, pending⟩ :=
  bind_source.computed ⟨rfl, HandlerExamples.checked⟩ pending event

theorem explicit_bounds_survive : Reduced [] .bind bindBody.boundAnnotation HandlerExamples.body.boundAnnotation :=
  Body.Reduction.bounds (.bind : bindBody.Reduction .bind HandlerExamples.body)

/-- A valid-looking absent packet cannot replace the explicit handler bounds
selected from this source. The existing computation relation rejects it. -/
theorem erased_bounds_rejected :
    ¬ Reduced [] .bind bindBody.boundAnnotation (Annotation.absent (plan := HandlerExamples.clause)) := by
  intro reduced
  cases reduced

/-- Disposal remains independently admitted after a branch. -/
theorem disposal_nested :
    (Body.dispose (world := []) (owner := 19)).Nested := by
  have step : (Body.sequence (before := Plan.pure) [] .pure .pure
      (Body.choice (Body.resume (world := []) (owner := 19)) Body.dispose)).Reduction .ifFalse Body.dispose := .ifFalse
  exact step.nested (.sequence (.choice .resume .dispose))

/-- Selecting a handler-bearing subtree also preserves the actual checked
clause declarations, rather than only their projected bound packet. -/
theorem handler_nested : HandlerExamples.body.Nested := by
  have original : HandlerExamples.body.Nested :=
    .handler (.cons (.available (fun _ => .dispose)) .unavailable .nil)
      (.cons (.available (.available (fun _ => .dispose rfl)) (fun _ => .dispose)) .unavailable .nil)
      (.choice .resume .dispose)
  exact (Body.Reduction.beta : betaBody.Reduction .beta HandlerExamples.body).nested
    (.sequence (.sequence original))

end Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples.bind_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples.beta_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples.branch_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples.bind_and_beta
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples.both_branches
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples.bind_event
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples.explicit_bounds_survive
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples.erased_bounds_rejected
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples.disposal_nested
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ComputationExamples.handler_nested
