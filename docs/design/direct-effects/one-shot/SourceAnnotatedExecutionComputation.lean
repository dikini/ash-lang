import SourceAnnotatedExecutionStable
import SourceAnnotatedRuntimeComputation

/-! Ready ordinary steps recover the actual annotated body or branch. Runtime
preservation reuses the existing completion and source reduction proofs. -/
namespace Ash.OneShot.SourceAnnotatedCode
open ScopedExpressions ScopedExecution
open RecursiveExpressions (Ready ready_not_value ready_not_focus)

/-- Raw ready reduction cannot select different source annotations: it keeps
the actual body or branch and performs the same substitution. -/
theorem Reduction.of_raw
    (raw : RawStep ⟨before.erase, scope, stack⟩ rawAfter created discharged)
    (ready : Ready before.erase) :
    ∃ after nextScope, Reduction before scope after nextScope ∧
      rawAfter = ⟨after.erase, nextScope, stack⟩ ∧ created = [] ∧ discharged = [] := by
  generalize same : (Configuration.mk before.erase scope stack) = rawBefore at raw
  have rawReady : Ready rawBefore.expression := by rw [← same]; exact ready
  cases raw with
  | focus plain focus tail => exact False.elim (ready_not_focus rawReady focus)
  | plug plain value closed scope tail => exact False.elim (ready_not_value rawReady closed.1)
  | leaveHandler handler value closed scope tail => exact False.elim (ready_not_value rawReady closed.1)
  | leaveCell identity payload answer savedScope scope value closed tail => exact False.elim (ready_not_value rawReady closed.1)
  | startCleanup action saved closed scope tail => exact False.elim (ready_not_value rawReady closed.1)
  | leaveClause ticket answer value closed scope caller tail => exact False.elim (ready_not_value rawReady closed.1)
  | enterHandler | enterCell | enterCleanup | finishCleanup | capture | resume | discard | finishClose | retire | readCell | writeCell => cases rawReady
  | bind parameter value body rawScope tail closed environmentReady =>
      cases before <;> simp [Term.erase, Configuration.mk.injEq] at same
      rcases same with ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨_, _, .bind closed environmentReady, by simp only [Term.erase_subst], rfl, rfl⟩
  | beta parameter body value rawScope tail closed closureReady =>
      cases before <;> simp [Term.erase, Configuration.mk.injEq] at same
      rename_i hint function argument
      cases function <;> simp [Term.erase] at same
      rcases same with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl, rfl⟩
      exact ⟨_, _, .beta closed closureReady, by simp only [Term.erase_subst], rfl, rfl⟩
  | ifTrue yes no rawScope tail =>
      cases before <;> simp [Term.erase, Configuration.mk.injEq] at same
      rename_i hint condition yesSource noSource
      cases condition <;> simp [Term.erase] at same
      rcases same with ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨_, _, .ifTrue, rfl, rfl, rfl⟩
  | ifFalse yes no rawScope tail =>
      cases before <;> simp [Term.erase, Configuration.mk.injEq] at same
      rename_i hint condition yesSource noSource
      cases condition <;> simp [Term.erase] at same
      rcases same with ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨_, _, .ifFalse, rfl, rfl, rfl⟩

end Ash.OneShot.SourceAnnotatedCode

namespace Ash.OneShot.SourceAnnotatedExecution
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution
open RecursiveExpressions (Ready ready_not_value ready_not_focus)

/-- Every supplied raw ready step has an annotated successor with the same
owner multiset and a sublist of the previous checked effect row. -/
theorem AtPlan.ready_preserves_bounds {plan : SourceDeclarationPlans.Plan dependencies}
    (bounds : SourcePlanBounds.Annotation (ScopedTyping.resourceWorld before.execution.issued) plan)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations before plan forest output demand row bound evidence)
    (ready : Ready before.execution.configuration.expression.erase)
    (raw : RawStep before.execution.configuration.erase rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ nextDependencies,
    ∃ nextPlan : SourceDeclarationPlans.Plan nextDependencies,
    ∃ nextBounds : SourcePlanBounds.Annotation (ScopedTyping.resourceWorld before.execution.issued) nextPlan,
    ∃ remaining nextRow,
      after.erase = rawAfter ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextPlan forest output remaining nextRow bound evidence ∧
      (∃ reduction : SourceAnnotatedCode.Reduction before.execution.configuration.expression
          before.execution.configuration.scope after.expression after.scope,
        SourcePlanBounds.Reduced (ScopedTyping.resourceWorld before.execution.issued) reduction.rule bounds nextBounds) ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨code, scope, reduction, same, _, _⟩ := SourceAnnotatedCode.Reduction.of_raw raw ready
  subst rawAfter
  let after : SourceAnnotatedRuntime.Configuration := ⟨code, scope, before.execution.configuration.stack⟩
  obtain ⟨_, nextPlan, nextBounds, remaining, nextRow, next, accounting, included, selected⟩ :=
    SourceAnnotatedRuntimeComputation.ordinary_preserves_bounds bounds source reduction
  obtain ⟨oldRemaining, oldRow, step, current, oldAccounting, oldIncluded⟩ :=
    SourceScheduledExecution.ready_preserves run.run.erase ready raw
  refine ⟨after, _, nextPlan, nextBounds, remaining, nextRow, rfl, step, ?_, ⟨reduction, selected⟩, accounting, included⟩
  have freshOwners : (before.execution.issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  apply assemble_entry_atPlan (after := after) run.coherent run.current raw freshOwners current.current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.current.results
  · rfl
  · simp

theorem Run.ready_preserves
    (run : Run operations declarations policy contracts registry tables families required annotations before forest output demand row bound evidence)
    (ready : Ready before.execution.configuration.expression.erase)
    (raw : RawStep before.execution.configuration.erase rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ remaining nextRow,
      after.erase = rawAfter ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) forest output remaining nextRow bound evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  cases source with
  | checked current scope pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      have indexed : AtPlan operations declarations policy contracts registry tables families required annotations
          before rootPlan forest output demand row bound evidence :=
        ⟨run.coherent, run.current, run.annotationHistory, actions, usage, history,
          .checked current scope pending closing templates matched contextual unique evaluated accepted accounting, retained⟩
      obtain ⟨after, _, _, _, remaining, nextRow, same, step, next, _, permutation, included⟩ :=
        AtPlan.ready_preserves_bounds .absent indexed ready raw
      exact ⟨after, remaining, nextRow, same, step, next.run, permutation, included⟩

/-- Existing source progress chooses the raw ordinary step; preservation
constructs its annotated successor without any future-validity premise. -/
theorem Run.ready_progress
    (run : Run operations declarations policy contracts registry tables families required annotations before forest output demand row bound evidence)
    (ready : Ready before.execution.configuration.expression.erase) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ remaining nextRow,
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) forest output remaining nextRow bound evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨rawAfter, _, _, raw, _⟩ := DeclaredSourceStates.ready_preserves run.current.source ready
  obtain ⟨after, remaining, nextRow, same, step, next, accounting, included⟩ := run.ready_preserves ready raw
  exact ⟨after, remaining, nextRow, step, next, accounting, included⟩

/-- Lift exact snapshot transport to the combined execution invariant. The
successor retains the same owner registry, name and completion guarantees. -/
theorem AtPlan.ready_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound evidence)
    (ready : Ready before.execution.configuration.expression.erase)
    (raw : RawStep before.execution.configuration.erase rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
    ∃ remaining nextRow,
      after.erase = rawAfter ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output remaining nextRow bound evidence ∧
      (∃ reduction : SourceAnnotatedCode.Reduction before.execution.configuration.expression
          before.execution.configuration.scope after.expression after.scope,
        SourceBoundSnapshots.Computed reduction.rule snapshot next) ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨after, _, nextPlan, nextBounds, remaining, nextRow, same, step, next, ⟨reduction, selected⟩, permutation, included⟩ :=
    AtPlan.ready_preserves_bounds snapshot.current run ready raw
  exact ⟨after, snapshot.computed nextPlan nextBounds, remaining, nextRow, same, step, next,
    ⟨reduction, .step snapshot nextBounds selected⟩, permutation, included⟩

/-- Ordinary progress supplies the raw step from the existing source proof;
no premise assumes successor admission or a successful future check. -/
theorem AtPlan.ready_progress_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound evidence)
    (ready : Ready before.execution.configuration.expression.erase) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
    ∃ remaining nextRow,
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output remaining nextRow bound evidence ∧
      (∃ reduction : SourceAnnotatedCode.Reduction before.execution.configuration.expression
          before.execution.configuration.scope after.expression after.scope,
        SourceBoundSnapshots.Computed reduction.rule snapshot next) ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨rawAfter, _, _, raw, _⟩ := DeclaredSourceStates.ready_preserves run.current.source ready
  obtain ⟨after, next, remaining, nextRow, _, step, typed, computation, permutation, included⟩ :=
    AtPlan.ready_snapshot snapshot run ready raw
  exact ⟨after, next, remaining, nextRow, step, typed, computation, permutation, included⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedCode.Reduction.of_raw
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.ready_preserves
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.ready_progress

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.ready_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.ready_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.ready_progress_snapshot
