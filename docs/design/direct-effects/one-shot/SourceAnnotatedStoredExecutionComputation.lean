import SourceAnnotatedStoredComputation
import SourceAnnotatedStoredExecution
import SourceAnnotatedExecutionComputation

/-! All four ordinary reductions preserve the actual joint packet/source
state. The pending stack is unchanged; source substitution, branch narrowing
and execution checks reuse the established proof engines. -/
namespace Ash.OneShot.SourceAnnotatedExecution
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution
open RecursiveExpressions (Ready ready_not_value ready_not_focus)

/-- Every supplied raw ready step has an annotated successor with the same
owner multiset and a sublist of the previous checked effect row. -/
theorem AtPackets.ready_preserves_bounds {plan : SourceDeclarationPlans.Plan dependencies}
    (bounds : SourcePlanBounds.Annotation (ScopedTyping.resourceWorld before.execution.issued) plan)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations before plan forest output demand row bound stored evidence)
    (ready : Ready before.execution.configuration.expression.erase)
    (raw : RawStep before.execution.configuration.erase rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack, ∃ nextDependencies,
    ∃ nextPlan : SourceDeclarationPlans.Plan nextDependencies,
    ∃ nextBounds : SourcePlanBounds.Annotation (ScopedTyping.resourceWorld before.execution.issued) nextPlan,
    ∃ remaining nextRow,
      after.erase = rawAfter ∧
      after.stack = before.execution.configuration.stack ∧ HEq nextStored stored ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextPlan forest output remaining nextRow bound nextStored evidence ∧
      (∃ reduction : SourceAnnotatedCode.Reduction before.execution.configuration.expression
          before.execution.configuration.scope after.expression after.scope,
        SourcePlanBounds.Reduced (ScopedTyping.resourceWorld before.execution.issued) reduction.rule bounds nextBounds) ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨code, scope, reduction, same, _, _⟩ := SourceAnnotatedCode.Reduction.of_raw raw ready
  subst rawAfter
  let after : SourceAnnotatedRuntime.Configuration := ⟨code, scope, before.execution.configuration.stack⟩
  obtain ⟨_, nextPlan, nextBounds, remaining, nextRow, next, accounting, included, selected⟩ :=
    SourceAnnotatedStoredComputation.ordinary_preserves_bounds bounds source reduction
  obtain ⟨oldRemaining, oldRow, step, current, oldAccounting, oldIncluded⟩ :=
    SourceScheduledExecution.ready_preserves run.atPlan.run.erase ready raw
  refine ⟨after, stored, _, nextPlan, nextBounds, remaining, nextRow, rfl, rfl, HEq.rfl, step, ?_, ⟨reduction, selected⟩, accounting, included⟩
  have freshOwners : (before.execution.issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  apply assemble_entry_atPackets (after := after) run.coherent run.current raw freshOwners current.current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.current.results
  · rfl
  · simp

theorem AtPackets.ready_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound stored evidence)
    (ready : Ready before.execution.configuration.expression.erase)
    (raw : RawStep before.execution.configuration.erase rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
    ∃ remaining nextRow,
      after.erase = rawAfter ∧
      after.stack = before.execution.configuration.stack ∧ HEq nextStored stored ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output remaining nextRow bound nextStored evidence ∧
      (∃ reduction : SourceAnnotatedCode.Reduction before.execution.configuration.expression
          before.execution.configuration.scope after.expression after.scope,
        SourceBoundSnapshots.Computed reduction.rule snapshot next) ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨after, nextStored, _, nextPlan, nextBounds, remaining, nextRow, same, stackSame, packetsSame, step, next, ⟨reduction, selected⟩, permutation, included⟩ :=
    AtPackets.ready_preserves_bounds snapshot.current run ready raw
  exact ⟨after, nextStored, snapshot.computed nextPlan nextBounds, remaining, nextRow, same, stackSame, packetsSame, step, next,
    ⟨reduction, .step snapshot nextBounds selected⟩, permutation, included⟩

/-- Ordinary progress supplies the raw step from the existing source proof;
no premise assumes successor admission or a successful future check. -/
theorem AtPackets.ready_progress_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound stored evidence)
    (ready : Ready before.execution.configuration.expression.erase) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
    ∃ remaining nextRow,
      after.stack = before.execution.configuration.stack ∧ HEq nextStored stored ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output remaining nextRow bound nextStored evidence ∧
      (∃ reduction : SourceAnnotatedCode.Reduction before.execution.configuration.expression
          before.execution.configuration.scope after.expression after.scope,
        SourceBoundSnapshots.Computed reduction.rule snapshot next) ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨rawAfter, _, _, raw, _⟩ := DeclaredSourceStates.ready_preserves run.current.source ready
  obtain ⟨after, nextStored, next, remaining, nextRow, _, stackSame, packetsSame, step, typed, computation, permutation, included⟩ :=
    AtPackets.ready_snapshot snapshot run ready raw
  exact ⟨after, nextStored, next, remaining, nextRow, stackSame, packetsSame, step, typed, computation, permutation, included⟩

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem AtPackets.ready_progress_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (admitted : snapshot.Admitted)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound stored evidence)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld before.execution.issued) required)
    (ready : Ready before.execution.configuration.expression.erase) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack,
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
    ∃ remaining nextRow,
      after.stack = before.execution.configuration.stack ∧ HEq nextStored stored ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output remaining nextRow bound nextStored evidence ∧
      (∃ reduction : SourceAnnotatedCode.Reduction before.execution.configuration.expression
          before.execution.configuration.scope after.expression after.scope,
        SourceBoundSnapshots.Computed reduction.rule snapshot next) ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ next.Admitted ∧
      nextStored.Admitted (ScopedTyping.resourceWorld before.execution.issued) required := by
  obtain ⟨after, nextStored, next, remaining, nextRow, stackSame, packetsSame, step, typed,
    ⟨reduction, computation⟩, permutation, included⟩ :=
    AtPackets.ready_progress_snapshot snapshot run ready
  have packetAdmission : nextStored.Admitted (ScopedTyping.resourceWorld before.execution.issued) required := by
    rcases after with ⟨expression, scope, stack⟩
    dsimp only at stackSame packetsSame ⊢
    cases stackSame
    cases eq_of_heq packetsSame
    exact storedAdmitted
  exact ⟨after, nextStored, next, remaining, nextRow, stackSame, packetsSame, step, typed,
    ⟨reduction, computation⟩, permutation, included, computation.admitted admitted, packetAdmission⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.ready_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.ready_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.ready_progress_snapshot

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.ready_progress_snapshot_admitted
