import SourceAnnotatedStoredExecution
import SourceAnnotatedStoredReturnSteps
import SourceAnnotatedBoundAdmission

/-! Value-return progress and preservation retain source and packet evidence
at the same actual successor while reusing runtime ownership and completion. -/
namespace Ash.OneShot.SourceAnnotatedExecution

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution
open RecursiveCompletion (retiredTickets)

theorem AtPackets.value_step_preserves_snapshot
    {before : SourceAnnotatedRuntime.NamedState}
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families before.execution.configuration.stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations before snapshot.plan snapshot.forest output demand row bound stored evidence)
    (isValue : before.execution.configuration.expression.erase.IsValue)
    (raw : RawStep before.execution.configuration.erase rawAfter created discharged) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack, ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
      after.erase = rawAfter ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after created discharged).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after created discharged) nextSnapshot.plan nextSnapshot.forest output remaining row bound nextStored evidence ∧
      demand = retiredTickets discharged ++ remaining ∧ created = [] ∧
      (∃ lifted : SourceAnnotatedRuntime.ReturnStep before.execution.configuration after created discharged,
        SourceAnnotatedRuntime.ReturnBounds lifted snapshot nextSnapshot ∧
        SourceAnnotatedRuntime.ReturnPackets lifted stored nextStored) := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨after, nextStored, remaining, nextSnapshot, same, next, accounting, noCreated, trace, moved⟩ :=
    SourceAnnotatedStoredReturns.raw_return_preserves_snapshot snapshot source raw isValue
  subst rawAfter
  subst created
  obtain ⟨runtimeRemaining, step, current, runtimeAccounting, empty⟩ :=
    DeclaredExecution.value_step_preserves run.current isValue raw
  have freshOwners : (before.execution.issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  refine ⟨after, nextStored, remaining, nextSnapshot, rfl, step, ?_, accounting, rfl, moved⟩
  apply assemble_entry_atPackets run.coherent run.current raw freshOwners current.names.unique step.checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp
theorem AtPackets.value_progress_snapshot
    {before : SourceAnnotatedRuntime.NamedState}
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families before.execution.configuration.stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound stored evidence)
    (isValue : before.execution.configuration.expression.erase.IsValue) :
    before.execution.configuration.stack = .nil ∨
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack, ∃ discharged remaining,
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] discharged).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] discharged) nextSnapshot.plan nextSnapshot.forest output remaining row bound nextStored evidence ∧
      demand = retiredTickets discharged ++ remaining ∧
      (∃ lifted : SourceAnnotatedRuntime.ReturnStep before.execution.configuration after [] discharged,
        SourceAnnotatedRuntime.ReturnBounds lifted snapshot nextSnapshot ∧
        SourceAnnotatedRuntime.ReturnPackets lifted stored nextStored) := by
  rcases DeclaredSourceStates.value_progress run.current.source isValue with terminal | ⟨rawAfter, discharged, raw⟩
  · left
    change before.execution.configuration.stack.erase = .nil at terminal
    cases stackSame : before.execution.configuration.stack <;>
      simp_all only [SourceAnnotatedRuntime.Stack.erase, reduceCtorEq]
  · obtain ⟨after, nextStored, remaining, nextSnapshot, _, step, next, accounting, _, moved⟩ :=
      AtPackets.value_step_preserves_snapshot snapshot run isValue raw
    exact Or.inr ⟨after, nextStored, discharged, remaining, nextSnapshot, step, next, accounting, moved⟩


variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem AtPackets.value_progress_snapshot_admitted
    {before : SourceAnnotatedRuntime.NamedState}
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families before.execution.configuration.stack}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (admitted : snapshot.Admitted)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound stored evidence)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld before.execution.issued) required)
    (isValue : before.execution.configuration.expression.erase.IsValue) :
    before.execution.configuration.stack = .nil ∨
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families after.stack, ∃ discharged remaining,
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] discharged).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] discharged) nextSnapshot.plan nextSnapshot.forest output remaining row bound nextStored evidence ∧
      demand = retiredTickets discharged ++ remaining ∧
      (∃ lifted : SourceAnnotatedRuntime.ReturnStep before.execution.configuration after [] discharged,
        SourceAnnotatedRuntime.ReturnBounds lifted snapshot nextSnapshot ∧
        SourceAnnotatedRuntime.ReturnPackets lifted stored nextStored) ∧
      nextSnapshot.Admitted ∧ nextStored.Admitted (ScopedTyping.resourceWorld before.execution.issued) required := by
  rcases AtPackets.value_progress_snapshot snapshot run isValue with terminal | progress
  · exact Or.inl terminal
  · obtain ⟨after, nextStored, discharged, remaining, nextSnapshot, step, successor, accounting,
      ⟨lifted, moved, packets⟩⟩ := progress
    exact Or.inr ⟨after, nextStored, discharged, remaining, nextSnapshot, step, successor, accounting,
      ⟨lifted, moved, packets⟩, moved.admitted admitted, packets.admitted storedAdmitted⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.value_step_preserves_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.value_progress_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.value_progress_snapshot_admitted
