import SourceAnnotatedStoredEvents
import SourceAnnotatedEventProgress

/-! Finite operational traces retain actual packet/source pairing. These
results use the current recipe declaration policy and do not establish the
separate bounded-annotation or complete initial-source admission obligations. -/
namespace Ash.OneShot.SourceAnnotatedStoredEvents
open SourceAnnotatedExecution (AtPackets)
open SourceScheduledSavedPlans (Saved)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceConsumingStoredBounds (StackBounds)

theorem steps_preserve {output : SourcePlannedTyping.Value}
    {families : SourceDependencyFrames.Families}
    {stored : StackBounds families before.execution.configuration.stack}
    {plan : SourceDeclarationPlans.Plan dependencies}
    {hints : Hints receiving} {forest : Forest hints}
    (trace : SourceAnnotatedExecutionEvents.Steps operations.erase.erase.ports output.erase.erase.port count before after)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before plan forest output demand row bound stored) :
    ClauseExecution.CountedSteps [] count before.erase after.erase ∧
    ∃ nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved,
    ∃ nextDependencies, ∃ nextPlan : SourceDeclarationPlans.Plan nextDependencies,
    ∃ nextStored : StackBounds nextFamilies after.execution.configuration.stack, ∃ nextDemand nextRow,
      AtPackets operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after nextPlan saved.forest output nextDemand nextRow bound nextStored ∧ nextRow ⊆ row := by
  induction trace generalizing contracts registry tables families required annotations receiving demand row dependencies with
  | zero => exact ⟨.zero, _, _, _, _, _, _, ⟨_, _, forest⟩, _, plan, stored, _, _, run, List.Subset.refl _⟩
  | next event trace ih =>
      obtain ⟨step, nextContracts, nextRegistry, nextTables, nextFamilies, nextRequired, nextAnnotations,
        saved, nextDependencies, nextPlan, nextStored, nextDemand, nextRow, next, included⟩ := step_preserves event run
      obtain ⟨execution, finalContracts, finalRegistry, finalTables, finalFamilies, finalRequired, finalAnnotations, finalSaved, finalDependencies, finalPlan, finalStored, finalDemand, finalRow, final, remaining⟩ := ih next
      exact ⟨.next step execution, finalContracts, finalRegistry, finalTables, finalFamilies, finalRequired, finalAnnotations, finalSaved, finalDependencies, finalPlan, finalStored, finalDemand, finalRow,
        final, List.Subset.trans remaining included⟩

/-- Exact-once terminal ownership follows from the original ledger theorem
at the derived joint endpoint of any supplied finite event trace. -/
theorem terminal_accounting {output : SourcePlannedTyping.Value}
    {families : SourceDependencyFrames.Families}
    {stored : StackBounds families before.execution.configuration.stack}
    {plan : SourceDeclarationPlans.Plan dependencies}
    {hints : Hints receiving} {forest : Forest hints}
    (trace : SourceAnnotatedExecutionEvents.Steps operations.erase.erase.ports output.erase.erase.port count before after)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before plan forest output demand row bound stored)
    (terminal : ScopedPortProgress.Terminal after.execution.configuration.erase) :
    after.execution.issued.Perm after.execution.completed ∧ after.execution.completed.Nodup := by
  obtain ⟨_, _, _, _, _, _, _, saved, nextDependencies, nextPlan, nextStored, nextDemand, nextRow, next, _⟩ :=
    steps_preserve trace run
  exact next.atPlan.run.terminal_accounting terminal

/-- Existing event selection is valid for the stronger initial source as well. -/
theorem progress {output : SourcePlannedTyping.Value}
    {families : SourceDependencyFrames.Families}
    {stored : StackBounds families before.execution.configuration.stack}
    {plan : SourceDeclarationPlans.Plan dependencies}
    {hints : Hints receiving} {forest : Forest hints}
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before plan forest output demand row bound stored) :
    (before.execution.configuration.expression.erase.IsValue ∧ before.execution.configuration.stack = .nil) ∨
    ∃ after, SourceAnnotatedExecutionEvents.Step operations.erase.erase.ports output.erase.erase.port before after :=
  SourceAnnotatedExecutionEvents.progress run.atPlan.run

/-- Every reachable endpoint is terminal or has another event; preservation
of that event is supplied by step_preserves. -/
theorem finite_progress {output : SourcePlannedTyping.Value}
    {families : SourceDependencyFrames.Families}
    {stored : StackBounds families before.execution.configuration.stack}
    {plan : SourceDeclarationPlans.Plan dependencies}
    {hints : Hints receiving} {forest : Forest hints}
    (trace : SourceAnnotatedExecutionEvents.Steps operations.erase.erase.ports output.erase.erase.port count before after)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before plan forest output demand row bound stored) :
    (after.execution.configuration.expression.erase.IsValue ∧ after.execution.configuration.stack = .nil) ∨
    ∃ next, SourceAnnotatedExecutionEvents.Step operations.erase.erase.ports output.erase.erase.port after next := by
  obtain ⟨_, _, _, _, _, _, _, saved, nextDependencies, nextPlan, nextStored, nextDemand, nextRow, next, _⟩ :=
    steps_preserve trace run
  exact progress next

/-- For every fuel bound, event selection and joint preservation construct an
actual prefix that either uses all fuel or reaches a terminal configuration. -/
theorem finite_prefix (fuel : Nat) {output : SourcePlannedTyping.Value}
    {families : SourceDependencyFrames.Families}
    {stored : StackBounds families before.execution.configuration.stack}
    {plan : SourceDeclarationPlans.Plan dependencies}
    {hints : Hints receiving} {forest : Forest hints}
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      before plan forest output demand row bound stored) :
    ∃ after nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved,
    ∃ nextDependencies, ∃ nextPlan : SourceDeclarationPlans.Plan nextDependencies,
    ∃ nextStored : StackBounds nextFamilies after.execution.configuration.stack, ∃ nextDemand nextRow count,
      count ≤ fuel ∧ SourceAnnotatedExecutionEvents.Steps operations.erase.erase.ports output.erase.erase.port count before after ∧
      AtPackets operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after nextPlan saved.forest output nextDemand nextRow bound nextStored ∧ nextRow ⊆ row ∧
      (count = fuel ∨ (after.execution.configuration.expression.erase.IsValue ∧ after.execution.configuration.stack = .nil)) := by
  induction fuel generalizing contracts registry tables families required annotations receiving before demand row dependencies with
  | zero =>
      exact ⟨before, _, _, _, _, _, _, ⟨_, _, forest⟩, _, plan, stored, demand, row, 0,
        Nat.le_refl _, .zero, run, List.Subset.refl _, Or.inl rfl⟩
  | succ fuel ih =>
      rcases progress run with terminal | ⟨middle, event⟩
      · exact ⟨before, _, _, _, _, _, _, ⟨_, _, forest⟩, _, plan, stored, demand, row, 0,
          Nat.zero_le _, .zero, run, List.Subset.refl _, Or.inr terminal⟩
      · obtain ⟨step, nextContracts, nextRegistry, nextTables, nextFamilies, nextRequired, nextAnnotations,
          saved, nextDependencies, nextPlan, nextStored, nextDemand, nextRow, next, included⟩ := step_preserves event run
        obtain ⟨after, finalContracts, finalRegistry, finalTables, finalFamilies, finalRequired, finalAnnotations,
          finalSaved, finalDependencies, finalPlan, finalStored, finalDemand, finalRow, count, bounded, trace, final, remaining, outcome⟩ := ih next
        refine ⟨after, finalContracts, finalRegistry, finalTables, finalFamilies, finalRequired, finalAnnotations,
          finalSaved, finalDependencies, finalPlan, finalStored, finalDemand, finalRow, count + 1,
          Nat.succ_le_succ bounded, .next event trace, final, List.Subset.trans remaining included, ?_⟩
        rcases outcome with exhausted | terminal
        · exact Or.inl (congrArg Nat.succ exhausted)
        · exact Or.inr terminal

end Ash.OneShot.SourceAnnotatedStoredEvents

#print axioms Ash.OneShot.SourceAnnotatedStoredEvents.steps_preserve
#print axioms Ash.OneShot.SourceAnnotatedStoredEvents.terminal_accounting
#print axioms Ash.OneShot.SourceAnnotatedStoredEvents.progress
#print axioms Ash.OneShot.SourceAnnotatedStoredEvents.finite_progress

#print axioms Ash.OneShot.SourceAnnotatedStoredEvents.finite_prefix
