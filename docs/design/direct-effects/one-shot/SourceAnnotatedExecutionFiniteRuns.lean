import SourceAnnotatedExecutionProgress
import SourceScheduledFiniteRuns

/-! Reuse counted machine execution and the finite-prefix induction pattern.
One annotated invariant supplies every successor; no trace supplies intermediate
validity. This constructs executions and does not quantify over arbitrary traces. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Saved)
open ClauseExecution (CountedSteps)

theorem Run.finite_prefix (fuel : Nat) {hints : Hints receiving} {forest : Forest hints}
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound) :
    ∃ after nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved,
    ∃ nextDemand nextRow count,
      count ≤ fuel ∧ CountedSteps [] count before.erase after.erase ∧
      Run operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after saved.forest output nextDemand nextRow bound ∧
      (count = fuel ∨ ScopedPortProgress.Terminal after.execution.configuration.erase) := by
  induction fuel generalizing contracts registry tables families required annotations receiving before demand row with
  | zero => exact ⟨before, contracts, registry, tables, families, required, annotations, ⟨_, _, forest⟩,
      demand, row, 0, Nat.le_refl _, .zero, run, Or.inl rfl⟩
  | succ fuel ih =>
    rcases run.progress with terminal | ⟨middle, nextContracts, nextRegistry, nextTables, nextFamilies,
      nextRequired, nextAnnotations, saved, nextDemand, nextRow, step, next⟩
    · refine ⟨before, contracts, registry, tables, families, required, annotations, ⟨_, _, forest⟩,
        demand, row, 0, Nat.zero_le _, .zero, run, Or.inr ?_⟩
      exact ⟨terminal.1, by simp only [SourceAnnotatedRuntime.Configuration.erase, terminal.2, SourceAnnotatedRuntime.Stack.erase]⟩
    · obtain ⟨after, finalContracts, finalRegistry, finalTables, finalFamilies, finalRequired, finalAnnotations,
        finalSaved, finalDemand, finalRow, count, bounded, execution, final, outcome⟩ := ih next
      refine ⟨after, finalContracts, finalRegistry, finalTables, finalFamilies, finalRequired, finalAnnotations,
        finalSaved, finalDemand, finalRow, count + 1, Nat.succ_le_succ bounded, .next step execution, final, ?_⟩
      rcases outcome with exhausted | terminal
      · exact Or.inl (congrArg Nat.succ exhausted)
      · exact Or.inr terminal

/-- The current explicit initial premises suffice for annotated finite progress.
Combining and deriving these premises is the separate admission obligation. -/
theorem initial_finite_prefix (fuel : Nat) {plan : SourceDeclarationPlans.Plan dependencies}
    (source : SourceAnnotatedSources.Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (SourcePlanSignatures.signature plan))
    (contextual : SourceScheduledChecks.Local [] (fun _ => none) (OwnerPhaseTransitions.available []) [] plan .nil)
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase bound)
    (signature : operations.erase.erase.ports = DeclarationResults.signature declarations) :
    demand = [] ∧
    ∃ after nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved,
    ∃ nextDemand nextRow count,
      count ≤ fuel ∧ CountedSteps [] count ⟨⟨⟨code.erase, .none, .nil⟩, [], []⟩, []⟩ after.erase ∧
      Run operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after saved.forest output nextDemand nextRow bound ∧
      (count = fuel ∨ ScopedPortProgress.Terminal after.execution.configuration.erase) := by
  obtain ⟨empty, initial⟩ := initial_run source contextual admitted result signature
    (tables := fun _ => []) (families := fun _ => []) (required := fun _ => [])
  exact ⟨empty, initial.finite_prefix fuel⟩

/-- The existing ledger proves that termination discharges every issued owner
exactly once, including resources, cleanups, closing scopes and continuations. -/
theorem Run.terminal_accounting
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound)
    (terminal : ScopedPortProgress.Terminal before.execution.configuration.erase) :
    before.execution.issued.Perm before.execution.completed ∧ before.execution.completed.Nodup :=
  run.erase.terminal_accounting terminal

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.finite_prefix
#print axioms Ash.OneShot.SourceAnnotatedExecution.initial_finite_prefix
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.terminal_accounting
