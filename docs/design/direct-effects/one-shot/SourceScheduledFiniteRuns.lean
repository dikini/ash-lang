import SourceScheduledProgress
import ClauseExecution

/-! Reuse the existing counted machine steps and finite-prefix induction.
From one retained invariant, construct any requested finite prefix unless an
ordinary terminal is reached first. This is an existence theorem, not
preservation for an arbitrary trace of unchecked machine annotations. -/
namespace Ash.OneShot.SourceScheduledExecution
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Saved)
open ClauseExecution (CountedSteps)

theorem Run.finite_prefix (fuel : Nat) {hints : Hints receiving} {forest : Forest hints}
    (before : Run operations declarations policy contracts registry tables families required annotations
      state forest output demand row bound) :
    ∃ after nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved,
    ∃ nextDemand nextRow count,
      count ≤ fuel ∧ CountedSteps [] count state after ∧
      Run operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after saved.forest output nextDemand nextRow bound ∧
      (count = fuel ∨ ScopedPortProgress.Terminal after.execution.configuration) := by
  induction fuel generalizing contracts registry tables families required annotations receiving state demand row with
  | zero => exact ⟨state, contracts, registry, tables, families, required, annotations, ⟨_, _, forest⟩,
      demand, row, 0, Nat.le_refl _, .zero, before, Or.inl rfl⟩
  | succ fuel ih =>
    rcases before.progress with terminal | ⟨middle, nextContracts, nextRegistry, nextTables, nextFamilies,
      nextRequired, nextAnnotations, saved, nextDemand, nextRow, step, next⟩
    · exact ⟨state, contracts, registry, tables, families, required, annotations, ⟨_, _, forest⟩,
        demand, row, 0, Nat.zero_le _, .zero, before, Or.inr terminal⟩
    · obtain ⟨after, finalContracts, finalRegistry, finalTables, finalFamilies, finalRequired, finalAnnotations,
        finalSaved, finalDemand, finalRow, count, bounded, execution, final, outcome⟩ := ih next
      refine ⟨after, finalContracts, finalRegistry, finalTables, finalFamilies, finalRequired, finalAnnotations,
        finalSaved, finalDemand, finalRow, count + 1, Nat.succ_le_succ bounded, .next step execution, final, ?_⟩
      rcases outcome with exhausted | terminal
      · exact Or.inl (congrArg Nat.succ exhausted)
      · exact Or.inr terminal


/-- The existing initial construction supplies the single invariant needed by
finite progress. Its premises list the current structural admission boundary. -/
theorem initial_finite_prefix (fuel : Nat) {plan : SourceDeclarationPlans.Plan dependencies}
    (source : SourcePlannedSources.Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (SourcePlanSignatures.signature plan))
    (contextual : SourceScheduledChecks.Local [] (fun _ => none) (OwnerPhaseTransitions.available []) [] plan .nil)
    (admitted : checkInitial code requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code bound)
    (signature : operations.erase.erase.ports = DeclarationResults.signature declarations) :
    demand = [] ∧
    ∃ after nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved,
    ∃ nextDemand nextRow count,
      count ≤ fuel ∧ CountedSteps [] count ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ after ∧
      Run operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after saved.forest output nextDemand nextRow bound ∧
      (count = fuel ∨ ScopedPortProgress.Terminal after.execution.configuration) := by
  obtain ⟨empty, initial⟩ := initial_run source contextual admitted result signature
    (tables := fun _ => []) (families := fun _ => []) (required := fun _ => [])
  exact ⟨empty, initial.finite_prefix fuel⟩

/-- Terminal accounting is the existing owner ledger with an empty control
forest: every issued owner is discharged, and none is discharged twice. -/
theorem Run.terminal_accounting
    (run : Run operations declarations policy contracts registry tables families required annotations
      state forest output demand row bound)
    (terminal : ScopedPortProgress.Terminal state.execution.configuration) :
    state.execution.issued.Perm state.execution.completed ∧ state.execution.completed.Nodup := by
  have ledger := run.current.ledger
  have completed := ledger_no_double_completion ledger
  obtain ⟨⟨⟨value, scope, stack⟩, issued, done⟩, activations⟩ := state
  obtain ⟨isValue, rfl⟩ := terminal
  exact ⟨by simpa [RunState.erase, Stack.erase, Control.owners] using ledger.1, completed⟩

namespace InitialAdmissionExamples
open ProtectionContracts

/-- Test operations agree with the declared builtin signatures. -/
def operations : SourcePlannedTyping.Operations
  | .cell identity, 0 => some (.reference identity, .integer)
  | .cell identity, 1 => some (.pair (.reference identity) .integer, .unit)
  | _, _ => none

theorem signature_agreement : operations.erase.erase.ports = DeclarationResults.signature (fun _ => none) := by
  funext effect operation
  cases effect with
  | cell identity => cases operation with
    | zero => rfl
    | succ operation => cases operation <;> rfl
  | user family arguments => rfl

/-- The new initial theorem constructs the complete retained state from the
computed admission result; no row/evaluation/support proofs are supplied. -/
theorem unit_initial :
    Run operations (fun _ => none) policy (fun _ => none) (fun _ => none)
      tables families required (fun _ => none) ⟨⟨⟨.unit, .none, .nil⟩, [], []⟩, []⟩
      .nil .unit [] [] (.storage []) :=
  (initial_run (plan := .pure) .unit .pure
    (by simp [checkInitial, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel,
      OwnerSource.exportAt, OwnerPhaseTransitions.project, ProtectionResiduals.residualize, checkFootprint, Code.dependencies, Syntax.resourceDependencies])
    (.leaf trivial rfl .nil) signature_agreement).2

/-- The evaluator rejects an invocation that has no initial saved template. -/
theorem missing_continuation_rejected :
    checkInitial .unit (.invoke ⟨19, .resume⟩ [] []) = false := by
  simp [checkInitial, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel, RecursiveRequirements.lookup]

/-- An outward operation cannot be admitted without an interpretation. -/
theorem unhandled_request_rejected :
    checkInitial (.perform (Instantiation.freezeEffect (.user 92 [])) 0 .unit)
      (.request [] [⟨.user 92 [], 0, false⟩]) = false := by
  simp [checkInitial, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel,
    OwnerSource.exportAt, OwnerPhaseTransitions.project, ProtectionResiduals.residualize, checkFootprint, checkRequest]

def unsupportedEffect : Instance := .user 91 [.resource 7]
def unsupportedCode : Code := .handle (Instantiation.freezeEffect unsupportedEffect) .unit .nil
def unsupportedPlan : SourceDeclarationPlans.Plan (.handler unsupportedEffect [] [] .pure) :=
  .handler [] .nil .pure
def unsupportedRequirements : RecursiveRequirements.Requirements [] :=
  (RecursiveRequirements.Requirements.request [] []).prepend [.ordinary (.handler unsupportedEffect 0 [])]

/-- Current expression typing can admit a handler identity containing an
unissued resource, even with no operations or literal resource-reference code. -/
theorem unsupported_source :
    SourcePlannedSources.Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      unsupportedCode .unit [] unsupportedRequirements (SourcePlanSignatures.signature unsupportedPlan) := by
  apply SourcePlannedSources.Expression.handler (residual := []) .unit .nil .nil
  · intro operation input output known
    cases known
  · exact List.nodup_nil
  · exact List.nil_subset _
  · exact .nil
  · exact .nil

/-- Local scheduling, empty row evaluation and completion typing also pass.
This isolates the resource-support check retained by executable admission. -/
theorem unsupported_other_checks :
    SourceScheduledChecks.Local [] (fun _ => none) (OwnerPhaseTransitions.available []) [] unsupportedPlan .nil ∧
    RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) unsupportedRequirements [] ∧
    CompletionContracts.Derives (fun _ => none) CallableContracts.Environment.empty [] .none unsupportedCode (.storage []) := by
  refine ⟨.handler .nil .nil rfl .pure, .request rfl, ?_⟩
  exact .handle (.leaf trivial rfl .nil) .nil rfl

theorem unsupported_identity_rejected :
    Syntax.resourceDependencies unsupportedCode.dependencies = [7] ∧
    checkInitial unsupportedCode unsupportedRequirements = false := by
  constructor
  · decide
  · have unsupported : Syntax.resourceDependencies unsupportedCode.dependencies ≠ [] := by decide
    cases checked : checkInitial unsupportedCode unsupportedRequirements with
    | false => rfl
    | true => exact False.elim (unsupported (checkInitial_iff.mp checked).2)


end InitialAdmissionExamples

end Ash.OneShot.SourceScheduledExecution

#print axioms Ash.OneShot.SourceScheduledExecution.Run.finite_prefix
#print axioms Ash.OneShot.SourceScheduledExecution.Run.terminal_accounting

#print axioms Ash.OneShot.SourceScheduledExecution.initial_finite_prefix

#print axioms Ash.OneShot.SourceScheduledExecution.InitialAdmissionExamples.signature_agreement
#print axioms Ash.OneShot.SourceScheduledExecution.InitialAdmissionExamples.unit_initial
#print axioms Ash.OneShot.SourceScheduledExecution.InitialAdmissionExamples.missing_continuation_rejected
#print axioms Ash.OneShot.SourceScheduledExecution.InitialAdmissionExamples.unhandled_request_rejected
#print axioms Ash.OneShot.SourceScheduledExecution.InitialAdmissionExamples.unsupported_source
#print axioms Ash.OneShot.SourceScheduledExecution.InitialAdmissionExamples.unsupported_other_checks
#print axioms Ash.OneShot.SourceScheduledExecution.InitialAdmissionExamples.unsupported_identity_rejected
