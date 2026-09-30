import DeclaredSourceSubstitution
import RecursiveExpressions

/-! Ordinary reductions retain hereditary source evidence. Substitution,
callable decomposition and requirement evaluation reuse established lemmas. -/
namespace Ash.OneShot.DeclaredSourceExpressions
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open DeclaredSources (Expression)
open DeclaredSourceValues (ValueSummary)
open DeclaredSourceSubstitution (substitution)
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (Phases spendAll)
open RecursiveExpressions (request_parts choice_parts)

theorem lambda_beta_expression
    (function : ValueSummary operations policy contracts world environment allowed
      (.lambda parameter body) (.function input output requests latent))
    (argument : ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value) (admitted : requests ⊆ allowed) :
    ∃ reduced : Requirements [],
      Expression operations policy contracts world allowed .none environment (body.subst parameter value) output [] reduced ∧
      ∀ store receiving before, evaluate store receiving before reduced =
        residualize (OwnerPhaseTransitions.project receiving before) latent := by
  obtain ⟨demand, requirements, source, outward⟩ := DeclaredSourceSubstitution.beta_body
    (DeclaredSourceValues.expression function .none) argument closed admitted
  have empty := RecursiveOutward.no_owners outward
  subst demand
  refine ⟨requirements, source, ?_⟩
  intro store receiving before
  simpa only [Option.bind_some] using RecursiveOutward.evaluation (store := store) (receiving := receiving) (before := before) outward

theorem bind_expression
    (source : Expression operations policy contracts world allowed scope environment (.bind parameter value body) result demand requirements)
    (closed : ClosedValue value) :
    ∃ reduced : Requirements demand,
      Expression operations policy contracts world allowed scope environment (body.subst parameter value) result demand reduced ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  cases source with
  | stable summary => exact ⟨_, .stable (CoherentSourceTypes.bind_summary summary closed), fun _ _ _ => rfl⟩
  | callable summary => cases summary with
      | summaryBind initializer body =>
          have empty := CallableSources.value_row initializer.to_generic closed.1
          subst_vars
          exact ⟨_, .callable (DeclaredSourceSubstitution.callable_substitution body initializer closed), fun _ _ _ => rfl⟩
  | bind initializer body =>
      have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase initializer) closed.1
      subst_vars
      refine ⟨_, substitution body (DeclaredSourceValues.value_summary initializer closed.1) closed, ?_⟩
      intro store receiving before
      rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase initializer) closed.1]
      simp only [OwnerPhaseTransitions.spendAll, RecursiveRecomposition.merge_empty_left]

theorem beta_expression
    (source : Expression operations policy contracts world allowed scope environment (.app (.lambda parameter body) value) result demand requirements)
    (closed : ClosedValue value) :
    ∃ reduced : Requirements demand,
      Expression operations policy contracts world allowed .none environment (body.subst parameter value) result demand reduced ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  cases source with
  | stable summary => exact ⟨_, .stable (CoherentSourceTypes.beta_summary summary closed), fun _ _ _ => rfl⟩
  | callable summary => cases summary with
      | summaryApp function argument admitted =>
          have functionRow := CallableSources.value_row function.to_generic trivial
          have argumentRow := CallableSources.value_row argument.to_generic closed.1
          subst_vars
          obtain ⟨reduced, next, evaluated⟩ := lambda_beta_expression function argument closed admitted
          exact ⟨reduced, next, fun store receiving before => by
            rw [evaluated]
            simp only [evaluate, RecursiveRequirements.evaluateFuel, OwnerSource.exportAt, List.nil_append]⟩
  | app function argument admitted =>
      have functionDemand := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase function) trivial
      have argumentDemand := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase argument) closed.1
      subst_vars
      obtain ⟨reduced, next, evaluated⟩ := lambda_beta_expression
        (DeclaredSourceValues.value_summary function trivial) (DeclaredSourceValues.value_summary argument closed.1) closed admitted
      refine ⟨reduced, next, ?_⟩
      intro store receiving before
      rw [evaluated, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase function) trivial, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase argument) closed.1]
      simp only [OwnerPhaseTransitions.spendAll, List.nil_append, RecursiveRecomposition.merge_empty_left]
      rfl

theorem branch_expression
    (source : Expression operations policy contracts world allowed scope environment (.branch (.boolean flag) yes no) result demand requirements) :
    ∃ (remaining : List Nat) (reduced : Requirements remaining),
      Expression operations policy contracts world allowed scope environment (if flag then yes else no) result remaining reduced ∧
      demand.Perm remaining ∧
      ∀ store receiving before row, Checked store receiving before requirements row →
        ∃ nextRow, Checked store receiving before reduced nextRow ∧ nextRow.Sublist row := by
  cases source with
  | stable summary => cases summary with
    | branch condition yesSource noSource => cases condition with
      | boolean =>
          cases flag with
          | false =>
              refine ⟨[], _, .stable noSource, .refl _, ?_⟩
              intro store receiving before row checked
              obtain ⟨firstRow, secondRow, left, right, rfl⟩ := request_parts checked
              exact ⟨secondRow, right, List.sublist_append_right _ _⟩
          | true =>
              refine ⟨[], _, .stable yesSource, .refl _, ?_⟩
              intro store receiving before row checked
              obtain ⟨firstRow, secondRow, left, right, rfl⟩ := request_parts checked
              exact ⟨firstRow, left, List.sublist_append_left _ _⟩
  | callable summary => cases summary with
    | summaryBranch condition yesSource noSource => cases condition with
      | summaryBoolean =>
          cases flag with
          | false =>
              refine ⟨[], _, .callable noSource, .refl _, ?_⟩
              intro store receiving before row checked
              obtain ⟨firstRow, secondRow, left, right, rfl⟩ := request_parts checked
              exact ⟨secondRow, right, List.sublist_append_right _ _⟩
          | true =>
              refine ⟨[], _, .callable yesSource, .refl _, ?_⟩
              intro store receiving before row checked
              obtain ⟨firstRow, secondRow, left, right, rfl⟩ := request_parts checked
              exact ⟨firstRow, left, List.sublist_append_left _ _⟩
  | branch condition yesSource noSource same =>
      have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase condition) trivial
      subst_vars
      cases flag with
      | false =>
          refine ⟨_, _, noSource, same, ?_⟩
          intro store receiving before row checked
          have evaluated := RecursiveRequirements.checked_complete checked
          rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase condition) trivial,
            RecursiveRecomposition.merge_empty_left] at evaluated
          obtain ⟨firstRow, secondRow, left, right, rfl⟩ := choice_parts (RecursiveRequirements.evaluate_sound evaluated)
          exact ⟨secondRow, right, List.sublist_append_right _ _⟩
      | true =>
          refine ⟨_, _, yesSource, .refl _, ?_⟩
          intro store receiving before row checked
          have evaluated := RecursiveRequirements.checked_complete checked
          rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase condition) trivial,
            RecursiveRecomposition.merge_empty_left] at evaluated
          obtain ⟨firstRow, secondRow, left, right, rfl⟩ := choice_parts (RecursiveRequirements.evaluate_sound evaluated)
          exact ⟨firstRow, left, List.sublist_append_left _ _⟩


end Ash.OneShot.DeclaredSourceExpressions

#print axioms Ash.OneShot.DeclaredSourceExpressions.lambda_beta_expression
#print axioms Ash.OneShot.DeclaredSourceExpressions.bind_expression
#print axioms Ash.OneShot.DeclaredSourceExpressions.beta_expression
#print axioms Ash.OneShot.DeclaredSourceExpressions.branch_expression
