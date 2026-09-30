import SourceAnnotatedSubstitution
import SourcePlanSignatureChecking

/-! Bind and beta reduction retain the synchronized body derivation. The
ownership and requirement evaluation arguments reuse the established lemmas;
no weaker paired source certificate is used as the successor. -/
namespace Ash.OneShot.SourceAnnotatedSources
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements evaluate)
open OwnerPhaseTransitions (spendAll)
open RecursiveContexts (evaluate_request)
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourcePlanSignatures (Signature)

/-- Extract the actual lambda body without selecting another intermediate type. -/
theorem lambda_body
    (function : Expression operations policy contracts world allowed scope environment
      (.lambda functionHint parameter code) (.function input output requests latent bodySignature) functionDemand functionRequirements functionSignature) :
    ∃ demand requirements,
      Expression operations policy contracts world requests .none (environment.extend parameter input)
        code output demand requirements bodySignature ∧ RecursiveOutward.Outward requirements (some latent) := by
  cases function with
  | checked hint metadata node => cases node with
    | lambda body outward formed bound => exact ⟨_, _, body, outward⟩

theorem beta_body
    (function : Expression operations policy contracts world allowed scope environment
      (.lambda functionHint parameter code) (.function input output requests latent bodySignature) functionDemand functionRequirements functionSignature)
    (argument : ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value.erase) (admitted : requests ⊆ allowed) :
    ∃ demand requirements,
      Expression operations policy contracts world allowed .none environment
        (code.subst parameter value) output demand requirements bodySignature ∧
      RecursiveOutward.Outward requirements (some latent) := by
  obtain ⟨demand, requirements, body, outward⟩ := lambda_body function
  have replaced := substitution body (Values.change_allowed argument closed.1 requests) closed
  exact ⟨demand, requirements, expression_allowed_mono replaced admitted, outward⟩

theorem bind_expression
    (source : Expression operations policy contracts world allowed scope environment (.bind hint parameter value body)
      result demand requirements (.sequence initialSignature bodySignature))
    (closed : ClosedValue value.erase) :
    ∃ reduced, Expression operations policy contracts world allowed scope environment (body.subst parameter value)
      result demand reduced bodySignature ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  cases source with
  | checked hint metadata node => cases node with
    | bind initializer body =>
        have empty := SourceTemplates.expression_value_demand
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase initializer.erase))) closed.1
        subst_vars
        refine ⟨_, substitution body (Values.summary initializer closed.1) closed, ?_⟩
        intro store receiving before
        rw [RecursiveRequirements.evaluate_sequence,
          RecursiveRecomposition.value_evaluation
            (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase initializer.erase))) closed.1]
        simp only [OwnerPhaseTransitions.spendAll, RecursiveRecomposition.merge_empty_left]

theorem beta_expression
    (source : Expression operations policy contracts world allowed scope environment (.app hint (.lambda functionHint parameter body) value)
      result demand requirements (.sequence functionSignature (.sequence argumentSignature bodySignature)))
    (closed : ClosedValue value.erase) :
    ∃ reduced, Expression operations policy contracts world allowed .none environment (body.subst parameter value)
      result demand reduced bodySignature ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  cases source with
  | checked hint metadata node => cases node with
    | app function argument admitted =>
        have functionDemand := SourceTemplates.expression_value_demand
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase function.erase))) trivial
        have argumentDemand := SourceTemplates.expression_value_demand
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase argument.erase))) closed.1
        subst_vars
        obtain ⟨demand, reduced, next, outward⟩ := beta_body function (Values.summary argument closed.1) closed admitted
        have empty := RecursiveOutward.no_owners outward
        subst demand
        refine ⟨reduced, next, ?_⟩
        intro store receiving before
        rw [RecursiveOutward.evaluation outward, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
          RecursiveRecomposition.value_evaluation
            (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase function.erase))) trivial,
          RecursiveRecomposition.value_evaluation
            (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase argument.erase))) closed.1]
        simp only [OwnerPhaseTransitions.spendAll, List.nil_append, RecursiveRecomposition.merge_empty_left]
        rfl

theorem branch_expression
    (source : Expression operations policy contracts world allowed scope environment
      (.branch hint (.boolean conditionHint flag) yes no) result demand requirements checking) :
    ∃ (remaining : List Nat) (reduced : Requirements remaining) (dependencies : SourceDependencyAnnotations.Dependencies)
      (nextChecking : Signature dependencies),
      Expression operations policy contracts world allowed scope environment (if flag then yes else no) result remaining reduced nextChecking ∧
      demand.Perm remaining ∧
      ∀ store receiving before row, RecursiveRequirements.Checked store receiving before requirements row →
        ∃ nextRow, RecursiveRequirements.Checked store receiving before reduced nextRow ∧ nextRow.Sublist row := by
  cases source with
  | checked hint metadata node => cases node with
    | branch condition yesSource noSource same =>
        have erased := DeclaredSources.expression_erase
          (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase condition.erase))
        have empty := SourceTemplates.expression_value_demand erased trivial
        subst_vars
        cases flag with
        | false =>
            refine ⟨_, _, _, _, noSource, same, ?_⟩
            intro store receiving before row checked
            have evaluated := RecursiveRequirements.checked_complete checked
            rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation erased trivial,
              RecursiveRecomposition.merge_empty_left] at evaluated
            obtain ⟨yesRow, noRow, yesChecked, noChecked, rfl⟩ :=
              RecursiveExpressions.choice_parts (RecursiveRequirements.evaluate_sound evaluated)
            exact ⟨noRow, noChecked, List.sublist_append_right _ _⟩
        | true =>
            refine ⟨_, _, _, _, yesSource, .refl _, ?_⟩
            intro store receiving before row checked
            have evaluated := RecursiveRequirements.checked_complete checked
            rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation erased trivial,
              RecursiveRecomposition.merge_empty_left] at evaluated
            obtain ⟨yesRow, noRow, yesChecked, noChecked, rfl⟩ :=
              RecursiveExpressions.choice_parts (RecursiveRequirements.evaluate_sound evaluated)
            exact ⟨yesRow, yesChecked, List.sublist_append_left _ _⟩

/-- Every annotated ordinary reduction preserves its source judgment. The
existing effect evaluation and owner-permutation laws account for branch
selection; no successor source premise is supplied by the reduction. -/
theorem reduction_preserves
    (source : Expression operations policy contracts world allowed scope environment before result demand requirements checking)
    (step : SourceAnnotatedCode.Reduction before scope after nextScope) :
    ∃ (remaining : List Nat) (reduced : Requirements remaining) (dependencies : SourceDependencyAnnotations.Dependencies)
      (nextChecking : Signature dependencies),
      Expression operations policy contracts world allowed nextScope environment after result remaining reduced nextChecking ∧
      demand.Perm remaining ∧
      ∀ store receiving phases row, RecursiveRequirements.Checked store receiving phases requirements row →
        ∃ nextRow, RecursiveRequirements.Checked store receiving phases reduced nextRow ∧ nextRow.Sublist row := by
  cases step with
  | bind closed ready =>
      cases source with
      | checked hint metadata node => cases node with
        | bind initializer body =>
            obtain ⟨reduced, next, evaluation⟩ := bind_expression (.checked hint metadata (.bind initializer body)) closed
            refine ⟨_, reduced, _, _, next, .refl _, ?_⟩
            intro store receiving phases row checked
            exact ⟨row, RecursiveRequirements.evaluate_sound
              ((evaluation store receiving phases).trans (RecursiveRequirements.checked_complete checked)), .refl _⟩
  | beta closed ready =>
      cases source with
      | checked hint metadata node => cases node with
        | app function argument admitted =>
            obtain ⟨reduced, next, evaluation⟩ := beta_expression (.checked hint metadata (.app function argument admitted)) closed
            refine ⟨_, reduced, _, _, next, .refl _, ?_⟩
            intro store receiving phases row checked
            exact ⟨row, RecursiveRequirements.evaluate_sound
              ((evaluation store receiving phases).trans (RecursiveRequirements.checked_complete checked)), .refl _⟩
  | ifTrue => exact branch_expression source
  | ifFalse => exact branch_expression source

end Ash.OneShot.SourceAnnotatedSources

#print axioms Ash.OneShot.SourceAnnotatedSources.lambda_body

#print axioms Ash.OneShot.SourceAnnotatedSources.beta_body

#print axioms Ash.OneShot.SourceAnnotatedSources.bind_expression

#print axioms Ash.OneShot.SourceAnnotatedSources.beta_expression

#print axioms Ash.OneShot.SourceAnnotatedSources.branch_expression

#print axioms Ash.OneShot.SourceAnnotatedSources.reduction_preserves
