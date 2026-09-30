import SourceDependencySubstitution
import DeclaredSourceExpressions

/-! Bind and beta reduction preserve the hereditary dependency body. Existing
value-demand and requirement-evaluation lemmas supply the ordinary one-shot
accounting. No capture or disposal admission is inferred from these results. -/
namespace Ash.OneShot.SourceDependencyAnnotations
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements evaluate)

/-- A value may have administrative pair nodes, but introduces no request,
cleanup, handler or continuation invocation while being evaluated. -/
inductive Dependencies.Silent : Dependencies → Prop where
  | pure : Silent .pure
  | sequence (left : Silent first) (right : Silent second) : Silent (.sequence first second)

theorem value_silent
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements dependencies)
    (isValue : code.IsValue) : dependencies.Silent := by
  induction source using Expression.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ => True) with
  | unit | boolean | integer | reference | lambda | purePair => exact .pure
  | pair left right ihLeft ihRight => exact .sequence (ihLeft isValue.1) (ihRight isValue.2)
  | «variable» | app | bind | branch | perform | handler | resume | discard | cleanup | resource => cases isValue
  | typed | annotated | unavailable | available | nil | cons => trivial

theorem beta_body
    (function : Expression operations policy contracts world allowed scope environment
      (.lambda parameter code) (.function input output requests latent dependencies) functionDemand functionRequirements functionDependencies)
    (argument : ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value) (admitted : requests ⊆ allowed) :
    ∃ demand, ∃ requirements : Requirements demand,
      Expression operations policy contracts world allowed .none environment
        (code.subst parameter value) output demand requirements dependencies ∧
      RecursiveOutward.Outward requirements (some latent) := by
  obtain ⟨demand, requirements, body, outward⟩ := lambda_dependencies function
  have replaced := substitution body (Values.change_allowed argument closed.1 requests) closed
  exact ⟨demand, requirements, expression_allowed_mono replaced admitted, outward⟩

/-- Substitution removes a silent initializer, retaining the exact annotated
body. The existing requirement evaluator proves that owner/effect checking is
unchanged, under every store, receiving context and owner phase. -/
theorem bind_expression
    (source : Expression operations policy contracts world allowed scope environment (.bind parameter value body)
      result demand requirements dependencies)
    (closed : ClosedValue value) :
    ∃ (reduced : Requirements demand) (remaining : Dependencies),
      Expression operations policy contracts world allowed scope environment (body.subst parameter value)
        result demand reduced remaining ∧
      (∃ initial, dependencies = .sequence initial remaining ∧ initial.Silent) ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  cases source with
  | bind initializer body =>
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (expression_erase initializer)) closed.1
      subst_vars
      refine ⟨_, _, substitution body (Values.summary initializer closed.1) closed,
        ⟨_, rfl, value_silent initializer closed.1⟩, ?_⟩
      intro store receiving before
      rw [RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (expression_erase initializer)) closed.1]
      simp only [OwnerPhaseTransitions.spendAll, RecursiveRecomposition.merge_empty_left]

/-- Beta reduction exposes the function's same latent annotation. Only the
silent function and argument prefixes are removed. The old requirement check
is preserved exactly, rather than replaced by a fresh assumed certificate. -/
theorem beta_expression
    (source : Expression operations policy contracts world allowed scope environment (.app (.lambda parameter body) value)
      result demand requirements dependencies)
    (closed : ClosedValue value) :
    ∃ (reduced : Requirements demand) (remaining : Dependencies),
      Expression operations policy contracts world allowed .none environment (body.subst parameter value)
        result demand reduced remaining ∧
      (∃ function argument, dependencies = .sequence function (.sequence argument remaining) ∧
        function.Silent ∧ argument.Silent) ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  cases source with
  | app function argument admitted =>
      have functionDemand := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (expression_erase function)) trivial
      have argumentDemand := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (expression_erase argument)) closed.1
      subst_vars
      obtain ⟨demand, reduced, next, outward⟩ := beta_body function (Values.summary argument closed.1) closed admitted
      have empty := RecursiveOutward.no_owners outward
      subst demand
      refine ⟨reduced, _, next, ⟨_, _, rfl, value_silent function trivial, value_silent argument closed.1⟩, ?_⟩
      intro store receiving before
      rw [RecursiveOutward.evaluation outward, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (expression_erase function)) trivial,
        RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (expression_erase argument)) closed.1]
      simp only [OwnerPhaseTransitions.spendAll, List.nil_append, RecursiveRecomposition.merge_empty_left]
      rfl

namespace Examples

theorem annotated_function_closed : ClosedValue functionCode :=
  ⟨trivial, rfl, by intro _ member; cases member⟩

/-- The actual bind substitutes a function containing cleanup. The following
beta step exposes that same cleanup annotation. Both source derivations and
their exact old requirement checks follow the generic reduction theorems. -/
theorem higher_order_reduction :
    RawStep ⟨boundProgram, .none, .nil⟩ ⟨.app functionCode .unit, .none, .nil⟩ [] [] ∧
    RawStep ⟨.app functionCode .unit, .none, .nil⟩ ⟨cleanupBody, .none, .nil⟩ [] [] ∧
    ∃ first second : Requirements [],
      Expression operations policy contracts [] allowed .none Environment.empty (.app functionCode .unit)
        .unit [] first (.sequence .pure (.sequence .pure cleanupDependencies)) ∧
      Expression operations policy contracts [] allowed .none Environment.empty cleanupBody
        .unit [] second cleanupDependencies ∧
      ∀ store receiving before,
        evaluate store receiving before first = evaluate store receiving before (.sequence noRequirements invokedRequirements) ∧
        evaluate store receiving before second = evaluate store receiving before first := by
  have unitClosed : ClosedValue .unit := ⟨trivial, rfl, by intro _ member; cases member⟩
  refine ⟨RawStep.bind 7 functionCode (.app (.variable 7) .unit) .none .nil annotated_function_closed
    (by intro name member; simpa [Code.dependencies] using member),
    RawStep.beta 3 cleanupBody .unit .none .nil unitClosed annotated_function_closed, ?_⟩
  obtain ⟨first, afterBind, bound, ⟨initial, same, silent⟩, firstCheck⟩ :=
    bind_expression bound_function_retains_cleanup annotated_function_closed
  have bindSame : afterBind = .sequence .pure (.sequence .pure cleanupDependencies) :=
    (Dependencies.sequence.inj same).2.symm
  subst afterBind
  change Expression operations policy contracts [] allowed .none Environment.empty (.app functionCode .unit)
    .unit [] first (.sequence .pure (.sequence .pure cleanupDependencies)) at bound
  obtain ⟨second, afterBeta, reduced, ⟨function, argument, same, functionSilent, argumentSilent⟩, secondCheck⟩ :=
    beta_expression bound unitClosed
  have betaSame : afterBeta = cleanupDependencies := (Dependencies.sequence.inj (Dependencies.sequence.inj same).2).2.symm
  subst afterBeta
  change Expression operations policy contracts [] allowed .none Environment.empty cleanupBody .unit [] second cleanupDependencies at reduced
  exact ⟨first, second, bound, reduced, fun store receiving before => ⟨firstCheck store receiving before, secondCheck store receiving before⟩⟩

end Examples

end Ash.OneShot.SourceDependencyAnnotations

#print axioms Ash.OneShot.SourceDependencyAnnotations.value_silent
#print axioms Ash.OneShot.SourceDependencyAnnotations.beta_body
#print axioms Ash.OneShot.SourceDependencyAnnotations.bind_expression
#print axioms Ash.OneShot.SourceDependencyAnnotations.beta_expression

#print axioms Ash.OneShot.SourceDependencyAnnotations.Examples.annotated_function_closed

#print axioms Ash.OneShot.SourceDependencyAnnotations.Examples.higher_order_reduction
