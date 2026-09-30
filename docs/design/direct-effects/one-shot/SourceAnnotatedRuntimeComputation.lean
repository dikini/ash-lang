import SourceAnnotatedRuntimeReturns

/-! Branch selection and all four ordinary syntax reductions preserve the
annotated scheduled state. The existing choice-row and owner-permutation laws
supply the accounting. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeComputation
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked evaluate)
open SourcePlanSignatures (signature)
open SourceAnnotatedSources (Expression ValueSummary)
open SourceRetainedPlans (Forest)
open OwnerPhaseTransitions (spendAll)
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation Reduced)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Branch selection retains the selected source plan and may narrow the
checked effect row while preserving the ownership multiset. -/
theorem branch_preserves_bounds {plan : Plan dependencies}
    (bounds : Annotation world plan)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope (.branch hint (.boolean conditionHint flag) yes no) stack plan forest output demand row evidence) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBounds : Annotation world nextPlan,
    ∃ remaining nextRow,
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        scope (if flag then yes else no) stack nextPlan forest output remaining nextRow evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧
      Reduced world (if flag then .ifTrue else .ifFalse) bounds nextBounds := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
    subst demand
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | checked hint metadata node => cases node with
      | branch condition yesSource noSource same =>
        cases plan with
        | sequence conditionPlan branches => cases branches with
          | choice yesPlan noPlan =>
            cases signatureSame
            cases contextual with
            | sequence conditionCheck choices => cases choices with
              | choice yesCheck noCheck =>
                have erasedCondition := DeclaredSources.expression_erase
                  (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase condition.erase))
                have empty := SourceTemplates.expression_value_demand erasedCondition trivial
                cases empty
                obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
                have activeCheck := RecursiveRequirements.checked_prepend_iff.mp currentCheck
                have evaluated := RecursiveRequirements.checked_complete activeCheck
                rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation erasedCondition trivial,
                  RecursiveRecomposition.merge_empty_left] at evaluated
                obtain ⟨yesRow, noRow, yesChecked, noChecked, rfl⟩ :=
                  RecursiveExpressions.choice_parts (RecursiveRequirements.evaluate_sound evaluated)
                simp only [List.nil_append] at pendingCheck ⊢
                cases flag with
                | false =>
                  have nextPending := pendingCheck
                  rw [RecursiveExpressions.spend_permutation same] at nextPending
                  have included := (List.sublist_append_right yesRow noRow).append (List.Sublist.refl pendingRow)
                  exact ⟨_, noPlan, bounds.second.right, _, _, .checked noSource scopeTyped pending closing templates matched noCheck unique
                    (.sequence (RecursiveRequirements.checked_prepend_iff.mpr noChecked) nextPending)
                    (checked_footprint_subset accepted included.subset) rfl,
                    same.append_right _, included, .ifFalse bounds⟩
                | true =>
                  have included := (List.sublist_append_left yesRow noRow).append (List.Sublist.refl pendingRow)
                  exact ⟨_, yesPlan, bounds.second.left, _, _, .checked yesSource scopeTyped pending closing templates matched yesCheck unique
                    (.sequence (RecursiveRequirements.checked_prepend_iff.mpr yesChecked) pendingCheck)
                    (checked_footprint_subset accepted included.subset) rfl, .refl _, included, .ifTrue bounds⟩


theorem branch_preserves
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.branch hint (.boolean conditionHint flag) yes no) stack forest output demand row evidence) :
    ∃ remaining nextRow,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        scope (if flag then yes else no) stack forest output remaining nextRow evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      obtain ⟨_, _, _, remaining, nextRow, next, permutation, included, _⟩ := branch_preserves_bounds .absent
        (.checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting)
      exact ⟨remaining, nextRow, next.state, permutation, included⟩


/-- The four ordinary reductions select exact existing bound packets while
reusing source substitution, row narrowing and owner accounting. The stable
checking plan is not a literal-source identity claim after substitution. -/
theorem ordinary_preserves_bounds {plan : Plan dependencies}
    (bounds : Annotation world plan)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope before stack plan forest output demand row evidence)
    (step : SourceAnnotatedCode.Reduction before scope after nextScope) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBounds : Annotation world nextPlan,
    ∃ remaining nextRow,
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        nextScope after stack nextPlan forest output remaining nextRow evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ Reduced world step.rule bounds nextBounds := by
  cases step with
  | bind closed ready =>
      obtain ⟨_, nextPlan, nextBounds, next, selected⟩ := SourceAnnotatedRuntimeState.bind_preserves_bounds bounds state closed
      exact ⟨_, nextPlan, nextBounds, demand, row, next, .refl _, .refl _, selected⟩
  | beta closed ready =>
      obtain ⟨_, nextPlan, nextBounds, next, selected⟩ := SourceAnnotatedRuntimeState.beta_preserves_bounds bounds state closed
      exact ⟨_, nextPlan, nextBounds, demand, row, next, .refl _, .refl _, selected⟩
  | ifTrue => exact branch_preserves_bounds bounds state
  | ifFalse => exact branch_preserves_bounds bounds state

/-- An actual ordinary raw step and its successor share the same persistent
snapshot. The entire pending forest and its annotations are unchanged. -/
theorem ordinary_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope before stack snapshot.plan snapshot.forest output demand row evidence)
    (step : SourceAnnotatedCode.Reduction before scope after nextScope) :
    ∃ next : SourceBoundSnapshots.Snapshot world, ∃ remaining nextRow,
      RawStep ⟨before.erase, scope, stack.erase⟩ ⟨after.erase, nextScope, stack.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        nextScope after stack next.plan next.forest output remaining nextRow evidence ∧
      SourceBoundSnapshots.Computed step.rule snapshot next ∧ demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨_, nextPlan, nextBounds, remaining, nextRow, next, permutation, included, selected⟩ :=
    ordinary_preserves_bounds snapshot.current state step
  exact ⟨snapshot.computed nextPlan nextBounds, remaining, nextRow, step.executes stack.erase, next,
    .step snapshot nextBounds selected, permutation, included⟩

theorem ordinary_preserves
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope before stack forest output demand row evidence)
    (step : SourceAnnotatedCode.Reduction before scope after nextScope) :
    ∃ remaining nextRow,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        nextScope after stack forest output remaining nextRow evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      obtain ⟨_, _, _, remaining, nextRow, next, permutation, included, _⟩ := ordinary_preserves_bounds .absent
        (.checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting) step
      exact ⟨remaining, nextRow, next.state, permutation, included⟩

end Ash.OneShot.SourceAnnotatedRuntimeComputation

#print axioms Ash.OneShot.SourceAnnotatedRuntimeComputation.branch_preserves
#print axioms Ash.OneShot.SourceAnnotatedRuntimeComputation.ordinary_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeComputation.branch_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedRuntimeComputation.ordinary_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedRuntimeComputation.ordinary_snapshot
