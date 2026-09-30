import SourceAnnotatedStoredState
import SourceAnnotatedRuntimeComputation

/-! Ordinary computation retains the exact joint pending source and packet
stack. Existing substitution, branch selection and row laws update the current
source and its bound annotation. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeState
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceAnnotatedSources (Expression)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourcePlanBounds (Annotation Reduced)
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

theorem AtPackets.replace_current
    {requirements : Requirements currentDemand} {plan : Plan dependencies}
    (current : Expression operations policy contracts world allowed nextScope (fun _ => none)
      next input currentDemand reduced (signature plan))
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports nextScope ticket)
    (pending : SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world
      stack input output pendingDemand pendingRequirements resumes forest .nil allowed [] stored)
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals)
    (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world plan forest)
    (unique : (ownedTickets stack.erase).Nodup)
    (evaluated : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase))
      (.sequence (requirements.prepend (OwnerPhases.ofStack tables stack.erase)) pendingRequirements) row)
    (accepted : checkFootprint outside row = true)
    (accounting : demand = currentDemand ++ pendingDemand)
    (same : ∀ store receiving before, RecursiveRequirements.evaluate store receiving before reduced =
      RecursiveRequirements.evaluate store receiving before requirements) :
    AtPackets operations policy contracts tables families required actions annotations world outward outside nextScope next stack plan forest output demand row stored evidence := by
  apply AtPackets.checked current scopeTyped pending closing templates matched contextual unique _ accepted accounting
  apply RecursiveRequirements.evaluate_sound
  have original := RecursiveRequirements.checked_complete evaluated
  simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend] at original ⊢
  rw [same]
  exact original

theorem AtPackets.bind_preserves_bounds {plan : Plan dependencies}
    (bounds : Annotation world plan)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside scope
      (.bind hint parameter value body) stack plan forest output demand row stored evidence)
    (closed : ClosedValue value.erase) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBounds : Annotation world nextPlan,
      AtPackets operations policy contracts tables families required actions annotations world outward outside scope
      (body.subst parameter value) stack nextPlan forest output demand row stored evidence ∧
      Reduced world .bind bounds nextBounds := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
    have originalCurrent := current
    generalize sameSignature : signature plan = currentSignature at current
    cases current with
    | checked hint metadata node => cases node with
      | bind initializer body =>
        cases plan with
        | sequence initialPlan bodyPlan =>
          obtain ⟨reduced, replacement, same⟩ := SourceAnnotatedSources.bind_expression originalCurrent closed
          cases contextual with
          | sequence first second =>
            exact ⟨_, bodyPlan, bounds.second,
              AtPackets.replace_current replacement scopeTyped pending closing templates matched second unique evaluated accepted accounting same, .bind bounds⟩


/-- Beta reduction reuses the actual latent body plan and its check. Its empty
lexical ticket scope is derived by the existing source substitution theorem. -/
theorem AtPackets.beta_preserves_bounds {plan : Plan dependencies}
    (bounds : Annotation world plan)
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside scope
      (.app hint (.lambda functionHint parameter body) value) stack plan forest output demand row stored evidence)
    (closed : ClosedValue value.erase) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBounds : Annotation world nextPlan,
      AtPackets operations policy contracts tables families required actions annotations world outward outside .none
      (body.subst parameter value) stack nextPlan forest output demand row stored evidence ∧
      Reduced world .beta bounds nextBounds := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
    have originalCurrent := current
    generalize sameSignature : signature plan = currentSignature at current
    cases current with
    | checked hint metadata node => cases node with
      | app function argument admitted =>
        cases plan with
        | sequence functionPlan rest => cases rest with
          | sequence argumentPlan bodyPlan =>
            obtain ⟨reduced, replacement, same⟩ := SourceAnnotatedSources.beta_expression originalCurrent closed
            cases contextual with
            | sequence first rest => cases rest with
              | sequence argument body =>
                exact ⟨_, bodyPlan, bounds.second.second,
                  AtPackets.replace_current replacement .none pending closing templates matched body unique evaluated accepted accounting same, .beta bounds⟩

end Ash.OneShot.SourceAnnotatedRuntimeState

namespace Ash.OneShot.SourceAnnotatedStoredComputation
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
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.branch hint (.boolean conditionHint flag) yes no) stack plan forest output demand row stored evidence) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBounds : Annotation world nextPlan,
    ∃ remaining nextRow,
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        scope (if flag then yes else no) stack nextPlan forest output remaining nextRow stored evidence ∧
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


theorem ordinary_preserves_bounds {plan : Plan dependencies}
    (bounds : Annotation world plan)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope before stack plan forest output demand row stored evidence)
    (step : SourceAnnotatedCode.Reduction before scope after nextScope) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBounds : Annotation world nextPlan,
    ∃ remaining nextRow,
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        nextScope after stack nextPlan forest output remaining nextRow stored evidence ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ Reduced world step.rule bounds nextBounds := by
  cases step with
  | bind closed ready =>
      obtain ⟨_, nextPlan, nextBounds, next, selected⟩ := SourceAnnotatedRuntimeState.AtPackets.bind_preserves_bounds bounds state closed
      exact ⟨_, nextPlan, nextBounds, demand, row, next, .refl _, .refl _, selected⟩
  | beta closed ready =>
      obtain ⟨_, nextPlan, nextBounds, next, selected⟩ := SourceAnnotatedRuntimeState.AtPackets.beta_preserves_bounds bounds state closed
      exact ⟨_, nextPlan, nextBounds, demand, row, next, .refl _, .refl _, selected⟩
  | ifTrue => exact branch_preserves_bounds bounds state
  | ifFalse => exact branch_preserves_bounds bounds state

/-- An actual ordinary raw step and its successor share the same persistent
snapshot. The entire pending forest and its annotations are unchanged. -/
theorem ordinary_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope before stack snapshot.plan snapshot.forest output demand row stored evidence)
    (step : SourceAnnotatedCode.Reduction before scope after nextScope) :
    ∃ next : SourceBoundSnapshots.Snapshot world, ∃ remaining nextRow,
      RawStep ⟨before.erase, scope, stack.erase⟩ ⟨after.erase, nextScope, stack.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        nextScope after stack next.plan next.forest output remaining nextRow stored evidence ∧
      SourceBoundSnapshots.Computed step.rule snapshot next ∧ demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨_, nextPlan, nextBounds, remaining, nextRow, next, permutation, included, selected⟩ :=
    ordinary_preserves_bounds snapshot.current state step
  exact ⟨snapshot.computed nextPlan nextBounds, remaining, nextRow, step.executes stack.erase, next,
    .step snapshot nextBounds selected, permutation, included⟩

end Ash.OneShot.SourceAnnotatedStoredComputation

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.replace_current
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.bind_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.beta_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedStoredComputation.branch_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedStoredComputation.ordinary_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedStoredComputation.ordinary_snapshot
