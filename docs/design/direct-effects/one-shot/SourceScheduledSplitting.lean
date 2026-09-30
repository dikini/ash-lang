import SourceScheduledRechecking

/-! A physical stack split retains the exact source plans on both sides.
This is the converse of checked segment append; it shares the same evaluation
equations and does not choose replacement annotations. -/
namespace Ash.OneShot.SourceScheduledFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value)
open SourcePlannedFrames (DependencyScope)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledRecomposition (forest_append_assoc)
open SourceDependencyChecks (scope_append_assoc)
open SourcePlannedRecomposition (hints_append_assoc)
open RecursiveRequirements (Requirements Store evaluate)
open ProtectionResiduals (merge merge_assoc)
open OwnerPhaseTransitions (spendAll)

variable {front tail : Stack}

theorem segment_split {hints : Hints wholeScope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      (front.append tail) input output demand requirements records forest outside incoming outgoing) :
    ∃ (middle : Value) (boundary : List Instance) (firstDemand secondDemand : List Nat)
      (firstRequirements : Requirements firstDemand) (secondRequirements : Requirements secondDemand)
      (firstRecords secondRecords : Store) (firstScope secondScope : DependencyScope),
      ∃ (firstHints : Hints firstScope) (secondHints : Hints secondScope)
        (firstForest : Forest firstHints) (secondForest : Forest secondHints),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        front input middle firstDemand firstRequirements firstRecords firstForest (secondForest.append outside) incoming boundary ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        tail middle output secondDemand secondRequirements secondRecords secondForest outside boundary outgoing ∧
      wholeScope = firstScope.append secondScope ∧ HEq hints (firstHints.append secondHints) ∧
      HEq forest (firstForest.append secondForest) ∧ demand = firstDemand ++ secondDemand ∧
      records = firstRecords ++ secondRecords ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before firstRequirements)
          (evaluate store receiving (spendAll before firstDemand) secondRequirements) := by
  induction front generalizing input demand requirements records wholeScope incoming with
  | nil =>
      refine ⟨input, incoming, [], demand, .request [] [], requirements, [], records, .nil, wholeScope,
        .nil, hints, .nil, forest, .nil (List.Subset.refl _), source, rfl, HEq.rfl, HEq.rfl, rfl, rfl, ?_⟩
      intro store receiving before
      simp only [RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | push entry front ih => cases source with
    | push head rest bound =>
      obtain ⟨middle, boundary, firstDemand, secondDemand, firstReq, secondReq, firstRecords, secondRecords,
        firstScope, secondScope, firstHints, secondHints, firstForest, secondForest,
        first, second, sameScope, sameHints, sameForest, sameDemand, sameRecords, evaluation⟩ := ih rest
      cases sameScope
      cases sameHints
      cases sameForest
      have headNext := head.receiving_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc _ _ _)
      refine ⟨middle, boundary, _, secondDemand, _, secondReq, firstRecords, secondRecords, _, secondScope,
        _, secondHints, _, secondForest, .push headNext first bound, second,
        head.source.source.erase.realizes.append.symm, head.source.decorate_append _ _, head.decorate_append _ _,
        by simp only [sameDemand, List.append_assoc], sameRecords, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
        OwnerPhases.stack_append, List.append_assoc, PhaseRechecking.spendAll_append, merge_assoc]
  | live owner inputType answerType capture caller front ihSaved ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound rest resume close bound =>
      obtain ⟨middle, boundary, firstDemand, secondDemand, firstReq, secondReq, firstRecords, secondRecords,
        firstScope, secondScope, firstHints, secondHints, firstForest, secondForest,
        first, second, sameScope, sameHints, sameForest, sameDemand, sameRecords, evaluation⟩ := ih rest
      cases sameScope
      cases sameHints
      cases sameForest
      have savedNext := saved.receiving_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc _ _ _)
      refine ⟨middle, boundary, firstDemand, secondDemand, _, secondReq, _, secondRecords, _, secondScope,
        _, secondHints, _, secondForest,
        .live known actionKnown inputAnnotation answerAnnotation scope held savedNext savedBound first resume close bound,
        second, rfl, HEq.rfl, HEq.rfl, sameDemand, ?_, ?_⟩
      · simp only [sameRecords, List.cons_append, List.append_assoc]
      · intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent, spendAll, evaluation, merge_assoc]
  | spent owner answerType caller front ih => cases source with
    | spent known annotation scope rest bound =>
      obtain ⟨middle, boundary, firstDemand, secondDemand, firstReq, secondReq, firstRecords, secondRecords,
        firstScope, secondScope, firstHints, secondHints, firstForest, secondForest,
        first, second, sameScope, sameHints, sameForest, sameDemand, sameRecords, evaluation⟩ := ih rest
      cases sameScope
      cases sameHints
      cases sameForest
      refine ⟨middle, boundary, firstDemand, secondDemand, _, secondReq, firstRecords, secondRecords, _, secondScope,
        _, secondHints, _, secondForest, .spent known annotation scope first bound,
        second, rfl, HEq.rfl, HEq.rfl, sameDemand, sameRecords, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent, spendAll, evaluation, merge_assoc]

end Ash.OneShot.SourceScheduledFrames

#print axioms Ash.OneShot.SourceScheduledFrames.segment_split
