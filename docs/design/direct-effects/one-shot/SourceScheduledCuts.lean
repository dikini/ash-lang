import SourceScheduledRecomposition

/-! The physical handler cut preserves joint source/checking witnesses.
Saved and waiting segments retain explicit plan forests, the refined answer,
requirements and owner records. Exact forest recomposition fixes each suffix. -/
namespace Ash.OneShot.SourceScheduledCuts
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value)
open SourcePlannedFrames (DependencyScope)
open SourceScheduledFrames (Segment)
open SourceRetainedPlans (Forest)
open SourceScheduledRecomposition (forest_append_assoc)
open SourceDependencyChecks (scope_append_assoc)
open SourcePlannedRecomposition (hints_append_assoc)
open SourceContextualHints (Hints)
open RecursiveRequirements (Requirements Store evaluate)
open ProtectionResiduals (merge merge_assoc)
open OwnerPhaseTransitions (spendAll)

theorem capture_segments {hints : Hints wholeScope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world whole input output demand requirements records forest outside incoming outgoing) :
    ∃ (answer : Value) (residual : List Instance) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedScope tailScope : DependencyScope),
      ∃ (savedHints : Hints capturedScope) (waitingHints : Hints tailScope),
      ∃ (savedForest : Forest savedHints) (waitingForest : Forest waitingHints),
      answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧ SourcePlannedFrames.Frame (evidence := evidence) operations policy contracts tables families required world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler))
        (fun rest => .handler (required handler) rest) (handler.effectInst :: residual) residual ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world capture input answer capturedDemand capturedRequirements capturedRecords savedForest (waitingForest.append outside) incoming residual ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world tail answer output tailDemand tailRequirements tailRecords waitingForest outside residual outgoing ∧
      wholeScope = capturedScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ HEq forest (savedForest.append waitingForest) ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧
      (∀ operation, SourceDependencyCapture.select requested operation wholeScope =
        SourceDependencyCapture.chosen operation (tables handler) (families handler) capturedScope tailScope) ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements)
          (evaluate store receiving (spendAll before capturedDemand) tailRequirements) := by
  induction cut generalizing input demand requirements records wholeScope incoming with
  | hit handler tail same => cases source with
    | push current rest bound =>
      have retainedFrame := current
      cases current with
      | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes =>
          refine ⟨_, _, [], _, .sequence ((Requirements.request [] []).prepend []) (.request [] []), _, [], _, _, _, _, _, .handler (required := required handler) .nil, _, annotation,
            .handler scope annotation clauses coverage unique declarations recipes capabilities modes,
            ?_, rest, rfl, HEq.rfl, HEq.rfl, rfl, rfl, ?_, ?_⟩
          · exact Segment.push (restHints := .nil) retainedFrame (.nil (List.Subset.refl _)) bound
          · intro operation
            simp only [SourceDependencyCapture.select, if_pos same.symm, SourceDependencyCapture.chosen]
            rfl
          intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | push entry rest cap tail handler miss next ih => cases source with
    | push current rest bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope, savedHints, waitingHints, savedForest, waitingForest,
          annotation, selected, saved, outside, sameScope, sameHints, sameForest, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        cases sameScope
        cases sameHints
        cases sameForest
        have currentNext := current.receiving_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc _ _ _)
        refine ⟨answer, residual, _, tailDemand, _, tailReq, capRecords, tailRecords, _, tailScope, _, waitingHints, _, waitingForest, annotation, selected, .push currentNext saved bound, outside,
          current.source.source.erase.realizes.append.symm, current.source.decorate_append _ _, current.decorate_append _ _,
          by simp only [sameDemand, List.append_assoc], sameRecords, ?_, ?_⟩
        · intro operation
          rw [current.source.source.erase.realizes.select_miss miss, selection operation, SourceDependencyCapture.chosen_prepend]
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
          handler_cut_reconstructs next, OwnerPhases.stack_append, List.append_assoc,
          PhaseRechecking.spendAll_append, merge_assoc]
  | live owner inputType answerType savedScope caller rest cap tail handler next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scopeKnown held historical savedInterface rest resume close bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope, savedHints, waitingHints, savedForest, waitingForest,
          annotation, selected, saved, outside, sameScope, sameHints, sameForest, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        cases sameScope
        cases sameHints
        cases sameForest
        have historicalNext := historical.receiving_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc _ _ _)
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, _, tailRecords, _, tailScope, _, waitingHints, _, waitingForest, annotation, selected,
          .live known actionKnown inputAnnotation answerAnnotation scopeKnown held historicalNext savedInterface saved resume close bound, outside,
          rfl, HEq.rfl, HEq.rfl, sameDemand, ?_, ?_, ?_⟩
        · simp only [sameRecords, List.cons_append, List.append_assoc]
        · intro operation
          rw [SourceDependencyCapture.select, selection operation, SourceDependencyCapture.chosen_prepend]
        · intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
            spendAll, merge_assoc]
  | spent owner answerType caller rest cap tail handler next ih => cases source with
    | spent known answerAnnotation scopeKnown rest bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope, savedHints, waitingHints, savedForest, waitingForest,
          annotation, selected, saved, outside, sameScope, sameHints, sameForest, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        cases sameScope
        cases sameHints
        cases sameForest
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, capRecords, tailRecords, _, tailScope, _, waitingHints, _, waitingForest, annotation, selected,
          .spent known answerAnnotation scopeKnown saved bound, outside, rfl, HEq.rfl, HEq.rfl, sameDemand, sameRecords, ?_, ?_⟩
        · intro operation
          rw [SourceDependencyCapture.select, selection operation, SourceDependencyCapture.chosen_prepend]
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
          spendAll, merge_assoc]

end Ash.OneShot.SourceScheduledCuts

#print axioms Ash.OneShot.SourceScheduledCuts.capture_segments
