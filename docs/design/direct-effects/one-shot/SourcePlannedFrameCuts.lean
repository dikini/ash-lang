import SourcePlannedFrames

/-! Split synchronized retained source at the actual handler cut. Source
requirements and owner records use the established capture equations. Matching
runtime annotations identify the same saved and waiting hints. -/
namespace Ash.OneShot.SourcePlannedFrameCuts
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value)
open SourcePlannedFrames (Frame Segment DependencyScope)
open SourceContextualHints (Hints)
open RecursiveRequirements (Requirements Store evaluate)
open ProtectionResiduals (merge merge_assoc)
open OwnerPhaseTransitions (spendAll)

theorem capture_segments {hints : Hints wholeScope}
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables families required actions world whole input output demand requirements records hints incoming outgoing) :
    ∃ (answer : Value) (residual : List Instance) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedScope tailScope : DependencyScope),
      ∃ (savedHints : Hints capturedScope) (waitingHints : Hints tailScope),
      answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧ SourcePlannedFrames.Frame operations policy contracts tables families required world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler))
        (fun rest => .handler (required handler) rest) (handler.effectInst :: residual) residual ∧
      Segment operations policy contracts tables families required actions world capture input answer capturedDemand capturedRequirements capturedRecords savedHints incoming residual ∧
      Segment operations policy contracts tables families required actions world tail answer output tailDemand tailRequirements tailRecords waitingHints residual outgoing ∧
      wholeScope = capturedScope.append tailScope ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧
      (∀ operation, SourceDependencyCapture.select requested operation wholeScope =
        SourceDependencyCapture.chosen operation (tables handler) (families handler) capturedScope tailScope) ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements)
          (evaluate store receiving (spendAll before capturedDemand) tailRequirements) := by
  induction cut generalizing input demand requirements records wholeScope incoming with
  | hit handler tail same => cases source with
    | push current rest bound => cases current with
      | handler scope annotation clauses coverage unique declarations recipes capabilities modes =>
          have frame := SourcePlannedFrames.Frame.handler (evidence := SourcePlannedFrames.recipeEvidence) scope annotation clauses coverage unique declarations recipes capabilities modes
          refine ⟨_, _, [], _, _, _, [], _, _, _, _, _, annotation, frame,
            .push frame (.nil (List.Subset.refl _)) bound, rest, rfl, rfl, rfl, ?_, ?_⟩
          · intro operation
            simp only [SourceDependencyCapture.select, if_pos same.symm, SourceDependencyCapture.chosen]
            rfl
          intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | push entry rest cap tail handler miss next ih => cases source with
    | push current rest bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope, savedHints, waitingHints,
          annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        refine ⟨answer, residual, _, tailDemand, _, tailReq, capRecords, tailRecords, _, tailScope, _, waitingHints, annotation, selected, .push current saved bound, outside,
          by rw [current.erase.realizes.append, ← sameScope],
          by simp only [sameDemand, List.append_assoc], sameRecords, ?_, ?_⟩
        · intro operation
          rw [current.erase.realizes.select_miss miss, selection operation, SourceDependencyCapture.chosen_prepend]
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
          handler_cut_reconstructs next, OwnerPhases.stack_append, List.append_assoc,
          PhaseRechecking.spendAll_append, merge_assoc]
  | live owner inputType answerType savedScope caller rest cap tail handler next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scopeKnown held historical savedInterface rest resume close bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope, savedHints, waitingHints,
          annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, _, tailRecords, _, tailScope, _, waitingHints, annotation, selected,
          .live known actionKnown inputAnnotation answerAnnotation scopeKnown held historical savedInterface saved resume close bound, outside,
          by simp only [SourceDependencyCapture.Scope.append, ← sameScope], sameDemand, ?_, ?_, ?_⟩
        · simp only [sameRecords, List.cons_append, List.append_assoc]
        · intro operation
          rw [SourceDependencyCapture.select, selection operation, SourceDependencyCapture.chosen_prepend]
        · intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
            spendAll, merge_assoc]
  | spent owner answerType caller rest cap tail handler next ih => cases source with
    | spent known answerAnnotation scopeKnown rest bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope, savedHints, waitingHints,
          annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, capRecords, tailRecords, _, tailScope, _, waitingHints, annotation, selected,
          .spent known answerAnnotation scopeKnown saved bound, outside, by simp only [SourceDependencyCapture.Scope.append, ← sameScope], sameDemand, sameRecords, ?_, ?_⟩
        · intro operation
          rw [SourceDependencyCapture.select, selection operation, SourceDependencyCapture.chosen_prepend]
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
          spendAll, merge_assoc]

end Ash.OneShot.SourcePlannedFrameCuts

#print axioms Ash.OneShot.SourcePlannedFrameCuts.capture_segments
