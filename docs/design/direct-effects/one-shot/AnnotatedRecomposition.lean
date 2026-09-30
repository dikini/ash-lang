import RecursiveCapture

/-! Recomposition retaining an arbitrary indexed frame predicate. The cases
are the existing RecursiveRecomposition constructors; evaluation transport,
normalization and record permutation reuse the established lemmas. -/
namespace Ash.OneShot.AnnotatedRecomposition
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open RecursiveCapture (AnnotatedSegment)
open RecursiveRequirements (Requirements Store Key Checked evaluate)
open OwnerPhaseTransitions (Phases spend spendAll)
open RecursiveRecomposition (evaluate_empty evaluate_spent merge_empty_left merge_empty_right move_records normalize_replaced)
variable {before phases : Phases} {front capture tail : Stack}

theorem segment_append
    (first : AnnotatedSegment predicate operations policy contracts tables world front input middle firstDemand firstRequirements firstRecords)
    (second : AnnotatedSegment predicate operations policy contracts tables world tail middle output secondDemand secondRequirements secondRecords) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      AnnotatedSegment predicate operations policy contracts tables world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) ∧
      ∀ store receiving phases,
        evaluate store receiving phases combined =
          merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases firstRequirements)
            (evaluate store receiving (spendAll phases firstDemand) secondRequirements) := by
  induction first generalizing output secondDemand secondRequirements secondRecords tail with
  | nil =>
      refine ⟨secondRequirements, second, ?_⟩
      intro store receiving phases
      simp only [evaluate_empty, spendAll, merge_empty_left]
  | push current head rest ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      rw [List.append_assoc]
      refine ⟨_, .push current head source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        OwnerPhases.stack_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, merge_assoc]
  | @live owner contract inputType answerType caller capture body nested rest middle demand requirements remaining
      known inputAnnotation answerAnnotation scopeKnown held saved restSource ihSaved ihRest =>
      obtain ⟨combined, source, evaluation⟩ := ihRest second
      refine ⟨@Requirements.sequence [] (demand ++ secondDemand) (.spent owner) combined, ?_, ?_⟩
      · simpa only [List.cons_append, List.append_assoc, Stack.append] using AnnotatedSegment.live known inputAnnotation answerAnnotation scopeKnown held saved source
      · intro store receiving phases
        simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]
  | spent known answerAnnotation scopeKnown rest ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      refine ⟨_, .spent known answerAnnotation scopeKnown source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]

theorem segment_append_checked
    (first : AnnotatedSegment predicate operations policy contracts tables world front input middle firstDemand firstRequirements firstRecords)
    (second : AnnotatedSegment predicate operations policy contracts tables world tail middle output secondDemand secondRequirements secondRecords)
    (firstChecked : Checked store (OwnerPhases.ofStack tables tail ++ receiving) before firstRequirements firstRow)
    (secondChecked : Checked store receiving (spendAll before firstDemand) secondRequirements secondRow) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      AnnotatedSegment predicate operations policy contracts tables world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) ∧
      Checked store receiving before combined (firstRow ++ secondRow) := by
  obtain ⟨combined, source, evaluation⟩ := segment_append first second
  refine ⟨combined, source, RecursiveRequirements.evaluate_sound ?_⟩
  rw [evaluation, RecursiveRequirements.checked_complete firstChecked, RecursiveRequirements.checked_complete secondChecked]
  rfl

theorem replace_live
    (source : AnnotatedSegment predicate operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) input output demand requirements records)
    (known : contracts owner = some contract) :
    ∃ (capturedRequirements : Requirements contract.resumeDemand) (capturedRecords : Store)
      (waitingRequirements : Requirements demand) (waitingRecords : Store),
      AnnotatedSegment predicate operations policy contracts tables world capture contract.input contract.answer
        contract.resumeDemand capturedRequirements capturedRecords ∧
      AnnotatedSegment predicate operations policy contracts tables world (front.append (.spent owner answerType caller tail)) input output
        demand waitingRequirements waitingRecords ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (capturedRecords ++ waitingRecords)) ∧
      ∀ store receiving phases, phases owner = .consumed →
        evaluate store receiving phases waitingRequirements = evaluate store receiving phases requirements := by
  induction front generalizing input demand requirements records with
  | nil => cases source with
      | live actual inputAnnotation answerAnnotation scopeKnown held saved rest =>
          have same := Option.some.inj (actual.symm.trans known)
          cases same
          refine ⟨_, _, _, _, saved, .spent known answerAnnotation scopeKnown rest, .refl _, ?_⟩
          intros; rfl
  | push frame front ih => cases source with
      | push current head rest =>
          rename_i middle headDemand headReq tailDemand tailReq
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, evaluation⟩ := ih rest
          refine ⟨capturedReq, capturedRecords, _, waitingRecords, saved, .push current head waiting, permutation, ?_⟩
          intro store receiving phases consumed
          rw [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence,
            RecursiveRequirements.evaluate_prepend, RecursiveRequirements.evaluate_prepend]
          have headSame := RecursiveTransport.evaluate_transport (requirements := headReq) (store := store) (nextStore := store)
            (fun _ _ => rfl) (normalize_replaced (front := front) (capture := capture) (tail := tail)
              (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := receiving) consumed)
          rw [← headSame, evaluation store receiving _ (RecursiveTransport.phases_spendAll_later owner consumed)]
  | live other otherInput otherAnswer savedFront savedScope front ihSaved ihFront => cases source with
      | @live other otherContract otherInput otherAnswer savedScope savedFront body nested restStack output demand requirements remaining
          actual inputAnnotation answerAnnotation scopeKnown held savedOther rest =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, evaluation⟩ := ihFront rest
          have rebuilt := AnnotatedSegment.live actual inputAnnotation answerAnnotation scopeKnown held savedOther waiting
          refine ⟨capturedReq, capturedRecords, _, _, saved, rebuilt, ?_, ?_⟩
          · simpa only [List.cons_append, List.append_assoc] using
              move_records (prefixRecords := (⟨other, .resume⟩, ⟨otherContract.resumeDemand, body⟩) :: nested) permutation
          · intro store receiving phases consumed
            simp only [RecursiveRequirements.evaluate_sequence, spendAll, evaluation store receiving phases consumed, evaluate_spent]
  | spent other answer savedScope front ih => cases source with
      | spent actual answerAnnotation scopeKnown rest =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, evaluation⟩ := ih rest
          refine ⟨capturedReq, capturedRecords, _, waitingRecords, saved, .spent actual answerAnnotation scopeKnown waiting, permutation, ?_⟩
          intro store receiving phases consumed
          simp only [RecursiveRequirements.evaluate_sequence, spendAll, evaluation store receiving phases consumed, evaluate_spent]


end Ash.OneShot.AnnotatedRecomposition

#print axioms Ash.OneShot.AnnotatedRecomposition.segment_append
#print axioms Ash.OneShot.AnnotatedRecomposition.segment_append_checked
#print axioms Ash.OneShot.AnnotatedRecomposition.replace_live
