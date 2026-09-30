import DeclaredConnectedCleanup

/-! Reattach structural source/effect segments without choosing new stored
annotations. The two structural inductions follow the existing annotated
append and live-boundary replacement proofs. Evaluation, record permutation
and consumed-phase transport use the established lemmas.
-/
namespace Ash.OneShot.DeclaredConnectedSources
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open RecursiveRequirements (Requirements Store Checked evaluate)
open OwnerPhaseTransitions (Phases spend spendAll)
open RecursiveRecomposition (evaluate_empty evaluate_spent merge_empty_left normalize_replaced move_records)

variable {front capture tail : Stack}

theorem segment_append
    (first : Segment operations policy contracts tables actions world front input middle
      firstDemand firstRequirements firstRecords incoming boundary)
    (second : Segment operations policy contracts tables actions world tail middle output
      secondDemand secondRequirements secondRecords boundary outgoing) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      Segment operations policy contracts tables actions world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) incoming outgoing ∧
      ∀ store receiving phases,
        evaluate store receiving phases combined =
          merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases firstRequirements)
            (evaluate store receiving (spendAll phases firstDemand) secondRequirements) := by
  induction first generalizing output secondDemand secondRequirements secondRecords tail outgoing with
  | nil bound =>
      refine ⟨secondRequirements, second.input_weaken bound, ?_⟩
      intro store receiving phases
      simp only [evaluate_empty, spendAll, merge_empty_left]
  | push head rest bound ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      rw [List.append_assoc]
      refine ⟨_, .push head source bound, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        OwnerPhases.stack_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, merge_assoc]
  | @live owner contract rights inputType answerType caller capture body nested restStack result demand requirements remaining
      boundary outgoing incoming known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface rest resume close bound ihSaved ihRest =>
      obtain ⟨combined, source, evaluation⟩ := ihRest second
      refine ⟨@Requirements.sequence [] (demand ++ secondDemand) (.spent owner) combined, ?_, ?_⟩
      · simpa only [List.cons_append, List.append_assoc, Stack.append] using
          Segment.live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface source resume close bound
      · intro store receiving phases
        simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]
  | spent known annotation scope rest bound ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      refine ⟨_, .spent known annotation scope source bound, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]

theorem segment_append_checked
    (first : Segment operations policy contracts tables actions world front input middle
      firstDemand firstRequirements firstRecords incoming boundary)
    (second : Segment operations policy contracts tables actions world tail middle output
      secondDemand secondRequirements secondRecords boundary outgoing)
    (firstChecked : Checked store (OwnerPhases.ofStack tables tail ++ receiving) before firstRequirements firstRow)
    (secondChecked : Checked store receiving (spendAll before firstDemand) secondRequirements secondRow) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      Segment operations policy contracts tables actions world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) incoming outgoing ∧
      Checked store receiving before combined (firstRow ++ secondRow) := by
  obtain ⟨combined, source, evaluation⟩ := segment_append first second
  refine ⟨combined, source, RecursiveRequirements.evaluate_sound ?_⟩
  rw [evaluation, RecursiveRequirements.checked_complete firstChecked, RecursiveRequirements.checked_complete secondChecked]
  rfl

/-- The independently checked action selects the saved structural derivation.
Other live captures keep their own conditional interfaces unchanged. -/
theorem replace_live
    (source : Segment operations policy contracts tables actions world
      (front.append (.live owner inputType answerType capture caller tail)) input output demand requirements records incoming outgoing)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true) :
    ∃ (capturedRequirements : Requirements contract.resumeDemand) (capturedRecords : Store)
      (waitingRequirements : Requirements demand) (waitingRecords : Store),
      Segment operations policy contracts tables actions world capture contract.input contract.answer
        contract.resumeDemand capturedRequirements capturedRecords [] contract.resumeEffects ∧
      Segment operations policy contracts tables actions world (front.append (.spent owner answerType caller tail)) input output
        demand waitingRequirements waitingRecords incoming outgoing ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (capturedRecords ++ waitingRecords)) ∧
      ∀ store receiving phases, phases owner = .consumed →
        evaluate store receiving phases waitingRequirements = evaluate store receiving phases requirements := by
  induction front generalizing input demand requirements records incoming with
  | nil => cases source with
      | live actual actualAction inputAnnotation answerAnnotation scope held saved savedInterface rest resume close bound =>
          have same := Option.some.inj (actual.symm.trans known)
          have sameRights := Option.some.inj (actualAction.symm.trans actionKnown)
          cases same
          cases sameRights
          refine ⟨_, _, _, _, savedInterface permitted, .spent known answerAnnotation scope rest bound, .refl _, ?_⟩
          intros; rfl
  | push frame front ih => cases source with
      | @push entry input middle headDemand headReq inner outer restStack output tailDemand tailReq records outgoing incoming head rest bound =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, evaluation⟩ := ih rest
          refine ⟨capturedReq, capturedRecords, _, waitingRecords, saved, .push head waiting bound, permutation, ?_⟩
          intro store receiving phases consumed
          rw [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence,
            RecursiveRequirements.evaluate_prepend, RecursiveRequirements.evaluate_prepend]
          have headSame := RecursiveTransport.evaluate_transport (requirements := headReq) (store := store) (nextStore := store)
            (fun _ _ => rfl) (normalize_replaced (front := front) (capture := capture) (tail := tail)
              (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := receiving) consumed)
          rw [← headSame, evaluation store receiving _ (RecursiveTransport.phases_spendAll_later owner consumed)]
  | live other otherInput otherAnswer savedFront savedScope front ihSaved ihFront => cases source with
      | @live other otherContract rights otherInput otherAnswer savedScope savedFront body nested restStack output demand requirements remaining
          boundary outgoing incoming actual actualAction inputAnnotation answerAnnotation scope held savedOther savedInterface rest resume close bound =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, evaluation⟩ := ihFront rest
          have rebuilt := Segment.live actual actualAction inputAnnotation answerAnnotation scope held savedOther savedInterface waiting resume close bound
          refine ⟨capturedReq, capturedRecords, _, _, saved, rebuilt, ?_, ?_⟩
          · simpa only [List.cons_append, List.append_assoc] using
              move_records (prefixRecords := (⟨other, .resume⟩, ⟨otherContract.resumeDemand, body⟩) :: nested) permutation
          · intro store receiving phases consumed
            simp only [RecursiveRequirements.evaluate_sequence, spendAll, evaluation store receiving phases consumed, evaluate_spent]
  | spent other answer savedScope front ih => cases source with
      | spent actual annotation scope rest bound =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, evaluation⟩ := ih rest
          refine ⟨capturedReq, capturedRecords, _, waitingRecords, saved, .spent actual annotation scope waiting bound, permutation, ?_⟩
          intro store receiving phases consumed
          simp only [RecursiveRequirements.evaluate_sequence, spendAll, evaluation store receiving phases consumed, evaluate_spent]

end Ash.OneShot.DeclaredConnectedSources

#print axioms Ash.OneShot.DeclaredConnectedSources.segment_append
#print axioms Ash.OneShot.DeclaredConnectedSources.segment_append_checked
#print axioms Ash.OneShot.DeclaredConnectedSources.replace_live
