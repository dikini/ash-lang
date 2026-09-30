import DeclaredConnectedCells

/-! A handler cut preserves the actual shared source/effect annotations on
both segments. The selected declaration therefore uses the same residual as
the captured segment and caller. Evaluation splitting reuses the established
recursive capture equations.
-/
namespace Ash.OneShot.DeclaredConnectedSources
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open RecursiveRequirements (Requirements Store Checked evaluate)
open OwnerPhaseTransitions (spendAll)

theorem capture_segments
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables actions world whole input output demand requirements records incoming outgoing) :
    ∃ (answer : Value) (residual : List Instance) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store),
      answer.port = ScopedPorts.eraseType handler.answer ∧ Frame operations policy contracts tables world (.handler handler) answer answer [] (.request [] [])
        (handler.effectInst :: residual) residual ∧
      Segment operations policy contracts tables actions world capture input answer capturedDemand capturedRequirements capturedRecords incoming residual ∧
      Segment operations policy contracts tables actions world tail answer output tailDemand tailRequirements tailRecords residual outgoing ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements)
          (evaluate store receiving (spendAll before capturedDemand) tailRequirements) := by
  induction cut generalizing input demand requirements records incoming with
  | hit handler tail same => cases source with
    | push current rest bound => cases current with
      | retained kind source interface => cases kind
      | handler scope annotation clauses coverage unique declarations capabilities modes =>
          have frame := Frame.handler scope annotation clauses coverage unique declarations capabilities modes
          refine ⟨_, _, [], _, _, _, [], _, annotation, frame,
            .push frame (.nil (List.Subset.refl _)) bound, rest, rfl, rfl, ?_⟩
          intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | push entry rest cap tail handler miss next ih => cases source with
    | push current rest bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
          annotation, selected, saved, outside, sameDemand, sameRecords, evaluation⟩ := ih rest
        refine ⟨answer, residual, _, tailDemand, _, tailReq, capRecords, tailRecords, annotation, selected, .push current saved bound, outside,
          by simp only [sameDemand, List.append_assoc], sameRecords, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
          handler_cut_reconstructs next, OwnerPhases.stack_append, List.append_assoc,
          PhaseRechecking.spendAll_append, merge_assoc]
  | live owner inputType answerType savedScope caller rest cap tail handler next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scopeKnown held historical savedInterface rest resume close bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
          annotation, selected, saved, outside, sameDemand, sameRecords, evaluation⟩ := ih rest
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, _, tailRecords, annotation, selected,
          .live known actionKnown inputAnnotation answerAnnotation scopeKnown held historical savedInterface saved resume close bound, outside,
          sameDemand, ?_, ?_⟩
        · simp only [sameRecords, List.cons_append, List.append_assoc]
        · intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
            spendAll, merge_assoc]
  | spent owner answerType caller rest cap tail handler next ih => cases source with
    | spent known answerAnnotation scopeKnown rest bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
          annotation, selected, saved, outside, sameDemand, sameRecords, evaluation⟩ := ih rest
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, capRecords, tailRecords, annotation, selected,
          .spent known answerAnnotation scopeKnown saved bound, outside, sameDemand, sameRecords, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
          spendAll, merge_assoc]

theorem capture_segments_checked
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables actions world whole input output demand requirements records incoming outgoing)
    (checked : Checked store receiving before requirements row) :
    ∃ (answer : Value) (residual : List Instance) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedRow tailRow : Footprint),
      answer.port = ScopedPorts.eraseType handler.answer ∧ Frame operations policy contracts tables world (.handler handler) answer answer [] (.request [] [])
        (handler.effectInst :: residual) residual ∧
      Segment operations policy contracts tables actions world capture input answer capturedDemand capturedRequirements capturedRecords incoming residual ∧
      Segment operations policy contracts tables actions world tail answer output tailDemand tailRequirements tailRecords residual outgoing ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧ row = capturedRow ++ tailRow ∧
      Checked store (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements capturedRow ∧
      Checked store receiving (spendAll before capturedDemand) tailRequirements tailRow := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
    annotation, selected, saved, outside, sameDemand, sameRecords, evaluation⟩ := capture_segments cut source
  have original := RecursiveRequirements.checked_complete checked
  rw [evaluation] at original
  obtain ⟨capturedRow, tailRow, inside, rest, sameRow⟩ := PhaseRechecking.merge_split original
  exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capturedRow, tailRow,
    annotation, selected, saved, outside, sameDemand, sameRecords, sameRow,
    RecursiveRequirements.evaluate_sound inside, RecursiveRequirements.evaluate_sound rest⟩

/-- Exact clause selection retains the source rule's two independent
interface equations at the installed handler's residual. -/
theorem Frame.selected_body {handler : HandlerData}
    (frame : Frame operations policy contracts tables world (.handler handler) answer answer [] (.request [] [])
      (handler.effectInst :: residual) residual)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row held = some row) :
    ∃ argument input resumeEffects closeEffects,
      operations handler.effectInst operation = some (argument, input) ∧
      (body.requiredActions.resume = true → resumeEffects = residual) ∧
      (body.requiredActions.dispose = true → closeEffects = residual) ∧
      ∀ owner (contract : Owners.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        DeclaredSources.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          (Environment.empty.extend parameter argument) body answer ⟨owner, contract, offered.dispose, row⟩ := by
  cases frame with
  | retained kind source interface => cases kind
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      exact DeclaredSources.selected_body declarations selected found available

/-- Derive capture/caller interface compatibility from the current structural
source and the selected source declaration. No post-allocation typing or
successful-execution premise is supplied. Closing-plan routing is separate. -/
theorem capture_interfaces
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables actions world whole input output demand requirements records incoming outgoing)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row held = some row)
    (operationKnown : operations requested operation = some (argument, input)) :
    ∃ (answer : Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : Requirements capDemand) (tailReq : Requirements tailDemand)
      (capRecords tailRecords : Store) (resumeEffects closeEffects : List Instance),
      answer.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.ports handler.scope ∧
      DeclaredSourceFrames.Segment operations policy contracts tables world capture input answer capDemand capReq capRecords ∧
      (body.requiredActions.resume = true → Segment operations policy contracts tables actions world
        capture input answer capDemand capReq capRecords [] resumeEffects) ∧
      Segment operations policy contracts tables actions world tail answer output tailDemand tailReq tailRecords residual outgoing ∧
      (body.requiredActions.resume = true → resumeEffects ⊆ residual) ∧
      (body.requiredActions.dispose = true → closeEffects ⊆ residual) ∧
      (∀ owner (contract : Owners.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        DeclaredSources.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          (Environment.empty.extend parameter argument) body answer ⟨owner, contract, offered.dispose, row⟩) ∧
      demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capReq)
          (evaluate store receiving (spendAll before capDemand) tailReq) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
    annotation, frame, saved, outside, sameDemand, sameRecords, evaluation⟩ := capture_segments cut source
  obtain ⟨actualArgument, actualInput, resumeEffects, closeEffects, known, resumeInterface, closeInterface, family⟩ :=
    frame.selected_body selected found available
  have scope : ScopedPorts.EffectScopeKnown contracts.ports handler.scope := by
    cases frame with
    | retained kind source interface => cases kind
    | handler scope annotation clauses coverage unique declarations capabilities modes => exact scope
  rw [ScopedTyping.handler_cut_instance cut] at known
  rcases Prod.mk.inj (Option.some.inj (known.symm.trans operationKnown)) with ⟨rfl, rfl⟩
  refine ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, resumeEffects, closeEffects,
    annotation, scope, saved.source, ?_, outside, ?_, ?_, family, sameDemand, sameRecords, evaluation⟩
  · intro used
    rw [resumeInterface used]
    exact saved.input_weaken (List.nil_subset _)
  · intro used
    simpa only [resumeInterface used] using List.Subset.refl residual
  · intro used
    simpa only [closeInterface used] using List.Subset.refl residual

end Ash.OneShot.DeclaredConnectedSources

#print axioms Ash.OneShot.DeclaredConnectedSources.capture_segments
#print axioms Ash.OneShot.DeclaredConnectedSources.capture_segments_checked

#print axioms Ash.OneShot.DeclaredConnectedSources.Frame.selected_body
#print axioms Ash.OneShot.DeclaredConnectedSources.capture_interfaces
