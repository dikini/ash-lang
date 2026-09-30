import SourceAnnotatedStoredTyping

/-! The actual handler cut splits the joint source/packet judgment. The saved
and waiting packets are the original atCut values, and the selected handler's
source is checked at its packet's exact plan and rich interface. -/
namespace Ash.OneShot.SourceConsumingStoredBounds
open SourceAnnotatedRuntime
variable {whole capture tail : Stack}

theorem StackBounds.atCut_hit (head : HandlerBounds families handler) (rest : StackBounds families tail)
    (same : handler.effectInst = requested) :
    (StackBounds.push (.handler head) rest).atCut (.hit handler tail same) =
      (.push (.handler head) .nil, rest) := rfl

theorem StackBounds.atCut_push (head : FrameBounds families frame) (rest : StackBounds families whole)
    (miss : frame.erase.erase.target ≠ some requested) (cut : HandlerCut requested whole capture tail handler) :
    (StackBounds.push head rest).atCut (.push frame whole capture tail handler miss cut) =
      (.push head (rest.atCut cut).1, (rest.atCut cut).2) := by
  cases cut.reconstructs
  rfl

theorem StackBounds.atCut_live (saved : StackBounds families savedStack) (rest : StackBounds families whole)
    (cut : HandlerCut requested whole capture tail handler) :
    (StackBounds.live (owner := owner) (input := input) (answer := answer) (caller := caller) saved rest).atCut
      (.live owner input answer savedStack caller whole capture tail handler cut) =
      (.live saved (rest.atCut cut).1, (rest.atCut cut).2) := by
  cases cut.reconstructs
  rfl

theorem StackBounds.atCut_spent (rest : StackBounds families whole)
    (cut : HandlerCut requested whole capture tail handler) :
    (StackBounds.spent (owner := owner) (answer := answer) (caller := caller) rest).atCut
      (.spent owner answer caller whole capture tail handler cut) =
      (.spent (rest.atCut cut).1, (rest.atCut cut).2) := by
  cases cut.reconstructs
  rfl

end Ash.OneShot.SourceConsumingStoredBounds

namespace Ash.OneShot.SourceAnnotatedStoredTyping
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value)
open SourcePlannedFrames (DependencyScope)
open SourceRetainedPlans (Forest)
open SourceScheduledRecomposition (forest_append_assoc)
open SourceDependencyChecks (scope_append_assoc)
open SourcePlannedRecomposition (hints_append_assoc)
open SourceContextualHints (Hints)
open SourceConsumingStoredBounds (FrameBounds HandlerBounds StackBounds)
open RecursiveRequirements (Requirements Store evaluate)
open ProtectionResiduals (merge merge_assoc)
open OwnerPhaseTransitions (spendAll)

theorem capture_segments {hints : Hints wholeScope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world whole input output demand requirements records forest outside incoming outgoing stored) :
    ∃ (answer : Value) (residual : List Instance) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedScope tailScope : DependencyScope),
      ∃ (savedHints : Hints capturedScope) (waitingHints : Hints tailScope),
      ∃ (savedForest : Forest savedHints) (waitingForest : Forest waitingHints),
      ∃ packet : HandlerBounds families handler,
      stored.handlerAt requested = some ⟨handler, packet⟩ ∧
      answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧ Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world (waitingForest.append outside) (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler.erase) (families handler.erase))
        (fun rest => .handler (required handler.erase) rest) (fun rest => .handler rest) (handler.effectInst :: residual) residual (.handler packet) ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world capture input answer capturedDemand capturedRequirements capturedRecords savedForest (waitingForest.append outside) incoming residual (stored.atCut cut).1 ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world tail answer output tailDemand tailRequirements tailRecords waitingForest outside residual outgoing (stored.atCut cut).2 ∧
      wholeScope = capturedScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ HEq forest (savedForest.append waitingForest) ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧
      (∀ operation, SourceDependencyCapture.select requested operation wholeScope =
        SourceDependencyCapture.chosen operation (tables handler.erase) (families handler.erase) capturedScope tailScope) ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail.erase ++ receiving) before capturedRequirements)
          (evaluate store receiving (spendAll before capturedDemand) tailRequirements) := by
  induction cut generalizing input demand requirements records wholeScope incoming with
  | hit handler tail same => cases source with
    | push current rest bound =>
      have retainedFrame := current
      rcases current with ⟨frame, packetSource⟩
      cases frame with
      | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes =>
          cases packetSource with
          | handler exactSource exactEvidence =>
            rename_i packet
            refine ⟨_, _, [], _, .sequence ((Requirements.request [] []).prepend []) (.request [] []), _, [], _, _, _, _, _, .handler (required := required handler.erase) .nil, _, packet, by simp only [StackBounds.handlerAt, same, if_true], annotation,
              retainedFrame,
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
        rename_i headStored restStored
        rw [StackBounds.atCut_push headStored restStored miss next]
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope, savedHints, waitingHints, savedForest, waitingForest,
          packet, packetAt, annotation, selected, saved, outside, sameScope, sameHints, sameForest, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        cases sameScope
        cases sameHints
        cases sameForest
        have currentNext := current.receiving_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc _ _ _)
        refine ⟨answer, residual, _, tailDemand, _, tailReq, capRecords, tailRecords, _, tailScope, _, waitingHints, _, waitingForest, packet, ?_, annotation, selected, .push currentNext saved bound, outside,
          current.forget.erase.source.source.erase.realizes.append.symm, current.forget.erase.source.decorate_append _ _, current.forget.decorate_append _ _,
          by simp only [sameDemand, List.append_assoc], sameRecords, ?_, ?_⟩
        · cases current.packetSource <;>
            simp_all [StackBounds.handlerAt, SourceAnnotatedRuntime.Frame.erase,
              ScopedExecution.ExecFrame.erase, Ash.OneShot.Frame.target, SourceAnnotatedRuntime.Handler.erase,
              ScopedExecution.HandlerData.erase]
        · intro operation
          rw [current.forget.erase.source.source.erase.realizes.select_miss miss, selection operation, SourceDependencyCapture.chosen_prepend]
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
          next.reconstructs, SourceAnnotatedRuntime.Stack.erase_append, OwnerPhases.stack_append, List.append_assoc,
          PhaseRechecking.spendAll_append, merge_assoc]
  | live owner inputType answerType savedScope caller rest cap tail handler next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scopeKnown held historical savedInterface rest resume close bound =>
        have packetSplit := StackBounds.atCut_live (owner := owner) (input := inputType) (answer := answerType) (caller := caller) historical.packets rest.packets next
        dsimp only [Segment.packets] at packetSplit
        rw [packetSplit]
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope, savedHints, waitingHints, savedForest, waitingForest,
          packet, packetAt, annotation, selected, saved, outside, sameScope, sameHints, sameForest, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        cases sameScope
        cases sameHints
        cases sameForest
        have historicalNext := historical.receiving_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc _ _ _)
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, _, tailRecords, _, tailScope, _, waitingHints, _, waitingForest, packet, ?_, annotation, selected,
          .live known actionKnown inputAnnotation answerAnnotation scopeKnown held historicalNext savedInterface saved resume close bound, outside,
          rfl, HEq.rfl, HEq.rfl, sameDemand, ?_, ?_, ?_⟩
        · exact packetAt
        · simp only [sameRecords, List.cons_append, List.append_assoc]
        · intro operation
          rw [SourceDependencyCapture.select, selection operation, SourceDependencyCapture.chosen_prepend]
        · intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
            spendAll, merge_assoc]
  | spent owner answerType caller rest cap tail handler next ih => cases source with
    | spent known answerAnnotation scopeKnown rest bound =>
        have packetSplit := StackBounds.atCut_spent (owner := owner) (answer := answerType) (caller := caller) rest.packets next
        dsimp only [Segment.packets] at packetSplit
        rw [packetSplit]
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope, savedHints, waitingHints, savedForest, waitingForest,
          packet, packetAt, annotation, selected, saved, outside, sameScope, sameHints, sameForest, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        cases sameScope
        cases sameHints
        cases sameForest
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, capRecords, tailRecords, _, tailScope, _, waitingHints, _, waitingForest, packet, ?_, annotation, selected,
          .spent known answerAnnotation scopeKnown saved bound, outside, rfl, HEq.rfl, HEq.rfl, sameDemand, sameRecords, ?_, ?_⟩
        · exact packetAt
        · intro operation
          rw [SourceDependencyCapture.select, selection operation, SourceDependencyCapture.chosen_prepend]
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
          spendAll, merge_assoc]


/-- Recomposition keeps the same packet append and reuses the original
requirement reassociation and forest equations. -/
theorem segment_append {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {receivingHints : Hints receivingScope} {outsideHints : Hints outsideScope}
    {firstForest : Forest firstHints} {secondForest : Forest secondHints}
    {receivingForest : Forest receivingHints} {outside : Forest outsideHints}
    (first : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world front input middle
      firstDemand firstRequirements firstRecords firstForest receivingForest incoming boundary frontStored)
    (second : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world tail middle output
      secondDemand secondRequirements secondRecords secondForest outside boundary outgoing tailStored)
    (receivingScopeSame : receivingScope = secondScope.append outsideScope)
    (receivingSame : HEq receivingHints (secondHints.append outsideHints))
    (receivingPlansSame : HEq receivingForest (secondForest.append outside)) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) (firstForest.append secondForest) outside incoming outgoing (frontStored.append tailStored) ∧
      ∀ store receiving before,
        evaluate store receiving before combined =
          merge (evaluate store (OwnerPhases.ofStack tables tail.erase ++ receiving) before firstRequirements)
            (evaluate store receiving (spendAll before firstDemand) secondRequirements) := by
  induction first generalizing output secondDemand secondRequirements secondRecords secondScope outsideScope tail outgoing with
  | nil bound =>
      refine ⟨secondRequirements, second.input_weaken bound, ?_⟩
      intro store receiving before
      simp only [RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | push head rest bound ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second receivingScopeSame receivingSame receivingPlansSame
      cases receivingScopeSame
      cases receivingSame
      cases receivingPlansSame
      have headNext := head.receiving_congr (scope_append_assoc _ _ _).symm (hints_append_assoc _ _ _).symm (forest_append_assoc _ _ _).symm
      have rebuilt := Segment.push headNext source bound
      have matched := rebuilt.forest_congr head.forget.erase.source.source.erase.realizes.append.symm (head.forget.erase.source.decorate_append _ _) (head.forget.decorate_append _ _)
      rw [List.append_assoc]
      refine ⟨_, matched, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        SourceAnnotatedRuntime.Stack.erase_append, OwnerPhases.stack_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, merge_assoc]
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface rest resume close bound ihSaved ihRest =>
      obtain ⟨combined, source, evaluation⟩ := ihRest second receivingScopeSame receivingSame receivingPlansSame
      cases receivingScopeSame
      cases receivingSame
      cases receivingPlansSame
      have savedNext := saved.receiving_congr (scope_append_assoc _ _ _).symm (hints_append_assoc _ _ _).symm (forest_append_assoc _ _ _).symm
      have rebuilt := Segment.live known actionKnown inputAnnotation answerAnnotation scope held savedNext savedInterface source resume close bound
      simp only [List.cons_append, List.append_assoc]
      refine ⟨_, rebuilt, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent, evaluation, spendAll, merge_assoc]
  | spent known annotation scope rest bound ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second receivingScopeSame receivingSame receivingPlansSame
      refine ⟨_, .spent known annotation scope source bound, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent, evaluation, spendAll, merge_assoc]


variable {front tail : SourceAnnotatedRuntime.Stack}

theorem segment_split {hints : Hints wholeScope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      (front.append tail) input output demand requirements records forest outside incoming outgoing stored) :
    ∃ (middle : Value) (boundary : List Instance) (firstDemand secondDemand : List Nat)
      (firstRequirements : Requirements firstDemand) (secondRequirements : Requirements secondDemand)
      (firstRecords secondRecords : Store) (firstScope secondScope : DependencyScope),
      ∃ (firstHints : Hints firstScope) (secondHints : Hints secondScope)
        (firstForest : Forest firstHints) (secondForest : Forest secondHints),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        front input middle firstDemand firstRequirements firstRecords firstForest (secondForest.append outside) incoming boundary (stored.splitAt front tail).1 ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        tail middle output secondDemand secondRequirements secondRecords secondForest outside boundary outgoing (stored.splitAt front tail).2 ∧
      wholeScope = firstScope.append secondScope ∧ HEq hints (firstHints.append secondHints) ∧
      HEq forest (firstForest.append secondForest) ∧ demand = firstDemand ++ secondDemand ∧
      records = firstRecords ++ secondRecords ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail.erase ++ receiving) before firstRequirements)
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
        head.forget.erase.source.source.erase.realizes.append.symm, head.forget.erase.source.decorate_append _ _, head.forget.decorate_append _ _,
        by simp only [sameDemand, List.append_assoc], sameRecords, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
        SourceAnnotatedRuntime.Stack.erase_append, OwnerPhases.stack_append, List.append_assoc, PhaseRechecking.spendAll_append, merge_assoc]
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


end Ash.OneShot.SourceAnnotatedStoredTyping

#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.atCut_hit
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.atCut_push
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.atCut_live
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.atCut_spent
#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.capture_segments

#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.segment_append

#print axioms Ash.OneShot.SourceAnnotatedStoredTyping.segment_split
