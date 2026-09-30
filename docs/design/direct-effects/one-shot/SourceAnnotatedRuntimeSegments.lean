import SourceAnnotatedRuntimeResources

/-! Splitting and recomposition retain actual annotated frames, dormant saved
segments and their source plans. Existing forest equations and requirement
reassociation supply the accounting; invocation rules supply rechecking. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeTyping

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledRecomposition (forest_append_assoc)
open SourcePlannedFrames (DependencyScope)
open RecursiveRequirements (Requirements Store evaluate)
open ProtectionResiduals (merge merge_assoc)
open OwnerPhaseTransitions (spendAll)
open SourceDependencyChecks (scope_append_assoc)
open SourcePlannedRecomposition (hints_append_assoc)

variable {front tail : SourceAnnotatedRuntime.Stack}

theorem Frame.receiving_congr {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints) (sameForest : HEq first second)
    (source : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      first entry input output demand requirements layer decorate decoratePlans incoming outgoing) :
    Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      second entry input output demand requirements layer decorate decoratePlans incoming outgoing := by
  cases sameScope
  cases sameHints
  cases sameForest
  exact source

theorem Frame.decorate_append
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    (first : Forest firstHints) (second : Forest secondHints) :
    HEq (decoratePlans (first.append second)) ((decoratePlans first).append second) := by
  cases frame <;> rfl

theorem Segment.receiving_congr {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints) (sameForest : HEq first second)
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints first incoming outgoing) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints second incoming outgoing := by
  cases sameScope
  cases sameHints
  cases sameForest
  exact source

theorem Segment.forest_congr {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints) (sameForest : HEq first second)
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records first outside incoming outgoing) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records second outside incoming outgoing := by
  cases sameScope
  cases sameHints
  cases sameForest
  exact source

/-- Concatenating checked segments keeps each original source plan and local
check together, including inside dormant continuations. The receiving suffix
is explicit, so this rule cannot silently reinterpret a pending computation. -/
theorem segment_append [SourceScheduledChecks.DeclarationProjection admission certification] {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {receivingHints : Hints receivingScope} {outsideHints : Hints outsideScope}
    {firstForest : Forest firstHints} {secondForest : Forest secondHints}
    {receivingForest : Forest receivingHints} {outside : Forest outsideHints}
    (first : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world front input middle
      firstDemand firstRequirements firstRecords firstForest receivingForest incoming boundary)
    (second : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world tail middle output
      secondDemand secondRequirements secondRecords secondForest outside boundary outgoing)
    (receivingScopeSame : receivingScope = secondScope.append outsideScope)
    (receivingSame : HEq receivingHints (secondHints.append outsideHints))
    (receivingPlansSame : HEq receivingForest (secondForest.append outside)) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) (firstForest.append secondForest) outside incoming outgoing ∧
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
      have matched := rebuilt.forest_congr head.erase.source.source.erase.realizes.append.symm (head.erase.source.decorate_append _ _) (head.decorate_append _ _)
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

end Ash.OneShot.SourceAnnotatedRuntimeTyping

namespace Ash.OneShot.SourceAnnotatedRuntimeTyping

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Pending)

/-- The frame's actual retained plan determines its new local check. -/
theorem Frame.recheck {oldHints : Hints oldScope} {receiving : Forest oldHints}
    {restHints : Hints restScope} {rest : Forest restHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions before world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    (checked : Pending nextOutward actions after world (decoratePlans rest) outside) :
    Frame (evidence := evidence) operations policy contracts tables families required nextOutward actions after world
      (rest.append outside) entry input output demand requirements layer decorate decoratePlans incoming outgoing ∧
    Pending nextOutward actions after world rest outside := by
  cases frame with
  | plain context hint closed scope inputAnnotation outputAnnotation old => cases checked with
    | plain current tail => exact ⟨.plain context hint closed scope inputAnnotation outputAnnotation current, tail⟩
  | handler scope annotation clauses coverage unique declarations recipes oldSupplied capabilities modes => cases checked with
    | handler supplied tail => exact ⟨.handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes, tail⟩
  | cell scope noEscape annotation interface => cases checked with
    | cell tail => exact ⟨.cell scope noEscape annotation interface, tail⟩
  | armed scope callback annotation interface old => cases checked with
    | cleanup current tail => exact ⟨.armed scope callback annotation interface current, tail⟩
  | running scope callback saved annotation interface => cases checked with
    | running tail => exact ⟨.running scope callback saved annotation interface, tail⟩
  | closing scope interface => cases checked with
    | running tail => exact ⟨.closing scope interface, tail⟩
  | retiring known interface => cases checked with
    | running tail => exact ⟨.retiring known interface, tail⟩

/-- Structural scheduling under the new suffix is sufficient to retain every
source witness, requirement and stored continuation template. -/
theorem Segment.recheck {hints : Hints scope} {forest : Forest hints}
    {oldHints : Hints oldScope} {oldOutside : Forest oldHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward before world
      stack input output demand requirements records forest oldOutside incoming outgoing)
    (checked : Pending nextOutward actions after world forest outside) :
    Segment (evidence := evidence) operations policy contracts tables families required actions nextOutward after world
      stack input output demand requirements records forest outside incoming outgoing := by
  induction source generalizing outsideScope with
  | nil bound => exact .nil bound
  | push head tail bound ih =>
      obtain ⟨headNext, tailCheck⟩ := head.recheck checked
      exact .push headNext (ih tailCheck) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      cases checked with
      | live inside outside =>
        exact .live known actionKnown inputAnnotation answerAnnotation scope held (ihSaved inside) savedBound
          (ihTail outside) resume close bound
  | spent known annotation scope tail bound ih => cases checked with
    | spent outside => exact .spent known annotation scope (ih outside) bound

/-- Widen the external effect interface without changing retained plans. -/
theorem Segment.output_weaken
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing)
    (larger : outgoing ⊆ nextOutgoing) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming nextOutgoing := by
  induction source with
  | nil bound => exact .nil (List.Subset.trans bound larger)
  | push head tail bound ih => exact .push head (ih larger) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound (ihTail larger) resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope (ih larger) bound

end Ash.OneShot.SourceAnnotatedRuntimeTyping
namespace Ash.OneShot.SourceAnnotatedRuntimeTyping

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
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

variable {front tail : SourceAnnotatedRuntime.Stack}

theorem segment_split [SourceScheduledChecks.DeclarationProjection admission certification] {hints : Hints wholeScope} {outsideHints : Hints outsideScope}
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
        head.erase.source.source.erase.realizes.append.symm, head.erase.source.decorate_append _ _, head.decorate_append _ _,
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

end Ash.OneShot.SourceAnnotatedRuntimeTyping

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Frame.receiving_congr

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Frame.decorate_append

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Segment.receiving_congr

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Segment.forest_congr

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.segment_append

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Frame.recheck

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Segment.recheck

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Segment.output_weaken

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.segment_split
