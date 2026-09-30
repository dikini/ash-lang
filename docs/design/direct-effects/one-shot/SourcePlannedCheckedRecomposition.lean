import SourcePlannedCheckedFrames

/-! Ordered recomposition preserves the joint source/checking witnesses.
Associativity transports use the established equality of annotated scopes;
source requirement evaluation reuses the existing stack and phase equations. -/
namespace Ash.OneShot.SourcePlannedCheckedFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceContextualHints (Hints)
open SourcePlannedFrames (DependencyScope)
open RecursiveRequirements (Requirements Store evaluate)
open ProtectionResiduals (merge merge_assoc)
open OwnerPhaseTransitions (spendAll)
open SourceDependencyChecks (scope_append_assoc)
open SourcePlannedRecomposition (hints_append_assoc)

variable {front tail : Stack}

theorem Frame.receiving_congr {first : Hints firstScope} {second : Hints secondScope}
    (sameScope : firstScope = secondScope) (sameHints : HEq first second)
    (source : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      first entry input output demand requirements layer decorate incoming outgoing) :
    Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      second entry input output demand requirements layer decorate incoming outgoing := by
  cases sameScope
  cases sameHints
  exact source

theorem Frame.decorate_append [certification : SourcePlannedChecks.DeclarationPolicy]
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      receiving entry input output demand requirements layer decorate incoming outgoing)
    (first : Hints firstScope) (second : Hints secondScope) :
    HEq (decorate (first.append second)) ((decorate first).append second) := by
  cases frame <;> rfl

theorem Segment.receiving_congr {first : Hints firstScope} {second : Hints secondScope}
    (sameScope : firstScope = secondScope) (sameHints : HEq first second)
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints first incoming outgoing) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints second incoming outgoing := by
  cases sameScope
  cases sameHints
  exact source

theorem Segment.hints_congr {first : Hints firstScope} {second : Hints secondScope}
    (sameScope : firstScope = secondScope) (sameHints : HEq first second)
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records first outside incoming outgoing) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records second outside incoming outgoing := by
  cases sameScope
  cases sameHints
  exact source

theorem Segment.input_weaken [certification : SourcePlannedChecks.DeclarationPolicy]
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints outside incoming outgoing)
    (smaller : nextIncoming ⊆ incoming) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints outside nextIncoming outgoing := by
  cases source with
  | nil bound => exact .nil (List.Subset.trans smaller bound)
  | push head tail bound => exact .push head tail (List.Subset.trans smaller bound)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close
        (List.Subset.trans smaller bound)
  | spent known annotation scope tail bound => exact .spent known annotation scope tail (List.Subset.trans smaller bound)

/-- Concatenating checked segments keeps each original source plan and local
check together, including inside dormant continuations. The receiving suffix
is explicit, so this rule cannot silently reinterpret a pending computation. -/
theorem segment_append {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {receivingHints : Hints receivingScope} {outside : Hints outsideScope}
    (first : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world front input middle
      firstDemand firstRequirements firstRecords firstHints receivingHints incoming boundary)
    (second : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world tail middle output
      secondDemand secondRequirements secondRecords secondHints outside boundary outgoing)
    (receivingScopeSame : receivingScope = secondScope.append outsideScope)
    (receivingSame : HEq receivingHints (secondHints.append outside)) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) (firstHints.append secondHints) outside incoming outgoing ∧
      ∀ store receiving before,
        evaluate store receiving before combined =
          merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before firstRequirements)
            (evaluate store receiving (spendAll before firstDemand) secondRequirements) := by
  induction first generalizing output secondDemand secondRequirements secondRecords secondScope outsideScope tail outgoing with
  | nil bound =>
      refine ⟨secondRequirements, second.input_weaken bound, ?_⟩
      intro store receiving before
      simp only [RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | push head rest bound ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second receivingScopeSame receivingSame
      cases receivingScopeSame
      cases receivingSame
      have headNext := head.receiving_congr (scope_append_assoc _ _ _).symm (hints_append_assoc _ _ _).symm
      have rebuilt := Segment.push headNext source bound
      have matched := rebuilt.hints_congr head.source.erase.realizes.append.symm (head.decorate_append _ _)
      rw [List.append_assoc]
      refine ⟨_, matched, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        OwnerPhases.stack_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, merge_assoc]
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface rest resume close bound ihSaved ihRest =>
      obtain ⟨combined, source, evaluation⟩ := ihRest second receivingScopeSame receivingSame
      cases receivingScopeSame
      cases receivingSame
      have savedNext := saved.receiving_congr (scope_append_assoc _ _ _).symm (hints_append_assoc _ _ _).symm
      have rebuilt := Segment.live known actionKnown inputAnnotation answerAnnotation scope held savedNext savedInterface source resume close bound
      simp only [List.cons_append, List.append_assoc]
      refine ⟨_, rebuilt, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent, evaluation, spendAll, merge_assoc]
  | spent known annotation scope rest bound ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second receivingScopeSame receivingSame
      refine ⟨_, .spent known annotation scope source bound, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent, evaluation, spendAll, merge_assoc]

end Ash.OneShot.SourcePlannedCheckedFrames

#print axioms Ash.OneShot.SourcePlannedCheckedFrames.Frame.receiving_congr
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.Frame.decorate_append
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.Segment.receiving_congr
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.Segment.hints_congr
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.Segment.input_weaken
#print axioms Ash.OneShot.SourcePlannedCheckedFrames.segment_append
