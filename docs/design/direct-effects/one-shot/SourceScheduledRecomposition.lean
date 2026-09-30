import SourceScheduledFrames

/-! Ordered recomposition retains actual pending plans. Scope and annotation
associativity and requirement accounting reuse the established equations. -/
namespace Ash.OneShot.SourceScheduledRecomposition
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open SourceScheduledChecks (Local Pending)
open SourceDependencyChecks (scope_append_assoc)
open SourcePlannedRecomposition (hints_append_assoc)

private theorem lift_heq {shape : SourceDependencyCapture.Scope → SourceDependencyCapture.Scope}
    {decorate : ∀ {scope}, Hints scope → Hints (shape scope)}
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints)
    (sameForest : HEq first second)
    (lift : ∀ {scope} {hints : Hints scope}, Forest hints → Forest (decorate hints)) :
    HEq (lift first) (lift second) := by
  cases sameScope
  cases sameHints
  cases sameForest
  rfl

theorem forest_append_assoc {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {thirdHints : Hints thirdScope} (first : Forest firstHints) (second : Forest secondHints) (third : Forest thirdHints) :
    HEq ((first.append second).append third) (first.append (second.append third)) := by
  induction first with
  | nil => rfl
  | plain plan rest ih => exact lift_heq (decorate := fun hints => .plain hints) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) ih (fun forest => .plain plan forest)
  | handler rest ih => exact lift_heq (decorate := fun hints => .handler _ hints) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) ih (fun forest => .handler forest)
  | cell rest ih => exact lift_heq (decorate := fun hints => .cell hints) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) ih (fun forest => .cell forest)
  | cleanup plan rest ih => exact lift_heq (decorate := fun hints => .cleanup hints) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) ih (fun forest => .cleanup plan forest)
  | running rest ih => exact lift_heq (decorate := fun hints => .running hints) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) ih (fun forest => .running forest)
  | live saved rest ihSaved ihRest => exact lift_heq (decorate := fun hints => .live _ hints) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) ihRest (fun forest => .live saved forest)
  | spent rest ih => exact lift_heq (decorate := fun hints => .spent hints) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) ih (fun forest => .spent forest)

theorem predicate_congr {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints) (sameForest : HEq first second)
    (predicate : ∀ {scope} {hints : Hints scope}, Forest hints → Prop) : predicate first ↔ predicate second := by
  cases sameScope
  cases sameHints
  cases sameForest
  rfl

section
variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

theorem local_append_assoc {firstHints : Hints firstScope} {secondHints : Hints secondScope} {thirdHints : Hints thirdScope}
    (first : Forest firstHints) (second : Forest secondHints) (third : Forest thirdHints) :
    Local outward actions phases world plan ((first.append second).append third) ↔
      Local outward actions phases world plan (first.append (second.append third)) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc firstHints secondHints thirdHints) (forest_append_assoc first second third) (fun hints => Local outward actions phases world plan hints)

theorem running_append_assoc {firstHints : Hints firstScope} {secondHints : Hints secondScope} {thirdHints : Hints thirdScope}
    (first : Forest firstHints) (second : Forest secondHints) (third : Forest thirdHints) :
    Local outward actions phases world plan (.running ((first.append second).append third)) ↔
      Local outward actions phases world plan (.running (first.append (second.append third))) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc firstHints secondHints thirdHints) (forest_append_assoc first second third) (fun hints => Local outward actions phases world plan (.running hints))

theorem pending_outside_assoc {firstHints : Hints firstScope} {secondHints : Hints secondScope} {thirdHints : Hints thirdScope}
    (first : Forest firstHints) (second : Forest secondHints) (third : Forest thirdHints) :
    Pending outward actions phases world saved ((first.append second).append third) ↔
      Pending outward actions phases world saved (first.append (second.append third)) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc firstHints secondHints thirdHints) (forest_append_assoc first second third) (fun hints => Pending outward actions phases world saved hints)

/-- Split and join the same annotated forest. Every pending expression and
callback retains its plan, and dormant branches retain their complete suffix. -/
theorem pending_append_iff {firstHints : Hints firstScope} {secondHints : Hints secondScope} {outsideHints : Hints outsideScope}
    (first : Forest firstHints) (second : Forest secondHints) (outside : Forest outsideHints) :
    Pending outward actions phases world (first.append second) outside ↔
      Pending outward actions phases world first (second.append outside) ∧
      Pending outward actions phases world second outside := by
  induction first with
  | nil => exact ⟨fun checked => ⟨.nil, checked⟩, fun ⟨_, checked⟩ => checked⟩
  | plain plan rest ih =>
      constructor
      · intro checked; cases checked with
        | plain code tail =>
            obtain ⟨inside, remaining⟩ := ih.mp tail
            exact ⟨.plain ((local_append_assoc _ _ _).mp code) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | plain code tail => exact .plain ((local_append_assoc _ _ _).mpr code) (ih.mpr ⟨tail, remaining⟩)
  | cleanup plan rest ih =>
      constructor
      · intro checked; cases checked with
        | cleanup callback tail =>
            obtain ⟨inside, remaining⟩ := ih.mp tail
            exact ⟨.cleanup ((running_append_assoc _ _ _).mp callback) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | cleanup callback tail => exact .cleanup ((running_append_assoc _ _ _).mpr callback) (ih.mpr ⟨tail, remaining⟩)
  | live saved rest ihSaved ihRest =>
      constructor
      · intro checked; cases checked with
        | live saved tail =>
            obtain ⟨inside, remaining⟩ := ihRest.mp tail
            exact ⟨.live ((pending_outside_assoc _ _ _).mp saved) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | live saved tail => exact .live ((pending_outside_assoc _ _ _).mpr saved) (ihRest.mpr ⟨tail, remaining⟩)
  | handler rest ih =>
      constructor
      · intro checked; cases checked with
        | handler supplied tail =>
            obtain ⟨inside, remaining⟩ := ih.mp tail
            exact ⟨.handler (by simpa only [scope_append_assoc] using supplied) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | handler supplied tail =>
            exact .handler (by simpa only [scope_append_assoc] using supplied) (ih.mpr ⟨tail, remaining⟩)
  | cell rest ih =>
      constructor
      · intro checked; cases checked with
        | cell tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.cell inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | cell tail => exact .cell (ih.mpr ⟨tail, remaining⟩)
  | running rest ih =>
      constructor
      · intro checked; cases checked with
        | running tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.running inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | running tail => exact .running (ih.mpr ⟨tail, remaining⟩)
  | spent rest ih =>
      constructor
      · intro checked; cases checked with
        | spent tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.spent inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | spent tail => exact .spent (ih.mpr ⟨tail, remaining⟩)

theorem pending_capture {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (checked : Pending outward actions phases world (saved.append tail) outside) :
    Pending outward actions phases world (.live (owner := owner) saved tail) outside :=
  .live ((pending_append_iff _ _ _).mp checked).1 ((pending_append_iff _ _ _).mp checked).2

end

theorem forest_append_nil {hints : Hints scope} (forest : Forest hints) : HEq (forest.append .nil) forest := by
  induction forest with
  | nil => rfl
  | plain plan rest ih =>
      exact lift_heq (decorate := fun hints => .plain hints)
        (SourceDependencyProjection.scope_append_nil _) (SourcePlannedRecomposition.hints_append_nil _) ih (fun forest => .plain plan forest)
  | handler rest ih =>
      exact lift_heq (decorate := fun hints => .handler _ hints)
        (SourceDependencyProjection.scope_append_nil _) (SourcePlannedRecomposition.hints_append_nil _) ih (fun forest => .handler forest)
  | cell rest ih =>
      exact lift_heq (decorate := fun hints => .cell hints)
        (SourceDependencyProjection.scope_append_nil _) (SourcePlannedRecomposition.hints_append_nil _) ih (fun forest => .cell forest)
  | cleanup plan rest ih =>
      exact lift_heq (decorate := fun hints => .cleanup hints)
        (SourceDependencyProjection.scope_append_nil _) (SourcePlannedRecomposition.hints_append_nil _) ih (fun forest => .cleanup plan forest)
  | running rest ih =>
      exact lift_heq (decorate := fun hints => .running hints)
        (SourceDependencyProjection.scope_append_nil _) (SourcePlannedRecomposition.hints_append_nil _) ih (fun forest => .running forest)
  | live saved rest ihSaved ihRest =>
      exact lift_heq (decorate := fun hints => .live _ hints)
        (SourceDependencyProjection.scope_append_nil _) (SourcePlannedRecomposition.hints_append_nil _) ihRest (fun forest => .live saved forest)
  | spent rest ih =>
      exact lift_heq (decorate := fun hints => .spent hints)
        (SourceDependencyProjection.scope_append_nil _) (SourcePlannedRecomposition.hints_append_nil _) ih (fun forest => .spent forest)

section
variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

theorem local_append_nil {hints : Hints scope} (forest : Forest hints) :
    Local outward actions phases world plan (forest.append .nil) ↔ Local outward actions phases world plan forest :=
  predicate_congr (SourceDependencyProjection.scope_append_nil _) (SourcePlannedRecomposition.hints_append_nil hints)
    (forest_append_nil forest) (fun forest => Local outward actions phases world plan forest)

theorem pending_outside_nil {hints : Hints scope} (outside : Forest hints) :
    Pending outward actions phases world saved (outside.append .nil) ↔ Pending outward actions phases world saved outside :=
  predicate_congr (SourceDependencyProjection.scope_append_nil _) (SourcePlannedRecomposition.hints_append_nil hints)
    (forest_append_nil outside) (fun outside => Pending outward actions phases world saved outside)

theorem pending_resume {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (inside : Pending outward actions phases world saved (.spent (owner := owner) tail))
    (waiting : Pending outward actions phases world tail .nil) :
    Pending outward actions phases world (saved.append (.spent (owner := owner) tail)) .nil :=
  (pending_append_iff _ _ _).mpr ⟨(pending_outside_nil _).mpr inside, .spent waiting⟩

theorem pending_dispose {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (closing : Pending outward actions phases world saved.forClosing (.running (.spent (owner := owner) tail)))
    (waiting : Pending outward actions phases world tail .nil) :
    Pending outward actions phases world (saved.forClosing.append (.running (.spent (owner := owner) tail))) .nil :=
  (pending_append_iff _ _ _).mpr ⟨(pending_outside_nil _).mpr closing, .running (.spent waiting)⟩

/-- Construct head invocation checks from the retained pieces. The access and
compatibility proofs are the established independent continuation judgments. -/
theorem resume_clause {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (known : actions owner = some rights) (permission : rights.resume = true)
    (available : phases owner = .available)
    (inside : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world saved (.spent (owner := owner) tail))
    (waiting : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world tail .nil)
    (compatible : SourceContextualHintChecking.Compatible (.live (owner := owner) savedHints tailHints) .nil) :
    Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) (.live (owner := owner) saved tail) := by
  let selected : SourceContextualInvocationHints.Selection := ⟨⟨.nil, savedScope, tailScope⟩, .nil, savedHints, tailHints⟩
  have found : SourceContextualInvocationHints.findOwner owner (.live (owner := owner) savedHints tailHints) = some selected := by
    simp [SourceContextualInvocationHints.findOwner, selected]
  refine .resume (selected := selected) (front := .nil) (saved := saved) (tail := tail) found ?_ HEq.rfl (pending_resume inside waiting)
  exact .checked found (.checked .hit known permission available) (SourcePlannedRecomposition.resume_compatible compatible)

theorem dispose_clause {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (known : actions owner = some rights) (permission : rights.dispose = true)
    (available : phases owner = .available) (unprotected : savedScope.held = false)
    (route : SourceRecursiveRoutes.Closing outward savedScope.shape [] [])
    (closing : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world
      saved.forClosing (.running (.spent (owner := owner) tail)))
    (waiting : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world tail .nil)
    (compatible : SourceContextualHintChecking.Compatible tailHints .nil) :
    Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) (.live (owner := owner) saved tail) := by
  let selected : SourceContextualInvocationHints.Selection := ⟨⟨.nil, savedScope, tailScope⟩, .nil, savedHints, tailHints⟩
  have found : SourceContextualInvocationHints.findOwner owner (.live (owner := owner) savedHints tailHints) = some selected := by
    simp [SourceContextualInvocationHints.findOwner, selected]
  refine .dispose (selected := selected) (front := .nil) (saved := saved) (tail := tail) found ?_ HEq.rfl (pending_dispose closing waiting)
  exact .checked found (.checked .hit known permission available unprotected route) (SourcePlannedRecomposition.dispose_compatible compatible)

end

end Ash.OneShot.SourceScheduledRecomposition

namespace Ash.OneShot.SourceScheduledFrames
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

variable {front tail : Stack}

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

theorem Segment.input_weaken [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
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
          merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before firstRequirements)
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
      have matched := rebuilt.forest_congr head.source.source.erase.realizes.append.symm (head.source.decorate_append _ _) (head.decorate_append _ _)
      rw [List.append_assoc]
      refine ⟨_, matched, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        OwnerPhases.stack_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, merge_assoc]
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

end Ash.OneShot.SourceScheduledFrames

#print axioms Ash.OneShot.SourceScheduledRecomposition.forest_append_assoc
#print axioms Ash.OneShot.SourceScheduledRecomposition.local_append_assoc
#print axioms Ash.OneShot.SourceScheduledRecomposition.running_append_assoc
#print axioms Ash.OneShot.SourceScheduledRecomposition.pending_outside_assoc
#print axioms Ash.OneShot.SourceScheduledRecomposition.pending_append_iff
#print axioms Ash.OneShot.SourceScheduledRecomposition.pending_capture
#print axioms Ash.OneShot.SourceScheduledFrames.Frame.receiving_congr
#print axioms Ash.OneShot.SourceScheduledFrames.Frame.decorate_append
#print axioms Ash.OneShot.SourceScheduledFrames.Segment.receiving_congr
#print axioms Ash.OneShot.SourceScheduledFrames.Segment.forest_congr
#print axioms Ash.OneShot.SourceScheduledFrames.Segment.input_weaken
#print axioms Ash.OneShot.SourceScheduledFrames.segment_append

#print axioms Ash.OneShot.SourceScheduledRecomposition.forest_append_nil
#print axioms Ash.OneShot.SourceScheduledRecomposition.local_append_nil
#print axioms Ash.OneShot.SourceScheduledRecomposition.pending_outside_nil
#print axioms Ash.OneShot.SourceScheduledRecomposition.pending_resume
#print axioms Ash.OneShot.SourceScheduledRecomposition.pending_dispose
#print axioms Ash.OneShot.SourceScheduledRecomposition.resume_clause
#print axioms Ash.OneShot.SourceScheduledRecomposition.dispose_clause

#print axioms Ash.OneShot.SourceScheduledRecomposition.predicate_congr
