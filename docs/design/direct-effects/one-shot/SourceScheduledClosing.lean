import SourceScheduledFrames

/-! Extract closing annotations from typed retained plans and derive their
scheduling checks from the request rule at the same actual capture. -/
namespace Ash.OneShot.SourceScheduledClosing
open ScopedExpressions ScopedExecution
open SourceRetainedPlans (Forest closingForest)
open SourceContextualHints (Hints)
open SourcePlannedClosingPlans (Plans Contents Template Checked)
open SourceScheduledFrames (Segment)
open SourceScheduledChecks (Local)

/-- Source extraction preserves the exact forest, including callbacks nested
inside dormant captures. The old closing-plan recursion is reused. -/
theorem plan_contents {hints : Hints receiving} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      capture input output demand requirements records forest outside incoming outgoing)
    (built : makePlan capture = some plan) :
    ∃ plans : Plans plan (SourceContextualInvocationHints.forClosing hints),
      Contents operations policy contracts world plans ∧ closingForest plans = forest.forClosing := by
  induction capture generalizing input output demand requirements records receiving hints outsideScope outsideHints incoming outgoing plan with
  | nil => cases source; cases built; exact ⟨.nil, .nil, rfl⟩
  | push frame rest ih => cases source with
    | push head tail bound => cases head with
      | plain => obtain ⟨plans, contents, same⟩ := ih tail built; exact ⟨plans, contents, same⟩
      | handler => obtain ⟨plans, contents, same⟩ := ih tail built; exact ⟨plans, contents, same⟩
      | cell =>
          cases next : makePlan rest <;> simp [makePlan, next] at built
          case some suffix =>
            subst plan
            obtain ⟨plans, contents, same⟩ := ih tail next
            exact ⟨.release plans, .release contents, congrArg Forest.cell same⟩
      | armed scope callback annotation interface checked =>
          cases next : makePlan rest <;> simp [makePlan, next] at built
          case some suffix =>
            subst plan
            obtain ⟨plans, contents, same⟩ := ih tail next
            exact ⟨.invoke _ plans, .invoke callback contents, congrArg (Forest.cleanup _) same⟩
      | running | closing | retiring => simp [makePlan] at built
  | live owner inputType answerType saved caller rest ihSaved ihTail => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scopeKnown held captured savedBound tail resume close bound =>
        cases inside : makePlan saved <;> cases outsidePlan : makePlan rest <;> simp [makePlan, inside, outsidePlan] at built
        case some.some first second =>
          subst plan
          obtain ⟨savedPlans, savedContents, savedSame⟩ := ihSaved captured inside
          obtain ⟨tailPlans, tailContents, tailSame⟩ := ihTail tail outsidePlan
          refine ⟨savedPlans.append (.retire tailPlans), savedContents.append (.retire known tailContents), ?_⟩
          exact (SourceRetainedPlans.closingForest_append savedPlans (.retire (owner := owner) tailPlans)).trans
            (congr (congrArg Forest.append savedSame) (congrArg Forest.running tailSame))
  | spent owner answer caller rest ih => cases source with
    | spent known annotation scopeKnown tail bound => obtain ⟨plans, contents, same⟩ := ih tail built; exact ⟨plans, contents, same⟩

/-- The request schedule supplies the closing check for the template extracted
from its actual captured source. There is no independent closing-check premise. -/
theorem request_template {wholeHints : Hints wholeScope} {savedHints : Hints capturedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (request : Local outward actions phases world (.request (effect := effect) (operation := operation)) whole)
    (cut : SourcePlannedCuts.Cut effect operation contract modes wholeHints savedHints waitingHints)
    (same : HEq whole (saved.append waiting)) (disposes : contract.dispose = true)
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      capture input output demand requirements records saved waiting incoming outgoing)
    (built : makePlan capture = some plan) :
    ∃ plans : Plans plan (SourceContextualInvocationHints.forClosing savedHints),
    ∃ raw, ∃ requirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan),
      Template operations policy contracts tables world caller plans raw requirements ∧
      Checked outward actions phases world (.running waitingHints) plans := by
  obtain ⟨plans, contents, retained⟩ := plan_contents source built
  obtain ⟨raw, requirements, template⟩ := contents.template (tables := tables) (caller := caller)
  refine ⟨plans, raw, requirements, template, ?_⟩
  cases request with
  | request guard scheduled =>
      have checked := scheduled _ _ _ _ _ _ cut saved waiting same disposes
      rw [← retained] at checked
      exact checked.closing_checked

/-- Disposal uses the exact selected capture's callback plans under the spent
owner phase. Its complete recomposed schedule supplies the closing prefix. -/
theorem dispose_template {hints : Hints scope} {forest : Forest hints}
    {selected : SourceContextualInvocationHints.Selection}
    {front : Forest selected.front} {saved : Forest selected.saved} {tail : Forest selected.tail}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (dispose : Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) forest)
    (found : SourceContextualInvocationHints.findOwner owner hints = some selected)
    (same : HEq forest (front.append (.live (owner := owner) saved tail)))
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      capture input output demand requirements records saved outside incoming outgoing)
    (built : makePlan capture = some plan) :
    ∃ plans : Plans plan (SourceContextualInvocationHints.forClosing selected.saved),
    ∃ raw, ∃ requirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan),
      Template operations policy contracts tables world caller plans raw requirements ∧
      Checked outward actions (OwnerPhaseTransitions.spend phases owner) world
        (.running (selected.front.append (.spent (owner := owner) selected.tail))) plans := by
  obtain ⟨plans, contents, retained⟩ := plan_contents source built
  obtain ⟨raw, requirements, template⟩ := contents.template (tables := tables) (caller := caller)
  refine ⟨plans, raw, requirements, template, ?_⟩
  have checked := dispose.dispose_schedule found same
  rw [← retained] at checked
  exact checked.closing_prefix_checked

end Ash.OneShot.SourceScheduledClosing

#print axioms Ash.OneShot.SourceScheduledClosing.plan_contents
#print axioms Ash.OneShot.SourceScheduledClosing.request_template

#print axioms Ash.OneShot.SourceScheduledClosing.dispose_template
