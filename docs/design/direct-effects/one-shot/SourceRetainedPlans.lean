import SourceRetainedPlanData
import SourcePlannedClosingPlans

/-! Scope annotations retain the actual pending and callback plans. Selection,
closing and recomposition preserve this data; the computation grammar and
existing continuation access relations are unchanged. -/
namespace Ash.OneShot.SourceRetainedPlans
open SourceContextualHints (Hints)
open SourceDeclarationPlans (Plan)
open SourceContextualInvocationHints (forClosing)

/-- Lift the existing nearest-handler cut to the retained plans. No second
lookup algorithm or independently chosen callback plan is used. -/
theorem split_cut
    (cut : SourcePlannedCuts.Cut effect operation contract modes hints saved waiting)
    (source : Forest hints) :
    ∃ captured : Forest saved, ∃ tail : Forest waiting, HEq source (captured.append tail) := by
  induction cut with
  | hit known declared => cases source with | handler rest => exact ⟨.handler .nil, rest, HEq.rfl⟩
  | plain next ih => cases source with
    | plain plan rest =>
        obtain ⟨captured, tail, same⟩ := ih rest
        have scopeSame := next.reconstruct_scope
        have hintsSame := next.hints
        cases scopeSame
        cases hintsSame
        cases same
        exact ⟨.plain plan captured, tail, HEq.rfl⟩
  | handler different next ih => cases source with
    | handler rest =>
        obtain ⟨captured, tail, same⟩ := ih rest
        have scopeSame := next.reconstruct_scope
        have hintsSame := next.hints
        cases scopeSame
        cases hintsSame
        cases same
        exact ⟨.handler captured, tail, HEq.rfl⟩
  | cell different next ih => cases source with
    | cell rest =>
        obtain ⟨captured, tail, same⟩ := ih rest
        have scopeSame := next.reconstruct_scope
        have hintsSame := next.hints
        cases scopeSame
        cases hintsSame
        cases same
        exact ⟨.cell captured, tail, HEq.rfl⟩
  | cleanup next ih => cases source with
    | cleanup plan rest =>
        obtain ⟨captured, tail, same⟩ := ih rest
        have scopeSame := next.reconstruct_scope
        have hintsSame := next.hints
        cases scopeSame
        cases hintsSame
        cases same
        exact ⟨.cleanup plan captured, tail, HEq.rfl⟩
  | running next ih => cases source with
    | running rest =>
        obtain ⟨captured, tail, same⟩ := ih rest
        have scopeSame := next.reconstruct_scope
        have hintsSame := next.hints
        cases scopeSame
        cases hintsSame
        cases same
        exact ⟨.running captured, tail, HEq.rfl⟩
  | live next ih => cases source with
    | live dormant rest =>
        obtain ⟨captured, tail, same⟩ := ih rest
        have scopeSame := next.reconstruct_scope
        have hintsSame := next.hints
        cases scopeSame
        cases hintsSame
        cases same
        exact ⟨.live dormant captured, tail, HEq.rfl⟩
  | spent next ih => cases source with
    | spent rest =>
        obtain ⟨captured, tail, same⟩ := ih rest
        have scopeSame := next.reconstruct_scope
        have hintsSame := next.hints
        cases scopeSame
        cases hintsSame
        cases same
        exact ⟨.spent captured, tail, HEq.rfl⟩

/-- Closing templates expose exactly the plans used by their source and
scheduling judgments as a retained forest. -/
def closingForest (plans : SourcePlannedClosingPlans.Plans plan hints) : Forest hints :=
  match plans with
  | .nil => .nil
  | .release rest => .cell (closingForest rest)
  | .retire rest => .running (closingForest rest)
  | .invoke callback rest => .cleanup callback (closingForest rest)

theorem closingForest_append (first : SourcePlannedClosingPlans.Plans before front)
    (second : SourcePlannedClosingPlans.Plans after tail) :
    closingForest (first.append second) = (closingForest first).append (closingForest second) := by
  induction first <;> simp_all [SourcePlannedClosingPlans.Plans.append, closingForest, Forest.append] <;> rfl

end Ash.OneShot.SourceRetainedPlans

#print axioms Ash.OneShot.SourceRetainedPlans.split_cut
#print axioms Ash.OneShot.SourceRetainedPlans.closingForest_append
