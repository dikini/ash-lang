import RecursiveRequirements
import UniformClauseBounds

/-! Structural effect bounds for recursive continuation requirements. Ownership
    demands, invocation keys and interpretation positions are exact. Only literal
    request rows may be covered by a larger row. The existing finite checker
    supplies recursion through captured records. -/
namespace Ash.OneShot.RecursiveBounds
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Store Key Checked evaluate)
open EffectBounds (Covers covers_refl covers_append_bounds)

inductive Bounds : {owners : List Nat} → Requirements owners → Requirements owners → Prop where
  | request (covered : Covers upper lower) : Bounds (.request nearer lower) (.request nearer upper)
  | retire : Bounds (.retire owner) (.retire owner)
  | spent : Bounds (.spent owner) (.spent owner)
  | invoke : Bounds (.invoke key demand nearer) (.invoke key demand nearer)
  | sequence (first : Bounds a upperA) (second : Bounds b upperB) :
      Bounds (.sequence a b) (.sequence upperA upperB)
  | emitAfter (body : Bounds a upperA) (covered : Covers upper lower) :
      Bounds (.emitAfter a nearer lower) (.emitAfter upperA nearer upper)
  | choice (first : Bounds a upperA) (second : Bounds b upperB) :
      Bounds (.choice a b same) (.choice upperA upperB same)

theorem bounds_refl (requirements : Requirements owners) : Bounds requirements requirements := by
  induction requirements with
  | request => exact .request (covers_refl _)
  | retire => exact .retire
  | spent => exact .spent
  | invoke => exact .invoke
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond
  | emitAfter body nearer raw ih => exact .emitAfter ih (covers_refl _)
  | choice first second same ihFirst ihSecond => exact .choice ihFirst ihSecond

/-- Matching finite records preserve lookup order, owner identity, continuation
    mode and the exact recursive demand of each saved template. -/
inductive StoreBounds : Store → Store → Prop where
  | nil : StoreBounds [] []
  | cons {actual upper : Requirements demand} (body : Bounds actual upper) (rest : StoreBounds actualRest upperRest) :
      StoreBounds ((key, ⟨demand, actual⟩) :: actualRest) ((key, ⟨demand, upper⟩) :: upperRest)

theorem store_refl (records : Store) : StoreBounds records records := by
  induction records with
  | nil => exact .nil
  | cons entry rest ih => obtain ⟨key, demand, body⟩ := entry; exact .cons (bounds_refl body) ih

theorem lookup_bounds (records : StoreBounds actualStore upperStore)
    (known : RecursiveRequirements.lookup key upperStore = some ⟨demand, upper⟩) :
    ∃ actual, RecursiveRequirements.lookup key actualStore = some ⟨demand, actual⟩ ∧ Bounds actual upper := by
  induction records with
  | nil => cases known
  | @cons owners actualRest upperRest candidate actual bound body rest ih =>
      by_cases same : key = candidate
      · simp only [RecursiveRequirements.lookup, same, if_true] at known
        cases Option.some.inj known
        exact ⟨actual, by simp only [RecursiveRequirements.lookup, same, if_true], body⟩
      · simp only [RecursiveRequirements.lookup, same, if_false] at known
        obtain ⟨actual, found, bounded⟩ := ih known
        exact ⟨actual, by simpa only [RecursiveRequirements.lookup, same, if_false] using found, bounded⟩

theorem export_covered (covered : Covers upper lower)
    (exported : OwnerSource.exportAt receiving before upper = some upperRow) :
    ∃ lowerRow, OwnerSource.exportAt receiving before lower = some lowerRow ∧ Covers upperRow lowerRow :=
  UniformClauseBounds.residual_coverage covered exported

/-- Reuse row coverage while traversing the existing finite recursive checker.
    Fuel decreases only when a saved continuation body is consulted. -/
theorem fuel_below (fuel : Nat) {actual upper : Requirements owners}
    (records : StoreBounds actualStore upperStore) (bounded : Bounds actual upper) :
    UniformClauseBounds.SuccessBelow
      (RecursiveRequirements.evaluateFuel fuel actualStore receiving before actual)
      (RecursiveRequirements.evaluateFuel fuel upperStore receiving before upper) := by
  induction fuel using Nat.strongRecOn generalizing owners receiving before with
  | ind fuel smaller =>
      induction bounded generalizing receiving before with
      | request covered =>
          simp only [RecursiveRequirements.evaluateFuel]
          exact fun row exported => export_covered covered exported
      | retire =>
          simp only [RecursiveRequirements.evaluateFuel]
          exact UniformClauseBounds.success_refl _
      | spent =>
          simp only [RecursiveRequirements.evaluateFuel]
          exact UniformClauseBounds.success_refl _
      | @invoke key demand nearer =>
          cases fuel with
          | zero =>
              simp only [RecursiveRequirements.evaluateFuel]
              exact UniformClauseBounds.success_refl _
          | succ remaining =>
              intro row evaluated
              cases found : RecursiveRequirements.lookup key upperStore with
              | none => simp [RecursiveRequirements.evaluateFuel, found] at evaluated
              | some template =>
                  obtain ⟨actualDemand, body⟩ := template
                  by_cases ready : actualDemand = demand ∧ PhaseRechecking.checkOwners before (key.owner :: demand) = true ∧
                      (OwnerPhases.consume key.owner (nearer ++ receiving)).isSome = true
                  · obtain ⟨actualBody, actualFound, bodyBound⟩ := lookup_bounds records found
                    have compared := smaller remaining (Nat.lt_succ_self remaining) bodyBound
                      (receiving := nearer ++ receiving) (before := OwnerPhaseTransitions.spend before key.owner)
                    have check : RecursiveRequirements.evaluateFuel remaining upperStore (nearer ++ receiving)
                        (OwnerPhaseTransitions.spend before key.owner) body = some row := by
                      simpa only [RecursiveRequirements.evaluateFuel, found, ready, and_self, if_true] using evaluated
                    obtain ⟨actualRow, checked, covered⟩ := compared row check
                    exact ⟨actualRow, by simpa only [RecursiveRequirements.evaluateFuel, actualFound, ready, and_self, if_true] using checked, covered⟩
                  · simp only [RecursiveRequirements.evaluateFuel, found, ready, if_false] at evaluated
                    cases evaluated
      | sequence first second ihFirst ihSecond =>
          simp only [RecursiveRequirements.evaluateFuel]
          exact UniformClauseBounds.merge_coverage ihFirst ihSecond
      | emitAfter body covered ih =>
          simp only [RecursiveRequirements.evaluateFuel]
          exact UniformClauseBounds.merge_coverage ih (fun row exported => export_covered covered exported)
      | choice first second ihFirst ihSecond =>
          simp only [RecursiveRequirements.evaluateFuel]
          exact UniformClauseBounds.merge_coverage ihFirst ihSecond

/-- A checked upper requirement supplies an actual check and its row bound,
    including recursively referenced saved bodies at their actual positions. -/
theorem checked_below
    (checked : Checked upperStore receiving before upper upperRow)
    (records : StoreBounds actualStore upperStore)
    (bounded : Bounds actual upper) :
    ∃ actualRow, Checked actualStore receiving before actual actualRow ∧ Covers upperRow actualRow := by
  obtain ⟨row, evaluated, covered⟩ := fuel_below _ records bounded upperRow
    (RecursiveRequirements.checked_complete checked)
  exact ⟨row, RecursiveRequirements.evaluate_sound evaluated, covered⟩

theorem evaluation_below
    (evaluated : evaluate upperStore receiving before upper = some upperRow)
    (records : StoreBounds actualStore upperStore) (bounded : Bounds actual upper) :
    ∃ actualRow, evaluate actualStore receiving before actual = some actualRow ∧ Covers upperRow actualRow := by
  obtain ⟨row, checked, covered⟩ := checked_below (RecursiveRequirements.evaluate_sound evaluated) records bounded
  exact ⟨row, RecursiveRequirements.checked_complete checked, covered⟩

theorem admitted_below
    (checked : Checked upperStore receiving before upper upperRow)
    (records : StoreBounds actualStore upperStore) (bounded : Bounds actual upper)
    (accepted : checkFootprint outside upperRow = true) :
    ∃ actualRow, Checked actualStore receiving before actual actualRow ∧
      Covers upperRow actualRow ∧ checkFootprint outside actualRow = true := by
  obtain ⟨row, actualCheck, covered⟩ := checked_below checked records bounded
  exact ⟨row, actualCheck, covered, EffectBounds.check_covered accepted covered⟩

namespace Examples
open RecursiveRequirements.Examples (outerKey innerKey outer invocation store recursive_invocation_checked)
open SharedResumption.NestedExamples (outerBoundary)
open SharedResumption.Examples (tables raw)

def actualStore : Store := [(outerKey, ⟨[29], outer⟩), (innerKey, ⟨[], .request [] []⟩)]

theorem records_bounded : StoreBounds actualStore store :=
  .cons (bounds_refl outer) (.cons (.request (List.nil_subset _)) .nil)

theorem nested_check_and_ownership : ∃ row,
    Checked actualStore (OwnerPhases.ofStack tables outerBoundary)
      (OwnerPhaseTransitions.available [19, 29]) invocation row ∧ Covers raw row ∧
    OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available [19, 29]) [19, 29]
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available [19, 29]) [19, 29]) := by
  obtain ⟨row, checked, covered⟩ := checked_below recursive_invocation_checked records_bounded (bounds_refl invocation)
  exact ⟨row, checked, covered, RecursiveRequirements.checked_trace checked⟩

end Examples
end Ash.OneShot.RecursiveBounds
#print axioms Ash.OneShot.RecursiveBounds.bounds_refl
#print axioms Ash.OneShot.RecursiveBounds.store_refl
#print axioms Ash.OneShot.RecursiveBounds.lookup_bounds
#print axioms Ash.OneShot.RecursiveBounds.export_covered
#print axioms Ash.OneShot.RecursiveBounds.checked_below
#print axioms Ash.OneShot.RecursiveBounds.evaluation_below
#print axioms Ash.OneShot.RecursiveBounds.admitted_below
#print axioms Ash.OneShot.RecursiveBounds.Examples.records_bounded
#print axioms Ash.OneShot.RecursiveBounds.Examples.nested_check_and_ownership
#print axioms Ash.OneShot.RecursiveBounds.fuel_below
