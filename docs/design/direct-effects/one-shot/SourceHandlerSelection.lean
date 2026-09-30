import SourceHandlerRequirements
import SourcePlannedCuts

/-! Exact captured and waiting scopes under interpretation replacement.
These laws use the existing lookup algorithm and its authenticated cuts;
they do not assert source preservation under arbitrary handler insertion. -/
namespace Ash.OneShot.SourceHandlerSelection
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture
open SourceHandlerRequirements (reaches)
open SourceContextualHints (Hints)

/-- A selection made inside a retained prefix keeps its capture and gains
the appended outside only in its waiting scope. Builtins have no capture. -/
def appendWaiting (outside : Scope) : Selection → Selection
  | .builtin identity => .builtin identity
  | .handler captured tail contract modes => .handler captured (tail.append outside) contract modes

/-- Exact composition of lookup. A matching incomplete handler stops lookup,
so an internal `none` cannot be replaced by an outside offer. -/
theorem select_append (front : Scope) :
    select effect operation (front.append outside) =
      if reaches effect front then
        (select effect operation outside).map (Selection.prepend (front.append))
      else (select effect operation front).map (appendWaiting outside) := by
  induction front with
  | nil =>
      simp only [Scope.append, reaches, ↓reduceIte]
      cases select effect operation outside with
      | none => rfl
      | some selected => cases selected <;> rfl
  | handler other table families rest ih =>
      by_cases same : effect = other
      · simp only [Scope.append, select, reaches, if_pos same, Bool.false_eq_true, ↓reduceIte]
        cases lookup operation table <;> cases lookupDependencies operation families <;> rfl
      · simp only [Scope.append, select, reaches, if_neg same, ih]
        by_cases passed : reaches effect rest = true <;>
          simp only [passed, Bool.false_eq_true, ↓reduceIte, Option.map_map] <;>
          congr 1 <;> funext selected <;> cases selected <;> rfl
  | cell identity rest ih =>
      by_cases same : effect = .cell identity
      · simp [Scope.append, select, reaches, same, appendWaiting]
      · simp only [Scope.append, select, reaches, if_neg same, ih]
        by_cases passed : reaches effect rest = true <;>
          simp only [passed, Bool.false_eq_true, ↓reduceIte, Option.map_map] <;>
          congr 1 <;> funext selected <;> cases selected <;> rfl
  | plain dependencies rest ih | cleanup needs callback rest ih | running rest ih | live owner saved rest ihSaved ih | spent owner rest ih =>
      simp only [Scope.append, select, reaches, ih]
      by_cases passed : reaches effect rest = true <;>
        simp only [passed, Bool.false_eq_true, ↓reduceIte, Option.map_map] <;>
        congr 1 <;> funext selected <;> cases selected <;> rfl

theorem selected_outside (passed : reaches effect front = true)
    (found : select effect operation outside = some selected) :
    select effect operation (front.append outside) = some (Selection.prepend front.append selected) := by
  rw [select_append, passed, if_pos rfl, found]
  rfl

theorem selected_inside (stopped : reaches effect front = false)
    (found : select effect operation front = some selected) :
    select effect operation (front.append outside) = some (appendWaiting outside selected) := by
  rw [select_append, stopped, if_neg Bool.false_ne_true, found]
  rfl

theorem blocked_inside (stopped : reaches effect front = false)
    (missing : select effect operation front = none) :
    select effect operation (front.append outside) = none := by
  rw [select_append, stopped, if_neg Bool.false_ne_true, missing]
  rfl

/-- An exposed request is intercepted by the new matching handler. Its
capture contains the entire preceding scope and that handler, while its
waiting scope is precisely the original outside. -/
theorem inserted_selected (passed : reaches effect front = true)
    (known : lookup operation table = some contract)
    (declared : lookupDependencies operation families = some modes) :
    select effect operation (front.append (.handler effect table families outside)) =
      some (.handler (front.append (.handler effect table families .nil)) outside contract modes) := by
  exact selected_outside (selected := .handler (.handler effect table families .nil) outside contract modes)
    passed (by simp only [select, ↓reduceIte, known, declared])

/-- A missing operation or dependency family at the new nearest handler
blocks the request, even when the previous outside could handle it. -/
theorem inserted_missing (passed : reaches effect front = true)
    (missing : lookup operation table = none ∨ lookupDependencies operation families = none) :
    select effect operation (front.append (.handler effect table families outside)) = none := by
  rw [select_append, passed, if_pos rfl]
  simp only [select, ↓reduceIte]
  rcases missing with absent | absent
  · simp only [absent]
    rfl
  · simp only [absent]
    cases lookup operation table <;> rfl

/-- For another effect, an outside selection retains its contract and gains
the inserted handler inside its capture. -/
theorem inserted_bypassed (passed : reaches effect front = true)
    (different : effect ≠ installed)
    (found : select effect operation outside = some (.handler captured tail contract modes)) :
    select effect operation (front.append (.handler installed table families outside)) =
      some (.handler (front.append (.handler installed table families captured)) tail contract modes) := by
  apply selected_outside (selected := .handler (.handler installed table families captured) tail contract modes) passed
  simp only [select, if_neg different, found, Option.map_some, Selection.prepend]

/-- If the selection was inside the preceding scope, insertion changes only
its waiting side. Capture, selected contract and mode families stay exact. -/
theorem inserted_after_selection (stopped : reaches effect front = false)
    (found : select effect operation front = some (.handler captured tail contract modes)) :
    select effect operation (front.append (.handler installed table families outside)) =
      some (.handler captured (tail.append (.handler installed table families outside)) contract modes) :=
  selected_inside stopped found

/-- Authenticate the new selected pieces against the actual hints by reusing
the existing lookup-to-cut theorem. All handler requirement annotations are
those already stored in the given whole scope. -/
theorem inserted_cut (frontHints : Hints front) (outsideHints : Hints outside)
    (passed : reaches effect front = true)
    (known : lookup operation table = some contract)
    (declared : lookupDependencies operation families = some modes) :
    ∃ saved : Hints (front.append (.handler effect table families .nil)), ∃ waiting : Hints outside,
      SourcePlannedCuts.Cut effect operation contract modes
        (frontHints.append (.handler (effect := effect) (table := table) (families := families) required outsideHints)) saved waiting :=
  SourcePlannedCuts.of_lookup _ (inserted_selected passed known declared)

theorem bypassed_cut (frontHints : Hints front) (outsideHints : Hints outside)
    (passed : reaches effect front = true) (different : effect ≠ installed)
    (found : select effect operation outside = some (.handler captured tail contract modes)) :
    ∃ saved : Hints (front.append (.handler installed table families captured)), ∃ waiting : Hints tail,
      SourcePlannedCuts.Cut effect operation contract modes
        (frontHints.append (.handler (effect := installed) (table := table) (families := families) required outsideHints)) saved waiting :=
  SourcePlannedCuts.of_lookup _ (inserted_bypassed passed different found)

theorem inside_cut (frontHints : Hints front) (outsideHints : Hints outside)
    (stopped : reaches effect front = false)
    (found : select effect operation front = some (.handler captured tail contract modes)) :
    ∃ saved : Hints captured, ∃ waiting : Hints (tail.append (.handler installed table families outside)),
      SourcePlannedCuts.Cut effect operation contract modes
        (frontHints.append (.handler (effect := installed) (table := table) (families := families) required outsideHints)) saved waiting :=
  SourcePlannedCuts.of_lookup _ (inserted_after_selection stopped found)

/-- The local capture guard depends on the exact capture, contract and modes,
not on the waiting scope. Pending source in that scope remains a separate
preservation obligation. -/
theorem guard_same_capture
    (beforeFound : select effect operation before = some (.handler captured waiting contract modes))
    (afterFound : select effect operation after = some (.handler captured nextWaiting contract modes))
    (checked : CaptureGuard outward before effect operation) : CaptureGuard outward after effect operation := by
  cases checked with
  | builtin actual => cases Option.some.inj (beforeFound.symm.trans actual)
  | handler actual permission row body closing =>
      cases Option.some.inj (beforeFound.symm.trans actual)
      exact .handler afterFound permission row body closing

theorem inside_guard_transport (stopped : reaches effect front = false)
    (found : select effect operation front = some (.handler captured waiting contract modes))
    (checked : CaptureGuard outward (front.append before) effect operation) :
    CaptureGuard outward (front.append after) effect operation :=
  guard_same_capture (selected_inside stopped found) (selected_inside stopped found) checked

namespace Examples

private def F : Instance := .user 4 []
private def G : Instance := .user 5 []
private def table := SourceDependencyCapture.Examples.resumeTable
private def families := SourceDependencyCapture.Examples.resumeDependencies
private def contract : ClauseContract := ⟨false, some [], some []⟩
private def modes := (some SourceDependencyCapture.Examples.resumeFamily, some SourceDependencyCapture.Examples.resumeFamily)
private def saved : Scope := .cleanup [.cell 7] .pure (.cell 7 .nil)
private def front : Scope := .plain .pure (.live 9 saved .nil)
private def outside : Scope := .handler F table families (.cell 8 .nil)

theorem exposed_intercepted :
    select F 0 (front.append (.handler F table families outside)) =
      some (.handler (front.append (.handler F table families .nil)) outside contract modes) :=
  inserted_selected rfl rfl rfl

theorem outside_capture_extended :
    select F 0 (front.append (.handler G [] [] outside)) =
      some (.handler (front.append (.handler G [] [] (.handler F table families .nil)))
        (.cell 8 .nil) contract modes) :=
  inserted_bypassed rfl (by decide) rfl

theorem inner_waiting_extended :
    select F 0 ((front.append (.handler F table families (.cell 8 .nil))).append (.handler G [] [] .nil)) =
      some (.handler (front.append (.handler F table families .nil))
        (.cell 8 (.handler G [] [] .nil)) contract modes) :=
  selected_inside (selected := .handler (front.append (.handler F table families .nil)) (.cell 8 .nil) contract modes) rfl rfl

theorem missing_inserted_blocks_old : select F 0 (front.append (.handler F [] [] outside)) = none :=
  inserted_missing rfl (Or.inl rfl)

theorem missing_inner_blocks_inserted :
    select F 0 ((front.append (.handler F [] [] .nil)).append (.handler F table families outside)) = none :=
  blocked_inside rfl rfl

theorem builtin_blocks_inserted :
    select (.cell 7) 0 ((Scope.cell 7 front).append (.handler (.cell 7) table families outside)) = some (.builtin 7) :=
  selected_inside (selected := .builtin 7) rfl rfl

theorem dormant_provider_does_not_block :
    select (.cell 7) 0 (front.append (.handler (.cell 7) table families outside)) =
      some (.handler (front.append (.handler (.cell 7) table families .nil)) outside contract modes) :=
  inserted_selected rfl rfl rfl

open SourceDependencyCapture.Examples in
/-- Reuse the established protected-capture counterexample: exact selection
of a disposing handler does not establish permission to capture running
completion. The two observations remain independently checked. -/
theorem selected_but_protected :
    select effectE 0 (.running surviving) =
      some (.handler (.running (.cleanup [effectF] callback (handlerE .nil))) (handlerF .nil)
        ⟨true, some [], none⟩ (some disposeFamily, none)) ∧
      checkCapture [effectF] (.running surviving) effectE 0 = false := by
  constructor
  · exact inserted_selected (front := .running (.cleanup [effectF] callback .nil))
      (outside := handlerF .nil) (table := disposeTable) (families := disposeDependencies) rfl rfl rfl
  · exact running_completion_rejected

end Examples

end Ash.OneShot.SourceHandlerSelection

#print axioms Ash.OneShot.SourceHandlerSelection.select_append
#print axioms Ash.OneShot.SourceHandlerSelection.selected_outside
#print axioms Ash.OneShot.SourceHandlerSelection.selected_inside
#print axioms Ash.OneShot.SourceHandlerSelection.blocked_inside
#print axioms Ash.OneShot.SourceHandlerSelection.inserted_selected
#print axioms Ash.OneShot.SourceHandlerSelection.inserted_missing
#print axioms Ash.OneShot.SourceHandlerSelection.inserted_bypassed
#print axioms Ash.OneShot.SourceHandlerSelection.inserted_after_selection
#print axioms Ash.OneShot.SourceHandlerSelection.inserted_cut
#print axioms Ash.OneShot.SourceHandlerSelection.bypassed_cut
#print axioms Ash.OneShot.SourceHandlerSelection.inside_cut
#print axioms Ash.OneShot.SourceHandlerSelection.guard_same_capture
#print axioms Ash.OneShot.SourceHandlerSelection.inside_guard_transport
#print axioms Ash.OneShot.SourceHandlerSelection.Examples.exposed_intercepted
#print axioms Ash.OneShot.SourceHandlerSelection.Examples.outside_capture_extended
#print axioms Ash.OneShot.SourceHandlerSelection.Examples.inner_waiting_extended
#print axioms Ash.OneShot.SourceHandlerSelection.Examples.missing_inserted_blocks_old
#print axioms Ash.OneShot.SourceHandlerSelection.Examples.missing_inner_blocks_inserted
#print axioms Ash.OneShot.SourceHandlerSelection.Examples.builtin_blocks_inserted
#print axioms Ash.OneShot.SourceHandlerSelection.Examples.dormant_provider_does_not_block
#print axioms Ash.OneShot.SourceHandlerSelection.Examples.selected_but_protected
