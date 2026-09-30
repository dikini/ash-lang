import ResourceRequirements

/-! Adding a builtin interpretation can remove outward requests. Preserving a
sublist of the checked row removes the hidden-name exclusion needed only for
exact row equality. Owner phases and invocation selection remain unchanged. -/
namespace Ash.OneShot.ProtectionResiduals
open ProtectionContracts

/-- Residualization respects deletion of input requests. Reuse its existing
append law rather than reprove interpretation of each handler constructor. -/
theorem residual_sublist (included : smaller.Sublist larger)
    (evaluated : residualize context larger = some output) :
    ∃ next, residualize context smaller = some next ∧ next.Sublist output := by
  induction included generalizing output with
  | slnil => exact ⟨[], residual_empty context, List.nil_sublist _⟩
  | @cons first second request included ih =>
      have split : merge (residualize context [request]) (residualize context second) = some output := by
        simpa only [← residual_rows_append, List.singleton_append] using evaluated
      cases left : residualize context [request] with
      | none => simp [left, merge] at split
      | some leftRow => cases right : residualize context second with
        | none => simp [right, merge] at split
        | some rightRow =>
          simp only [left, right, merge, Option.some.injEq] at split
          subst output
          obtain ⟨next, checked, smaller⟩ := ih right
          exact ⟨next, checked, smaller.trans (List.sublist_append_right _ _)⟩
  | @cons_cons first second request included ih =>
      have split : merge (residualize context [request]) (residualize context second) = some output := by
        simpa only [← residual_rows_append, List.singleton_append] using evaluated
      cases left : residualize context [request] with
      | none => simp [left, merge] at split
      | some leftRow => cases right : residualize context second with
        | none => simp [right, merge] at split
        | some rightRow =>
          simp only [left, right, merge, Option.some.injEq] at split
          subst output
          obtain ⟨next, checked, smaller⟩ := ih right
          refine ⟨leftRow ++ next, ?_, (List.Sublist.refl _).append smaller⟩
          change residualize context ([request] ++ first) = some (leftRow ++ next)
          rw [residual_rows_append, left, checked]
          rfl

end Ash.OneShot.ProtectionResiduals

namespace Ash.OneShot.ResourceRequirements
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked Store evaluate)
open OwnerPhaseTransitions (Phases spendAll)

/-- A builtin inserted at any exact interpretation position preserves checking
and may narrow the outward row, even when that row mentions its identity. -/
theorem export_insert_builtin_sublist
    (exported : OwnerSource.exportAt (front ++ receiving) before raw = some row) :
    ∃ next, OwnerSource.exportAt (front ++ .ordinary (.builtin identity) :: receiving) before raw = some next ∧
      next.Sublist row := by
  simp only [OwnerSource.exportAt, OwnerPhaseTransitions.project_append, residual_append] at exported ⊢
  cases prefixRow : residualize (OwnerPhaseTransitions.project front before) raw with
  | none => simp [prefixRow] at exported
  | some exposed =>
      have checked : residualize (OwnerPhaseTransitions.project receiving before) exposed = some row := by
        simpa only [prefixRow] using exported
      have included : (CallableProtection.outsideCell identity exposed).Sublist exposed := List.filter_sublist
      obtain ⟨next, checkedNext, smaller⟩ := residual_sublist included checked
      refine ⟨next, ?_, smaller⟩
      simpa only [prefixRow, OwnerPhaseTransitions.project, residual_builtin] using checkedNext

/-- Traverse the existing successful requirement derivation, retaining its
owner demand, store lookups and one-shot phase checks. Only its row may shrink. -/
theorem checked_insert_builtin_sublist
    (checked : Checked store original before requirements row)
    (split : original = front ++ receiving) :
    ∃ next, Checked store (front ++ .ordinary (.builtin identity) :: receiving) before requirements next ∧
      next.Sublist row := by
  induction checked generalizing front receiving with
  | request exported =>
      obtain ⟨next, preserved, smaller⟩ := export_insert_builtin_sublist (identity := identity)
        (front := _ ++ front) (receiving := receiving) (by simpa only [split, List.append_assoc] using exported)
      exact ⟨next, .request (by simpa only [List.append_assoc] using preserved), smaller⟩
  | retire ready => exact ⟨[], .retire ready, .refl _⟩
  | spent consumed => exact ⟨[], .spent consumed, .refl _⟩
  | invoke known ready selection next ih =>
      rename_i key demand body phases nearer current waiting output
      obtain ⟨nextRow, preserved, smaller⟩ := ih (front := nearer ++ front) (receiving := receiving)
        (by simp only [split, List.append_assoc])
      obtain ⟨waiting, selected⟩ := selection_insert_builtin (identity := identity) (front := _ ++ front)
        (receiving := receiving) (by simpa only [split, List.append_assoc] using selection)
      exact ⟨nextRow, .invoke known ready (by simpa only [List.append_assoc] using selected)
        (by simpa only [List.append_assoc] using preserved), smaller⟩
  | sequence first second ihFirst ihSecond =>
      obtain ⟨left, leftChecked, leftSublist⟩ := ihFirst split
      obtain ⟨right, rightChecked, rightSublist⟩ := ihSecond split
      exact ⟨left ++ right, .sequence leftChecked rightChecked, leftSublist.append rightSublist⟩
  | emitAfter body exported ih =>
      obtain ⟨left, leftChecked, leftSublist⟩ := ih split
      obtain ⟨right, rightChecked, rightSublist⟩ := export_insert_builtin_sublist (identity := identity)
        (front := _ ++ front) (receiving := receiving) (by simpa only [split, List.append_assoc] using exported)
      exact ⟨left ++ right, .emitAfter leftChecked (by simpa only [List.append_assoc] using rightChecked),
        leftSublist.append rightSublist⟩
  | choice first second ihFirst ihSecond =>
      obtain ⟨left, leftChecked, leftSublist⟩ := ihFirst split
      obtain ⟨right, rightChecked, rightSublist⟩ := ihSecond split
      exact ⟨left ++ right, .choice leftChecked rightChecked, leftSublist.append rightSublist⟩

/-- Resource opening needs no hidden-name exclusion when its output row may
narrow. Freshness for resource ownership and source types remains separate. -/
theorem checked_open_resource_sublist
    (checked : Checked store receiving before closed row)
    (hidden : Hides identity opened closed) :
    ∃ next, Checked store (.ordinary (.builtin identity) :: receiving) before opened next ∧
      next.Sublist row := by
  obtain ⟨next, preserved, smaller⟩ := checked_insert_builtin_sublist checked (front := []) rfl (identity := identity)
  refine ⟨next, RecursiveRequirements.evaluate_sound ?_, smaller⟩
  rw [evaluate_hidden hidden]
  exact RecursiveRequirements.checked_complete preserved

namespace Examples

/-- The existing exact-row freshness example succeeds without exclusion when
its newly interpreted request is allowed to disappear from the output row. -/
theorem existing_request_is_interpreted :
    Checked records (.ordinary (.builtin 7) :: caller) (OwnerPhaseTransitions.available [5]) invocation [] := by
  have original := RecursiveRequirements.evaluate_sound allocation_freshness_matters.1
  obtain ⟨next, checked, included⟩ := checked_insert_builtin_sublist original (front := []) rfl (identity := 7)
  have empty : next = [] := Option.some.inj
    ((RecursiveRequirements.checked_complete checked).symm.trans allocation_freshness_matters.2.1)
  exact empty ▸ checked

end Examples

end Ash.OneShot.ResourceRequirements

#print axioms Ash.OneShot.ProtectionResiduals.residual_sublist
#print axioms Ash.OneShot.ResourceRequirements.export_insert_builtin_sublist
#print axioms Ash.OneShot.ResourceRequirements.checked_insert_builtin_sublist
#print axioms Ash.OneShot.ResourceRequirements.checked_open_resource_sublist

#print axioms Ash.OneShot.ResourceRequirements.Examples.existing_request_is_interpreted
