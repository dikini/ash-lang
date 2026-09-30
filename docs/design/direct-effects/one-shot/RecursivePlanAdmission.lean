import RecursiveAllocation

/-!
Closing-template checking from its ordinary callback residual. Actual ownership
supplies retirement availability, while the surviving caller keeps its live
owners. Spent markers need not be absent from the caller's history.
-/

namespace Ash.OneShot.RecursivePlanAdmission
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked evaluate)
open RecursiveClosing (PlanTemplate)
open OwnerPhaseTransitions (Phases Trace available spend spendAll)
open OwnerClosingSource (retirements)

theorem caller_export
    (ready : ∀ owner ∈ activeTickets fixed, before owner = .available) :
    OwnerSource.exportAt (OwnerPhases.ofStack tables fixed) before raw =
      residualize (CallableProtectionFrames.contextOf tables fixed) raw := by
  unfold OwnerSource.exportAt
  rw [OwnerPhaseTransitions.project_agrees, OwnerPhases.project_stack]
  simpa only [OwnerPhaseTransitions.liveNames_stack] using ready

/-- The source-derived plan is checked by its ordinary ordered residual once
    the existing ownership trace establishes retirement and caller availability. -/
theorem template_checked
    (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (transition : Trace before (retirements plan) after)
    (callerReady : ∀ owner ∈ activeTickets fixed, after owner = .available)
    (exported : residualize (CallableProtectionFrames.contextOf tables fixed) raw = some row) :
    Checked store (OwnerPhases.ofStack tables fixed) before requirements row := by
  induction template generalizing before row with
  | nil =>
      have empty : row = [] := Option.some.inj ((residual_empty _).symm.trans exported) |>.symm
      subst row
      exact .request (by simp [OwnerSource.exportAt, residual_empty])
  | release rest ih =>
      exact .sequence (.request (row := []) (by simp [OwnerSource.exportAt, residual_empty]))
        (ih transition exported)
  | retire known rest ih =>
      cases transition with
      | cons ready remaining => exact .sequence (.retire ready) (ih remaining exported)
  | @invoke latent tail raw requirements action callback rest ih =>
      rw [residual_rows_append] at exported
      obtain ⟨callbackRow, tailRow, callbackExport, tailExport, rfl⟩ := PhaseRechecking.merge_split exported
      have readyBefore : ∀ owner ∈ activeTickets fixed, before owner = .available := by
        intro owner member
        exact RecursiveTransport.available_earlier
          (fun _ consumed => OwnerPhaseTransitions.trace_monotone transition consumed) (callerReady owner member)
      have checkedCallback : Checked store (OwnerPhases.ofStack tables fixed) before
          ((Requirements.request [] (qualify true latent)).prepend (OwnerPhases.ofStack tables (closeControl scope tail))) callbackRow := by
        apply RecursiveRequirements.checked_prepend_iff.mpr
        apply Checked.request
        simp only [List.nil_append, RecursiveClosing.callback_evaluation, caller_export readyBefore]
        exact callbackExport
      exact .sequence checkedCallback (ih transition tailExport)

theorem captured_retirement
    (built : makePlan capture = some plan)
    (unique : (ownedTickets (.live owner input answer capture caller fixed)).Nodup) :
    Trace (spend (available (ownedTickets (.live owner input answer capture caller fixed))) owner)
      (retirements plan) (available (ownedTickets fixed)) := by
  have captured := OwnerClosingSource.retirements_capture built
  have restUnique := (List.nodup_cons.mp unique).2
  have planned : (ownedTickets ((closeControl .none plan).append fixed)).Nodup := by
    rw [owned_tickets_append, ← OwnerClosingSource.retirements_actual]
    exact (captured.append_right _).symm.nodup restUnique
  have transition := RecursiveClosing.materialized_transition planned
  rw [owned_tickets_append, ← OwnerClosingSource.retirements_actual,
    OwnerPhaseTransitions.available_permutation (captured.append_right _)] at transition
  simpa only [ownedTickets, OwnerPhaseTransitions.spend_available_cons (List.nodup_cons.mp unique).1] using transition

theorem captured_evaluation
    (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (built : makePlan capture = some plan)
    (unique : (ownedTickets (.live owner input answer capture caller fixed)).Nodup)
    (exported : residualize (CallableProtectionFrames.contextOf tables fixed) raw = some row) :
    evaluate store (OwnerPhases.ofStack tables fixed)
      (spend (available (ownedTickets (.live owner input answer capture caller fixed))) owner) requirements = some row := by
  apply RecursiveRequirements.checked_complete
  apply template_checked template (captured_retirement built unique) _ exported
  intro actual member
  exact if_pos (active_tickets_owned fixed member)

/-- A declaration's upper row determines a successful actual closing export.
    Retirement checking remains the existing ownership proof. -/
theorem captured_bounded
    (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (built : makePlan capture = some plan)
    (unique : (ownedTickets (.live owner input answer capture caller fixed)).Nodup)
    (covered : EffectBounds.Covers upperRaw raw)
    (exported : residualize (CallableProtectionFrames.contextOf tables fixed) upperRaw = some upperRow) :
    ∃ actualRow,
      evaluate store (OwnerPhases.ofStack tables fixed)
        (spend (available (ownedTickets (.live owner input answer capture caller fixed))) owner) requirements = some actualRow ∧
      EffectBounds.Covers upperRow actualRow := by
  obtain ⟨actualRow, actualExport, actualBound⟩ := UniformClauseBounds.residual_coverage covered exported
  exact ⟨actualRow, captured_evaluation template built unique actualExport, actualBound⟩

theorem captured_bound_admitted
    (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (built : makePlan capture = some plan)
    (unique : (ownedTickets (.live owner input answer capture caller fixed)).Nodup)
    (covered : EffectBounds.Covers upperRaw raw)
    (admitted : checkFootprint (CallableProtectionFrames.contextOf tables fixed ++ outside) upperRaw = true) :
    ∃ actualRow,
      evaluate store (OwnerPhases.ofStack tables fixed)
        (spend (available (ownedTickets (.live owner input answer capture caller fixed))) owner) requirements = some actualRow ∧
      checkFootprint outside actualRow = true := by
  obtain ⟨upperRow, exported, accepted⟩ := residual_admitted_iff.mp admitted
  obtain ⟨actualRow, evaluated, actualBound⟩ := captured_bounded template built unique covered exported
  exact ⟨actualRow, evaluated, EffectBounds.check_covered accepted actualBound⟩

/-- Structural effect admission supplies a closing row and its successful
    template check; retirement phases are not an additional source premise. -/
theorem captured_admitted
    (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (built : makePlan capture = some plan)
    (unique : (ownedTickets (.live owner input answer capture caller fixed)).Nodup)
    (admitted : ∀ request ∈ raw,
      Admitted (CallableProtectionFrames.contextOf tables fixed ++ outside) request) :
    ∃ row,
      evaluate store (OwnerPhases.ofStack tables fixed)
        (spend (available (ownedTickets (.live owner input answer capture caller fixed))) owner) requirements = some row ∧
      checkFootprint outside row = true := by
  exact captured_bound_admitted template built unique (EffectBounds.covers_refl raw)
    (check_footprint_iff.mpr admitted)

namespace Examples
open SharedClosingSource.Examples (operations policy contracts tables nested)
open RecursiveClosing.Examples (nestedPlan nested_rows nested_built)

/-- Reuse the plan with a cell-reading cleanup and a nested retirement. Its
    actual owner map now supplies all phase and retirement premises. -/
theorem nested_closing_checked :
    ∃ requirements,
      PlanTemplate operations policy contracts tables [4] .none nestedPlan [] requirements ∧
      evaluate [] (OwnerPhases.ofStack tables .nil)
        (spend (available (ownedTickets (.live 23 .unit .unit nested .none .nil))) 23) requirements = some [] := by
  obtain ⟨requirements, template⟩ := RecursiveClosing.rows_template (scope := .none) (tables := tables) nested_rows
  exact ⟨requirements, template, captured_evaluation template nested_built (by decide) (by rfl)⟩

end Examples

end Ash.OneShot.RecursivePlanAdmission

#print axioms Ash.OneShot.RecursivePlanAdmission.caller_export
#print axioms Ash.OneShot.RecursivePlanAdmission.template_checked
#print axioms Ash.OneShot.RecursivePlanAdmission.captured_retirement
#print axioms Ash.OneShot.RecursivePlanAdmission.captured_evaluation
#print axioms Ash.OneShot.RecursivePlanAdmission.captured_admitted
#print axioms Ash.OneShot.RecursivePlanAdmission.Examples.nested_closing_checked

#print axioms Ash.OneShot.RecursivePlanAdmission.captured_bounded
#print axioms Ash.OneShot.RecursivePlanAdmission.captured_bound_admitted
