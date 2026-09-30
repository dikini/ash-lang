import RecursiveDispatch
import ClosingAdmission

/-! Connect exact structural request preservation to protected cleanup-row
interpretation. The common outside stack retains the actual handler tables.
Distinct activations prevent a removed handler from being confused with an
outside handler carrying the same activation. No interpretation is exchanged. -/
namespace Ash.OneShot.ProtectedClosingRows
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open CallableProtectionFrames (Tables pushContext)
open OwnerPhaseTransitions (Phases)

def phaseContext (tables : Tables) (phases : Phases) (stack : Stack) : ProtectionContracts.Context :=
  OwnerPhaseTransitions.project (OwnerPhases.ofStack tables stack) phases

theorem phase_context_push (tables : Tables) (phases : Phases) (frame : ExecFrame) (stack : Stack) :
    phaseContext tables phases (.push frame stack) = pushContext tables frame (phaseContext tables phases stack) := by
  cases frame <;> rfl

/-- A live boundary may already be consumed. Protected callback requests are
unchanged in either phase, without pretending the owner is still available. -/
theorem phase_context_live_request :
    residualize (phaseContext tables phases (.live owner input answer saved scope rest)) [⟨requested, operation, true⟩] =
      residualize (phaseContext tables phases rest) [⟨requested, operation, true⟩] := by
  by_cases ready : phases owner = .available
  · simp [phaseContext, OwnerPhases.ofStack, OwnerPhaseTransitions.project, ready,
      residualize, DisposalProtection.through_barrier, qualify]
  · simp [phaseContext, OwnerPhases.ofStack, OwnerPhaseTransitions.project, ready]

/-- Source resolution supplies membership in the existing activation ledger. -/
theorem source_activation_member {control : Control}
    (resolved : control.resolve requested = some (.source activation)) : activation ∈ control.activations := by
  induction control with
  | nil => cases resolved
  | push frame rest ih =>
      cases first : frame.resolve requested with
      | none =>
          exact List.mem_append_right _ (ih (by simpa only [Control.resolve, first] using resolved))
      | some target =>
          have same : target = .source activation := by simpa only [Control.resolve, first, Option.some.injEq] using resolved
          cases same
          apply List.mem_append_left
          cases kind : frame.kind <;> simp_all [Frame.resolve, Frame.activation]
  | live owner input answer saved rest ihSaved ihRest => exact List.mem_append_right _ (ihRest resolved)
  | spent owner answer rest ih => exact ih resolved

/-- An unresolved prefix cannot alter a protected request. Reuse the existing
frame-miss residual theorem; live barriers cannot add further protection. -/
theorem unresolved_prefix {front tail : Stack}
    (unresolved : front.erase.resolve requested = none) :
    residualize (phaseContext tables phases (front.append tail)) [⟨requested, operation, true⟩] =
      residualize (phaseContext tables phases tail) [⟨requested, operation, true⟩] := by
  induction front with
  | nil => rfl
  | push frame rest ih =>
      have first : frame.erase.resolve requested = none := by
        cases found : frame.erase.resolve requested <;> simp_all [Stack.erase, Control.resolve]
      have next : rest.erase.resolve requested = none := by simpa only [Stack.erase, Control.resolve, first] using unresolved
      have missed := RecursiveDispatch.residual_push_miss (incoming := true) (operation := operation) tables frame (phaseContext tables phases (rest.append tail))
        (ScopedTyping.frame_target_miss_of_resolution_none frame.erase first)
      simpa only [Stack.append, phase_context_push, Bool.true_or, ih next] using missed
  | live owner input answer saved scope rest ihSaved ihRest =>
      simpa only [Stack.append, phase_context_live_request] using ihRest unresolved
  | spent owner answer scope rest ih => exact ih unresolved

/-- Builtin interpretation discharges the request regardless of intervening
barriers; source handlers still block builtin lookup. -/
theorem builtin_residual
    (resolved : stack.erase.resolve requested = some (.builtin identity)) :
    residualize (phaseContext tables phases stack) [⟨requested, operation, true⟩] = some [] := by
  induction stack with
  | nil => cases resolved
  | push frame rest ih =>
      cases first : frame.erase.resolve requested with
      | none =>
          have next : rest.erase.resolve requested = some (.builtin identity) := by
            simpa only [Stack.erase, Control.resolve, first] using resolved
          have missed := RecursiveDispatch.residual_push_miss (incoming := true) (operation := operation) tables frame (phaseContext tables phases rest)
            (ScopedTyping.frame_target_miss_of_resolution_none frame.erase first)
          simpa only [phase_context_push, Bool.true_or, ih next] using missed
      | some target =>
          have same : target = .builtin identity := by simpa only [Stack.erase, Control.resolve, first, Option.some.injEq] using resolved
          cases same
          cases frame <;> simp_all [ExecFrame.erase, PlainData.erase, HandlerData.erase, ActionData.erase,
            closeFrame, CloseItem.frame, Frame.resolve]
          all_goals
            rcases first with ⟨rfl, rfl⟩
            simp [phase_context_push, pushContext, residualize, throughLayer, demandThrough, merge, residual_empty]
  | live owner input answer saved scope rest ihSaved ihRest =>
      simpa only [phase_context_live_request] using ihRest resolved
  | spent owner answer scope rest ih => exact ih resolved

/-- A source target absent from a prefix must be selected in the common tail. -/
theorem source_passes_prefix {front tail : Control}
    (resolved : (front.append tail).resolve requested = some (.source activation))
    (absent : activation ∉ front.activations) : front.resolve requested = none := by
  cases first : front.resolve requested with
  | none => rfl
  | some target =>
      have same : target = .source activation := by simpa only [resolve_append, first, Option.some.injEq] using resolved
      cases same
      exact False.elim (absent (source_activation_member first))

/-- Exact target preservation gives exact protected-row interpretation when
both stacks share their surviving outside handlers. The names premise rules
out confusing a removed source handler with one in that common outside. -/
theorem same_target_residual {front surviving tail : Stack}
    (noHandlers : surviving.erase.activations = [])
    (separated : ∀ activation ∈ front.erase.activations, activation ∉ tail.erase.activations)
    (original : (front.append tail).erase.resolve requested = some target)
    (after : (surviving.append tail).erase.resolve requested = some target) :
    residualize (phaseContext tables phases (front.append tail)) [⟨requested, operation, true⟩] =
      residualize (phaseContext tables phases (surviving.append tail)) [⟨requested, operation, true⟩] := by
  cases target with
  | builtin identity => rw [builtin_residual original, builtin_residual after]
  | source activation =>
      have absentAfter : activation ∉ surviving.erase.activations := by simp [noHandlers]
      have passesAfter := source_passes_prefix (by simpa only [erase_append] using after) absentAfter
      have tailTarget : tail.erase.resolve requested = some (.source activation) := by
        simpa only [erase_append, resolve_append, passesAfter] using after
      have inTail := source_activation_member tailTarget
      have absentBefore : activation ∉ front.erase.activations := fun present => separated _ present inTail
      have passesBefore := source_passes_prefix (by simpa only [erase_append] using original) absentBefore
      exact (unresolved_prefix passesBefore).trans (unresolved_prefix passesAfter).symm

/-- Lift exact singleton interpretation to the entire callback footprint using
the existing residual append law. No source annotation uniqueness is needed. -/
theorem same_requests_residual {front surviving tail : Stack}
    (noHandlers : surviving.erase.activations = [])
    (separated : ∀ activation ∈ front.erase.activations, activation ∉ tail.erase.activations)
    (same : SameRequests (front.append tail).erase (surviving.append tail).erase (row.map Demand.effect)) :
    residualize (phaseContext tables phases (front.append tail)) (qualify true row) =
      residualize (phaseContext tables phases (surviving.append tail)) (qualify true row) := by
  induction row with
  | nil => simp [qualify, residual_empty]
  | cons request rest ih =>
      cases same with
      | cons _ _ target original after remaining =>
          have head := same_target_residual (tables := tables) (phases := phases) (operation := request.operation) noHandlers separated original after
          have splitRow : qualify true (request :: rest) = [⟨request.effect, request.operation, true⟩] ++ qualify true rest := by
            simp [qualify]
          rw [splitRow, residual_rows_append, residual_rows_append, head, ih remaining]

/-- A successful structural closing check for the actual callback footprint
therefore preserves its exported effect row, including local builtin discharge. -/
theorem closing_callback_residual {front tail : Stack}
    (separated : ∀ activation ∈ front.erase.activations, activation ∉ tail.erase.activations)
    (same : SameRequests (front.append tail).erase ((closeControl scope plan).append tail).erase (latent.map Demand.effect)) :
    residualize (phaseContext tables phases (front.append tail)) (qualify true latent) =
      residualize (phaseContext tables phases tail) (DisposalProtection.callbackResidual plan latent) := by
  have noHandlers : (closeControl scope plan).erase.activations = [] := by
    rw [close_control_erases, plan_control_activations]
  rw [same_requests_residual noHandlers separated same]
  unfold phaseContext
  rw [OwnerPhases.stack_append, OwnerPhaseTransitions.project_append, OwnerClosingSource.plan_project,
    residual_append, DisposalProtection.protected_row_residual]

theorem same_requests_member
    (same : SameRequests original surviving requests) (member : requested ∈ requests) :
    ∃ target, original.resolve requested = some target ∧ surviving.resolve requested = some target := by
  induction same with
  | nil => cases member
  | cons request rest target before after remaining ih =>
      rcases List.mem_cons.mp member with equal | next
      · cases equal; exact ⟨target, before, after⟩
      · exact ih next

theorem same_requests_subset
    (same : SameRequests original surviving requests) (included : actual ⊆ requests) :
    SameRequests original surviving actual := by
  induction actual with
  | nil => exact .nil
  | cons requested rest ih =>
      obtain ⟨target, before, after⟩ := same_requests_member same (included List.mem_cons_self)
      exact .cons requested rest target before after (ih (fun _ member => included (List.mem_cons_of_mem _ member)))

/-- Derive the separation premise from the existing distinct-name invariant,
then use the existing executable request checker for the exact callback row. -/
theorem checked_callback_residual {front tail : Stack}
    (names : DistinctNames (front.append tail).erase)
    (checked : ClosingAdmission.checkRequests (front.append tail).erase
      ((closeControl scope plan).append tail).erase (latent.map Demand.effect) = true) :
    residualize (phaseContext tables phases (front.append tail)) (qualify true latent) =
      residualize (phaseContext tables phases tail) (DisposalProtection.callbackResidual plan latent) := by
  apply closing_callback_residual _ (ClosingAdmission.check_requests_iff.mp checked)
  have unique := names.2
  rw [erase_append, activations_append] at unique
  intro activation first second
  exact (List.nodup_append.mp unique).2.2 activation first activation second rfl

/-- An existing action check suffices when the declared requests cover the
actual callback footprint. That coverage is an explicit source-type obligation. -/
theorem checked_action_residual {front tail : Stack} {action : ActionData}
    (names : DistinctNames (front.append tail).erase)
    (checked : ClosingAdmission.checkAction action.erase front.erase tail.erase tail.erase
      (plan.map CloseEntry.erase) = true)
    (covered : ∀ request ∈ latent, request.effect ∈ action.requests) :
    residualize (phaseContext tables phases (front.append tail)) (qualify true latent) =
      residualize (phaseContext tables phases tail) (DisposalProtection.callbackResidual plan latent) := by
  apply checked_callback_residual (scope := .none) names
  apply ClosingAdmission.check_requests_iff.mpr
  have requests := (ClosingAdmission.check_action_iff.mp checked).2.2
  have actual : SameRequests (front.append tail).erase ((closeControl .none plan).append tail).erase action.requests := by
    simpa only [erase_append, close_control_erases, ActionData.erase] using requests
  apply same_requests_subset actual
  intro requested member
  obtain ⟨request, present, rfl⟩ := List.mem_map.mp member
  exact covered request present

/-- Recover the callback's exact closing export from its existing normal
requirement check at the same owner phases. -/
theorem checked_action_export {front tail : Stack} {action : ActionData}
    (names : DistinctNames (front.append tail).erase)
    (checked : ClosingAdmission.checkAction action.erase front.erase tail.erase tail.erase
      (plan.map CloseEntry.erase) = true)
    (covered : ∀ request ∈ latent, request.effect ∈ action.requests)
    (normal : RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail) phases
      ((RecursiveRequirements.Requirements.request [] (qualify true latent)).prepend (OwnerPhases.ofStack tables front)) row) :
    OwnerSource.exportAt (OwnerPhases.ofStack tables tail) phases (DisposalProtection.callbackResidual plan latent) = some row := by
  have same := checked_action_residual (tables := tables) (phases := phases) names checked covered
  have exported := RecursiveRequirements.checked_complete (RecursiveRequirements.checked_prepend_iff.mp normal)
  have original : residualize (phaseContext tables phases (front.append tail)) (qualify true latent) = some row := by
    simpa only [RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel,
      OwnerSource.exportAt, phaseContext, OwnerPhases.stack_append, List.nil_append] using exported
  exact same.symm.trans original

/-- A pending armed callback contributes a component of the captured effect
budget. Its checked closing interpretation inherits that same component. -/
theorem checked_armed_budget {front tail : Stack} {action : ActionData}
    (names : DistinctNames (front.append tail).erase)
    (checked : ClosingAdmission.checkAction action.erase front.erase tail.erase tail.erase
      (plan.map CloseEntry.erase) = true)
    (covered : ∀ request ∈ latent, request.effect ∈ action.requests)
    (normal : RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail) phases
      (.sequence ((RecursiveRequirements.Requirements.request [] (qualify true latent)).prepend (OwnerPhases.ofStack tables front)) pending) row) :
    ∃ callbackRow,
      OwnerSource.exportAt (OwnerPhases.ofStack tables tail) phases (DisposalProtection.callbackResidual plan latent) = some callbackRow ∧
      EffectBounds.Covers row callbackRow := by
  obtain ⟨callbackRow, pendingRow, callback, rest, same⟩ := RecursiveRequirements.checked_sequence_parts normal
  exact ⟨callbackRow, checked_action_export names checked covered callback, same ▸ List.subset_append_left _ _⟩

end Ash.OneShot.ProtectedClosingRows

#print axioms Ash.OneShot.ProtectedClosingRows.source_activation_member
#print axioms Ash.OneShot.ProtectedClosingRows.unresolved_prefix
#print axioms Ash.OneShot.ProtectedClosingRows.builtin_residual
#print axioms Ash.OneShot.ProtectedClosingRows.source_passes_prefix

#print axioms Ash.OneShot.ProtectedClosingRows.same_target_residual
#print axioms Ash.OneShot.ProtectedClosingRows.same_requests_residual
#print axioms Ash.OneShot.ProtectedClosingRows.closing_callback_residual

#print axioms Ash.OneShot.ProtectedClosingRows.same_requests_member
#print axioms Ash.OneShot.ProtectedClosingRows.same_requests_subset
#print axioms Ash.OneShot.ProtectedClosingRows.checked_callback_residual
#print axioms Ash.OneShot.ProtectedClosingRows.checked_action_residual

#print axioms Ash.OneShot.ProtectedClosingRows.phase_context_push
#print axioms Ash.OneShot.ProtectedClosingRows.phase_context_live_request

#print axioms Ash.OneShot.ProtectedClosingRows.checked_action_export
#print axioms Ash.OneShot.ProtectedClosingRows.checked_armed_budget
