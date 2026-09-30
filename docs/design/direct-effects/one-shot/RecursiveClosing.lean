import RecursiveDispatch
import SourceClosingRows

/-!
Recursive requirements derived from actual one-shot closing plans. Source
callback contracts, release order and retirement entries determine the template.
Its checking result is independent of the continuation store; integration into
collected live-boundary disposal records remains a separate preservation join.
-/

namespace Ash.OneShot.RecursiveClosing
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open SourceTemplates (Segment)
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (Phases Trace spend spendAll)
open OwnerClosingSource (retirements)
open SourceClosingRows (Contents Rows)

/-- Callback annotations and retired-owner contracts come from the same retained
    source forest used by recursive resumption checking. -/
theorem plan_contents
    (source : Segment operations policy contracts tables world capture input output demand requirements records)
    (built : makePlan capture = some plan) : Contents operations policy contracts world plan := by
  induction capture generalizing input output demand requirements records plan with
  | nil => cases built; exact .nil
  | push frame rest ih => cases source with
      | push head tail => cases frame with
          | plain => exact ih tail built
          | handler => exact ih tail built
          | cell identity payload scope answer =>
              cases next : makePlan rest <;> simp [makePlan, next] at built
              case some suffix => subst plan; exact .release (ih tail next)
          | armed action => cases head with
              | armed scopeKnown callback annotation =>
                  cases next : makePlan rest <;> simp [makePlan, next] at built
                  case some suffix => subst plan; exact .invoke callback (ih tail next)
          | running | unwinding | closing | retiring => simp [makePlan] at built
  | live owner inputType answerType saved scope rest ihSaved ihRest => cases source with
      | live known inputAnnotation answerAnnotation scopeKnown held captured tail =>
          cases inside : makePlan saved <;> cases outside : makePlan rest <;> simp [makePlan, inside, outside] at built
          case some.some first second =>
            subst plan
            exact SourceClosingRows.contents_append (ihSaved captured inside) (.retire known (ihRest tail outside))
  | spent owner answer scope rest ih => cases source with
      | spent known answerAnnotation scopeKnown tail => exact ih tail built

theorem plan_rows
    (source : Segment operations policy contracts tables world capture input output demand requirements records)
    (built : makePlan capture = some plan) : ∃ raw, Rows operations policy contracts world plan raw :=
  SourceClosingRows.contents_rows (plan_contents source built)

theorem check_owners_cons (before : Phases) (owner : Nat) (rest : List Nat) :
    PhaseRechecking.checkOwners before (owner :: rest) =
      (decide (before owner = .available) && PhaseRechecking.checkOwners (spend before owner) rest) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, PhaseRechecking.check_owners_iff]
  constructor
  · intro trace
    cases trace with
    | cons ready remaining => exact ⟨ready, remaining⟩
  · rintro ⟨ready, remaining⟩
    exact .cons ready remaining

theorem evaluate_retire : evaluate store receiving before (.retire owner) =
    if before owner = .available then some [] else none := by
  simp [evaluate, RecursiveRequirements.evaluateFuel, PhaseRechecking.checkOwners]

theorem callback_evaluation (tables : CallableProtectionFrames.Tables) (scope : Scope) (plan : List CloseEntry)
    (fixed : Stack) (before : Phases) (latent : Footprint) :
    OwnerSource.exportAt (OwnerPhases.ofStack tables (closeControl scope plan) ++ OwnerPhases.ofStack tables fixed)
      before (qualify true latent) =
    OwnerSource.exportAt (OwnerPhases.ofStack tables fixed) before (DisposalProtection.callbackResidual plan latent) := by
  simp only [OwnerSource.exportAt, OwnerPhaseTransitions.project_append, OwnerClosingSource.plan_project]
  rw [residual_append, DisposalProtection.protected_row_residual]

/-- Closing templates follow the actual plan constructors. The footprint is
    derived from callback source and each callback's remaining plan suffix. -/
inductive PlanTemplate (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (scope : Scope) :
    (plan : List CloseEntry) → Footprint → Requirements (retirements plan) → Prop where
  | nil : PlanTemplate operations policy contracts tables world scope [] [] (.request [] [])
  | release (rest : PlanTemplate operations policy contracts tables world scope tail raw requirements) :
      PlanTemplate operations policy contracts tables world scope (.release identity payload :: tail) raw
        (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (closeControl scope tail))) requirements)
  | retire (known : contracts owner = some contract)
      (rest : PlanTemplate operations policy contracts tables world scope tail raw requirements) :
      PlanTemplate operations policy contracts tables world scope (.retire owner :: tail) raw
        (.sequence (.retire owner) requirements)
  | invoke (callback : SourceTemplates.ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent))
      (rest : PlanTemplate operations policy contracts tables world scope tail raw requirements) :
      PlanTemplate operations policy contracts tables world scope (.invoke action :: tail)
        (DisposalProtection.callbackResidual tail latent ++ raw)
        (.sequence ((Requirements.request [] (qualify true latent)).prepend (OwnerPhases.ofStack tables (closeControl scope tail))) requirements)

theorem rows_template (rows : Rows operations policy contracts world plan raw) :
    ∃ requirements, PlanTemplate operations policy contracts tables world scope plan raw requirements := by
  induction rows with
  | nil => exact ⟨_, .nil⟩
  | release rest ih => obtain ⟨requirements, template⟩ := ih; exact ⟨_, .release template⟩
  | retire known rest ih => obtain ⟨requirements, template⟩ := ih; exact ⟨_, .retire known template⟩
  | invoke callback rest ih => obtain ⟨requirements, template⟩ := ih; exact ⟨_, .invoke callback template⟩

theorem template_rows (template : PlanTemplate operations policy contracts tables world scope plan raw requirements) :
    Rows operations policy contracts world plan raw := by
  induction template with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke callback ih

theorem template_source (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope) :
    Segment operations policy contracts tables world (closeControl scope plan) .unit .unit (retirements plan) requirements [] := by
  induction template with
  | nil => exact .nil
  | release rest ih => exact .push (.cell scopeKnown (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]) rfl) ih
  | retire known rest ih => exact .push (.retiring known) ih
  | @invoke latent tail raw requirements action callback rest ih =>
      exact .push (.armed (action := { action with scope := scope, answer := .unit }) scopeKnown callback rfl) ih

/-- The store is arbitrary because the plan contains no continuation
    invocations; retirements are explicit owner transitions. -/
theorem template_evaluation (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (separate : ∀ owner ∈ retirements plan, owner ∉ OwnerPhases.names (OwnerPhases.ofStack tables fixed)) :
    evaluate store (OwnerPhases.ofStack tables fixed) before requirements =
      bif PhaseRechecking.checkOwners before (retirements plan) then
        OwnerSource.exportAt (OwnerPhases.ofStack tables fixed) before raw else none := by
  induction template generalizing before with
  | nil =>
      simp only [retirements, PhaseRechecking.checkOwners, List.nodup_nil, decide_true, List.all_nil,
        Bool.true_and, Bool.cond_true, RecursiveContexts.evaluate_request]
  | release rest ih =>
      simpa only [retirements, RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left] using ih separate
  | @retire owner contract tail raw requirements known rest ih =>
      have remaining := ih (before := spend before owner)
        (fun other member => separate other (List.mem_cons_of_mem owner member))
      have moved := OwnerClosingSource.suffix_spend (raw := raw) (before := before) (separate owner List.mem_cons_self)
      simp only [retirements, RecursiveRequirements.evaluate_sequence, evaluate_retire, spendAll]
      rw [remaining, moved, check_owners_cons]
      by_cases ready : before owner = .available
      · simp only [ready, if_true, decide_true, Bool.true_and, RecursiveRecomposition.merge_empty_left]
      · simp only [ready, if_false, decide_false, Bool.false_and, Bool.cond_false, merge]
  | @invoke latent tail raw requirements action callback rest ih =>
      simp only [retirements, RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveContexts.evaluate_request, spendAll]
      rw [callback_evaluation, ih separate, RecursiveContexts.export_rows]
      cases ready : PhaseRechecking.checkOwners before (retirements tail)
      · simp [merge]
      · simp

/-- A plan's template checks exactly its retirement availability and its ordered
    callback residual. -/
theorem plan_template
    (rows : Rows operations policy contracts world plan raw)
    (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope) :
    ∃ requirements : Requirements (retirements plan),
      Segment operations policy contracts tables world (closeControl scope plan) .unit .unit (retirements plan) requirements [] ∧
      ∀ store fixed before,
        (∀ owner ∈ retirements plan, owner ∉ OwnerPhases.names (OwnerPhases.ofStack tables fixed)) →
        evaluate store (OwnerPhases.ofStack tables fixed) before requirements =
          bif PhaseRechecking.checkOwners before (retirements plan) then
            OwnerSource.exportAt (OwnerPhases.ofStack tables fixed) before raw else none := by
  obtain ⟨requirements, template⟩ := rows_template rows
  exact ⟨requirements, template_source template scopeKnown, fun _ _ _ separate => template_evaluation template separate⟩


theorem plan_checked
    (rows : Rows operations policy contracts world plan raw)
    (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope)
    (transition : Trace before (retirements plan) after)
    (separate : ∀ owner ∈ retirements plan, owner ∉ OwnerPhases.names (OwnerPhases.ofStack tables fixed))
    (exported : OwnerSource.exportAt (OwnerPhases.ofStack tables fixed) before raw = some row) :
    ∃ requirements : Requirements (retirements plan),
      Segment operations policy contracts tables world (closeControl scope plan) .unit .unit (retirements plan) requirements [] ∧
      Checked store (OwnerPhases.ofStack tables fixed) before requirements row := by
  obtain ⟨requirements, source, evaluation⟩ := plan_template rows scopeKnown
  refine ⟨requirements, source, RecursiveRequirements.evaluate_sound ?_⟩
  rw [evaluation store fixed before separate, PhaseRechecking.trace_checked transition, Bool.cond_true, exported]

theorem plan_unprotected (built : makePlan capture = some plan) : ProtectionContexts.protectedMode capture.erase = false := by
  have same := CaptureInterfaces.plan_available capture
  simpa [built] using same.symm

/-- Successful plan construction from the retained source determines both its
    exact ownership accounting and its store-independent recursive template. -/
theorem captured_template
    (source : Segment operations policy contracts tables world capture input output demand requirements records)
    (built : makePlan capture = some plan)
    (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope) :
    ∃ (raw : Footprint) (body : Requirements (retirements plan)),
      Rows operations policy contracts world plan raw ∧
      Segment operations policy contracts tables world (closeControl scope plan) .unit .unit (retirements plan) body [] ∧
      (retirements plan).Perm (ownedTickets capture) ∧ ProtectionContexts.protectedMode capture.erase = false ∧
      ∀ store fixed before,
        (∀ owner ∈ retirements plan, owner ∉ OwnerPhases.names (OwnerPhases.ofStack tables fixed)) →
        evaluate store (OwnerPhases.ofStack tables fixed) before body =
          bif PhaseRechecking.checkOwners before (retirements plan) then
            OwnerSource.exportAt (OwnerPhases.ofStack tables fixed) before raw else none := by
  obtain ⟨raw, rows⟩ := plan_rows source built
  obtain ⟨body, materialized, evaluation⟩ := plan_template rows scopeKnown
  exact ⟨raw, body, rows, materialized, OwnerClosingSource.retirements_capture built, plan_unprotected built, evaluation⟩

theorem spend_available_prefix (unique : (first ++ rest).Nodup) :
    spendAll (OwnerPhaseTransitions.available (first ++ rest)) first = OwnerPhaseTransitions.available rest := by
  funext owner
  rw [OwnerPhaseTransitions.spendAll_at]
  by_cases member : owner ∈ first
  · have absent : owner ∉ rest := fun present => (List.nodup_append.mp unique).2.2 owner member owner present rfl
    simp only [member, if_true, OwnerPhaseTransitions.available, if_neg absent]
  · simp only [member, if_false, OwnerPhaseTransitions.available, List.mem_append, false_or]

/-- Retirement of a materialized plan leaves exactly its caller's owner map. -/
theorem materialized_transition
    (unique : (ownedTickets ((closeControl scope plan).append fixed)).Nodup) :
    Trace (OwnerPhaseTransitions.available (ownedTickets ((closeControl scope plan).append fixed)))
      (retirements plan) (OwnerPhaseTransitions.available (ownedTickets fixed)) := by
  have owners : ownedTickets ((closeControl scope plan).append fixed) = retirements plan ++ ownedTickets fixed := by
    rw [owned_tickets_append, ← OwnerClosingSource.retirements_actual scope plan]
  rw [owners] at unique ⊢
  rw [← spend_available_prefix unique]
  apply OwnerPhaseTransitions.trace_of_available (List.nodup_append.mp unique).1
  intro owner member
  simp only [OwnerPhaseTransitions.available, List.mem_append, member, true_or, if_true]

/-- Join an actual materialized plan to its surviving caller using the caller's
    collected store. No records for the plan's retired captures are needed. -/
theorem materialized_configuration
    (rows : Rows operations policy contracts world plan raw)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (tailSource : Segment operations policy contracts tables world fixed .unit output tailDemand tailRequirements records)
    (tailCheck : Checked records [] (OwnerPhaseTransitions.available (ownedTickets fixed)) tailRequirements tailRow)
    (unique : (ownedTickets ((closeControl scope plan).append fixed)).Nodup)
    (separate : ∀ owner ∈ retirements plan, owner ∉ OwnerPhases.names (OwnerPhases.ofStack tables fixed))
    (exported : OwnerSource.exportAt (OwnerPhases.ofStack tables fixed)
      (OwnerPhaseTransitions.available (ownedTickets ((closeControl scope plan).append fixed))) raw = some closingRow)
    (accepted : checkFootprint outside (closingRow ++ tailRow) = true) :
    SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope .unit
      ((closeControl scope plan).append fixed) output (retirements plan ++ tailDemand) (closingRow ++ tailRow) := by
  have transition := materialized_transition unique
  obtain ⟨requirements, source, checked⟩ := plan_checked (store := records) rows
    ⟨ticket, ScopedPorts.effect_scope_has_types scopeTyped⟩ transition separate exported
  obtain ⟨combined, pending, pendingCheck⟩ := RecursiveRecomposition.segment_append_checked source tailSource
    (by simpa only [List.append_nil] using checked)
    (OwnerPhaseTransitions.trace_result transition ▸ tailCheck)
  have current : SourceTemplates.Expression operations policy contracts world [] scope Environment.empty .unit .unit [] (.request [] []) := .stable .unit
  have currentCheck : Checked records []
      (OwnerPhaseTransitions.available (ownedTickets ((closeControl scope plan).append fixed)))
      ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables ((closeControl scope plan).append fixed))) [] :=
    Checked.request (row := []) (by simp [OwnerSource.exportAt, residual_empty])
  exact .checked (.checked (currentDemand := []) (pendingDemand := retirements plan ++ tailDemand) current scopeTyped (by simpa only [List.nil_append] using pending)) unique
    (by simpa only [List.nil_append] using Checked.sequence currentCheck pendingCheck) accepted


/-- Authenticate a disposal invocation with the actual plan's template. The
    selected owner and every retired nested owner are consumed exactly once.
    This constructs the entry's check; adding entries to collected live stores
    and proving raw-disposal preservation still require integration. -/
theorem disposal_check
    (rows : Rows operations policy contracts world plan raw) (built : makePlan capture = some plan)
    (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope)
    (ready : before owner = .available)
    (transition : Trace (spend before owner) (retirements plan) after)
    (separate : ∀ other ∈ retirements plan, other ∉ OwnerPhases.names (OwnerPhases.ofStack tables fixed))
    (exported : OwnerSource.exportAt (OwnerPhases.ofStack tables fixed) (spend before owner) raw = some row) :
    ∃ requirements : Requirements (retirements plan),
      Segment operations policy contracts tables world (closeControl scope plan) .unit .unit (retirements plan) requirements [] ∧
      (retirements plan).Perm (ownedTickets capture) ∧
      Checked ((⟨owner, .dispose⟩, ⟨retirements plan, requirements⟩) :: records)
        (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller fixed)) before
        (.invoke ⟨owner, .dispose⟩ (retirements plan) []) row := by
  obtain ⟨requirements, source, evaluation⟩ := plan_template (policy := policy) rows scopeKnown
  let store := (⟨owner, RecursiveRequirements.Mode.dispose⟩, ⟨retirements plan, requirements⟩) :: records
  have planCheck : Checked store (OwnerPhases.ofStack tables fixed) (spend before owner) requirements row := by
    apply RecursiveRequirements.evaluate_sound
    rw [evaluation store fixed (spend before owner) separate, PhaseRechecking.trace_checked transition, Bool.cond_true, exported]
  have callerCheck : Checked store
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller fixed))
      (spend before owner) requirements row := by
    apply RecursiveTransport.checked_transport planCheck (fun _ _ => rfl)
    simp only [OwnerPhases.ofStack, RecursiveTransport.normalize, OwnerPhaseTransitions.spend_self, if_true]
  refine ⟨requirements, source, OwnerClosingSource.retirements_capture built, ?_⟩
  apply Checked.invoke (body := requirements) (by simp [RecursiveRequirements.lookup])
    (PhaseRechecking.trace_checked (.cons ready transition))
    (by simpa only [List.nil_append, OwnerPhases.ofStack] using
      (OwnerPhases.Consumes.hit (owner := owner) (held := ProtectionContexts.protectedMode capture.erase)
        (rest := OwnerPhases.ofStack tables fixed)))
  simpa only [List.nil_append] using callerCheck


namespace Examples
open SharedClosingSource.Examples
  (operations policy contracts tables action latent callback_shared capture nested owner_known reversed reversed_rows)
open OwnerPhaseTransitions (available empty)

def capturedRequirements : Requirements [] :=
  .sequence ((Requirements.request [] (qualify true latent)).prepend
    (OwnerPhases.ofStack tables (.push (.cell 4 17 .none .unit) .nil)))
    (.sequence ((Requirements.request [] []).prepend []) (.request [] []))
def nestedPlan : List CloseEntry := [.invoke action, .release 4 17, .retire 19]

theorem captured_source : Segment operations policy contracts tables [4] capture .unit .unit [] capturedRequirements [] :=
  .push (.armed (action := action) ⟨.none, .none⟩ (.stable callback_shared) rfl)
    (.push (.cell ⟨.none, .none⟩ (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]) rfl) .nil)

theorem nested_source : Segment operations policy contracts tables [4] nested .unit .unit []
    (.sequence (.spent 19) (.request [] [])) [(⟨19, .resume⟩, ⟨[], capturedRequirements⟩)] :=
  .live owner_known rfl rfl ⟨.none, .none⟩ rfl captured_source .nil

theorem nested_built : makePlan nested = some nestedPlan := rfl

theorem nested_rows : Rows operations policy contracts [4] nestedPlan [] :=
  .invoke (action := action) (latent := latent) (.stable callback_shared) (.release (.retire owner_known .nil))

theorem nested_materialized : SourceTemplates.CheckedConfiguration operations policy contracts tables [4] [] .none .unit
    ((closeControl .none nestedPlan).append .nil) .unit [19] [] := by
  exact materialized_configuration (tailDemand := []) (tailRow := []) (closingRow := []) nested_rows .none .nil
    (Checked.request (raw := []) (nearer := []) (row := []) (by simp [OwnerSource.exportAt, residual_empty]))
    (by decide) (by intro owner member; exact List.not_mem_nil) (by simp [OwnerSource.exportAt, residual_empty]) (by decide)

theorem nested_disposal_invocation : ∃ requirements : Requirements [19],
    Segment operations policy contracts tables [4] (closeControl .none nestedPlan) .unit .unit [19] requirements [] ∧
    Checked ((⟨23, .dispose⟩, ⟨[19], requirements⟩) :: records)
      (OwnerPhases.ofStack tables (.live 23 .unit .unit nested .none .nil)) (available [23, 19])
      (.invoke ⟨23, .dispose⟩ [19] []) [] := by
  obtain ⟨requirements, source, ownership, checked⟩ := disposal_check (policy := policy) (tables := tables) (row := [])
    (inputType := Ty.unit) (answerType := Ty.unit) (caller := Execution.Scope.none) (fixed := Stack.nil)
    (before := available [23, 19]) (owner := 23)
    nested_rows nested_built (scope := Execution.Scope.none) ⟨.none, .none⟩ (by decide)
    (PhaseRechecking.check_owners_iff.mp (by decide))
    (by intro owner member; exact List.not_mem_nil) (by simp [OwnerSource.exportAt, residual_empty])
  exact ⟨requirements, source, checked⟩

theorem reversed_exports_missing_cell : ∃ requirements : Requirements [],
    Segment operations policy contracts tables [4] (closeControl .none reversed) .unit .unit [] requirements [] ∧
    (∀ store, evaluate store [] empty requirements = some [⟨.cell 4, 0, true⟩]) ∧
    checkFootprint [] [⟨.cell 4, 0, true⟩] = false := by
  obtain ⟨requirements, source, evaluation⟩ := plan_template (policy := policy) (tables := tables)
    (SourceClosingRows.from_legacy reversed_rows) (scope := Execution.Scope.none) ⟨.none, .none⟩
  refine ⟨requirements, source, ?_, by decide⟩
  intro store
  change @evaluate store (OwnerPhases.ofStack tables .nil) empty (retirements reversed) requirements = _
  exact evaluation store .nil empty (by intro owner member; exact List.not_mem_nil)

theorem duplicate_retirement_rejected : ∃ requirements : Requirements [19, 19],
    Segment operations policy contracts tables [4] (closeControl .none [.retire 19, .retire 19])
      .unit .unit [19, 19] requirements [] ∧
    ∀ store, evaluate store [] (available [19]) requirements = none := by
  have rows : Rows operations policy contracts [4] [.retire 19, .retire 19] [] := .retire owner_known (.retire owner_known .nil)
  obtain ⟨requirements, source, evaluation⟩ := plan_template (policy := policy) (tables := tables)
    rows (scope := Execution.Scope.none) ⟨.none, .none⟩
  refine ⟨requirements, source, ?_⟩
  intro store
  change @evaluate store (OwnerPhases.ofStack tables .nil) (available [19])
    (retirements [.retire 19, .retire 19]) requirements = _
  exact evaluation store .nil (available [19]) (by intro owner member; exact List.not_mem_nil)

end Examples

end Ash.OneShot.RecursiveClosing

#print axioms Ash.OneShot.RecursiveClosing.plan_contents
#print axioms Ash.OneShot.RecursiveClosing.plan_rows
#print axioms Ash.OneShot.RecursiveClosing.check_owners_cons
#print axioms Ash.OneShot.RecursiveClosing.evaluate_retire
#print axioms Ash.OneShot.RecursiveClosing.callback_evaluation
#print axioms Ash.OneShot.RecursiveClosing.rows_template
#print axioms Ash.OneShot.RecursiveClosing.template_rows
#print axioms Ash.OneShot.RecursiveClosing.template_source
#print axioms Ash.OneShot.RecursiveClosing.template_evaluation
#print axioms Ash.OneShot.RecursiveClosing.plan_template
#print axioms Ash.OneShot.RecursiveClosing.plan_checked
#print axioms Ash.OneShot.RecursiveClosing.plan_unprotected
#print axioms Ash.OneShot.RecursiveClosing.captured_template
#print axioms Ash.OneShot.RecursiveClosing.spend_available_prefix
#print axioms Ash.OneShot.RecursiveClosing.materialized_transition
#print axioms Ash.OneShot.RecursiveClosing.materialized_configuration
#print axioms Ash.OneShot.RecursiveClosing.disposal_check
#print axioms Ash.OneShot.RecursiveClosing.Examples.captured_source
#print axioms Ash.OneShot.RecursiveClosing.Examples.nested_source
#print axioms Ash.OneShot.RecursiveClosing.Examples.nested_built
#print axioms Ash.OneShot.RecursiveClosing.Examples.nested_rows
#print axioms Ash.OneShot.RecursiveClosing.Examples.nested_materialized
#print axioms Ash.OneShot.RecursiveClosing.Examples.nested_disposal_invocation
#print axioms Ash.OneShot.RecursiveClosing.Examples.reversed_exports_missing_cell
#print axioms Ash.OneShot.RecursiveClosing.Examples.duplicate_retirement_rejected
