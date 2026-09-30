import RecursiveRecomposition
import SourceCallableSubstitution

/-!
Closed substitution and ordinary reductions for the recursive source judgment.
These results retain the actual continuation templates and receiving context;
they do not assume a successful check of the successor expression.
-/

namespace Ash.OneShot.RecursiveExpressions
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open SourceTemplates (Expression)
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (Phases spendAll)

theorem substitution
    (source : Expression operations policy contracts world allowed scope (environment.extend name input) code result demand requirements)
    (replacement : SourceTemplates.ValueSummary operations policy contracts world environment allowed value input) (closed : ClosedValue value) :
    Expression operations policy contracts world allowed scope environment (code.subst name value) result demand requirements :=
  SourceCallableSubstitution.substitution source replacement closed

theorem lambda_beta_expression
    (function : SourceTemplates.ValueSummary operations policy contracts world environment allowed
      (.lambda parameter body) (.function input output requests latent))
    (argument : SourceTemplates.ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value) (admitted : requests ⊆ allowed) :
    ∃ reduced : Requirements [],
      Expression operations policy contracts world allowed .none environment (body.subst parameter value) output [] reduced ∧
      ∀ store receiving before, evaluate store receiving before reduced =
        residualize (OwnerPhaseTransitions.project receiving before) latent := by
  obtain ⟨demand, requirements, source, outward⟩ := SourceCallableTransport.lambda_body function
  have empty := RecursiveOutward.no_owners outward
  subst demand
  refine ⟨requirements, SourceCallableTransport.expression_allowed_mono
    (substitution source (argument.change_allowed closed.1 _) closed) admitted, ?_⟩
  intro store receiving before
  simpa only [Option.bind_some] using RecursiveOutward.evaluation (store := store) (receiving := receiving) (before := before) outward

theorem bind_expression
    (source : Expression operations policy contracts world allowed scope environment (.bind parameter value body) result demand requirements)
    (closed : ClosedValue value) :
    ∃ reduced : Requirements demand,
      Expression operations policy contracts world allowed scope environment (body.subst parameter value) result demand reduced ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  cases source with
  | stable summary => exact ⟨_, .stable (CoherentSourceTypes.bind_summary summary closed), fun _ _ _ => rfl⟩
  | callable summary => cases summary with
      | summaryBind initializer body =>
          have empty := CallableSources.value_row initializer closed.1
          subst_vars
          exact ⟨_, .callable (SourceCallableSubstitution.callable_substitution body (.callable initializer) closed), fun _ _ _ => rfl⟩
  | bind initializer body =>
      have empty := SourceTemplates.expression_value_demand initializer closed.1
      subst_vars
      refine ⟨_, substitution body (RecursiveRecomposition.value_summary initializer closed.1) closed, ?_⟩
      intro store receiving before
      rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation initializer closed.1]
      simp only [OwnerPhaseTransitions.spendAll, RecursiveRecomposition.merge_empty_left]

theorem beta_expression
    (source : Expression operations policy contracts world allowed scope environment (.app (.lambda parameter body) value) result demand requirements)
    (closed : ClosedValue value) :
    ∃ reduced : Requirements demand,
      Expression operations policy contracts world allowed .none environment (body.subst parameter value) result demand reduced ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  cases source with
  | stable summary => exact ⟨_, .stable (CoherentSourceTypes.beta_summary summary closed), fun _ _ _ => rfl⟩
  | callable summary => cases summary with
      | summaryApp function argument admitted =>
          have functionRow := CallableSources.value_row function trivial
          have argumentRow := CallableSources.value_row argument closed.1
          subst_vars
          obtain ⟨reduced, next, evaluated⟩ := lambda_beta_expression (.callable function) (.callable argument) closed admitted
          exact ⟨reduced, next, fun store receiving before => by
            rw [evaluated]
            simp only [evaluate, RecursiveRequirements.evaluateFuel, OwnerSource.exportAt, List.nil_append]⟩
  | app function argument admitted =>
      have functionDemand := SourceTemplates.expression_value_demand function trivial
      have argumentDemand := SourceTemplates.expression_value_demand argument closed.1
      subst_vars
      obtain ⟨reduced, next, evaluated⟩ := lambda_beta_expression
        (RecursiveRecomposition.value_summary function trivial) (RecursiveRecomposition.value_summary argument closed.1) closed admitted
      refine ⟨reduced, next, ?_⟩
      intro store receiving before
      rw [evaluated, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.value_evaluation function trivial, RecursiveRecomposition.value_evaluation argument closed.1]
      simp only [OwnerPhaseTransitions.spendAll, List.nil_append, RecursiveRecomposition.merge_empty_left]
      rfl

/-- Replacing current code by a source with the same demand and evaluation
    preserves the entire configuration. The pending source supplies the store. -/
theorem replace_current {requirements : Requirements currentDemand}
    (replacement : Expression operations policy contracts world allowed nextScope Environment.empty next input currentDemand reduced)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports nextScope nextTicket)
    (pending : SourceTemplates.Segment operations policy contracts tables world stack input output pendingDemand pendingRequirements records)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked records [] (OwnerPhaseTransitions.available (ownedTickets stack))
      (.sequence (requirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row)
    (accepted : checkFootprint outside row = true)
    (same : ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements) :
    SourceTemplates.CheckedConfiguration operations policy contracts tables world outside nextScope next stack output
      (currentDemand ++ pendingDemand) row := by
  apply SourceTemplates.check_configuration (.checked replacement scopeTyped pending) unique _ accepted
  have original := RecursiveRequirements.checked_complete checked
  simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend] at original ⊢
  rw [same]
  exact original

theorem bind_preserves
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope
      (.bind parameter value body) stack output demand row)
    (closed : ClosedValue value) :
    SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope
      (body.subst parameter value) stack output demand row := by
  cases source with
  | checked source unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨reduced, replacement, same⟩ := bind_expression current closed
        exact replace_current replacement scopeTyped pending unique checked accepted same

theorem beta_preserves
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope
      (.app (.lambda parameter body) value) stack output demand row)
    (closed : ClosedValue value) :
    SourceTemplates.CheckedConfiguration operations policy contracts tables world outside .none
      (body.subst parameter value) stack output demand row := by
  cases source with
  | checked source unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨reduced, replacement, same⟩ := beta_expression current closed
        exact replace_current replacement .none pending unique checked accepted same

theorem request_parts
    (checked : Checked store receiving before (.request nearer (first ++ second)) row) :
    ∃ firstRow secondRow, Checked store receiving before (.request nearer first) firstRow ∧
      Checked store receiving before (.request nearer second) secondRow ∧ row = firstRow ++ secondRow := by
  have evaluated := RecursiveRequirements.checked_complete checked
  simp only [evaluate, RecursiveRequirements.evaluateFuel, OwnerSource.exportAt, residual_rows_append] at evaluated
  obtain ⟨firstRow, secondRow, left, right, same⟩ := PhaseRechecking.merge_split evaluated
  exact ⟨firstRow, secondRow, .request left, .request right, same⟩

theorem choice_parts {first : Requirements a} {second : Requirements b}
    (checked : Checked store receiving before (.choice first second same) row) :
    ∃ firstRow secondRow, Checked store receiving before first firstRow ∧
      Checked store receiving before second secondRow ∧ row = firstRow ++ secondRow := by
  have evaluated := RecursiveRequirements.checked_complete checked
  rw [RecursiveRequirements.evaluate_choice] at evaluated
  obtain ⟨firstRow, secondRow, left, right, same⟩ := PhaseRechecking.merge_split evaluated
  exact ⟨firstRow, secondRow, RecursiveRequirements.evaluate_sound left, RecursiveRequirements.evaluate_sound right, same⟩

/-- Branch selection may remove requests. It retains the same set of consumed
    owners, with order allowed to follow the selected branch. -/
theorem branch_expression
    (source : Expression operations policy contracts world allowed scope environment (.branch (.boolean flag) yes no) result demand requirements) :
    ∃ (remaining : List Nat) (reduced : Requirements remaining),
      Expression operations policy contracts world allowed scope environment (if flag then yes else no) result remaining reduced ∧
      demand.Perm remaining ∧
      ∀ store receiving before row, Checked store receiving before requirements row →
        ∃ nextRow, Checked store receiving before reduced nextRow ∧ nextRow.Sublist row := by
  cases source with
  | stable summary => cases summary with
    | branch condition yesSource noSource => cases condition with
      | boolean =>
          cases flag with
          | false =>
              refine ⟨[], _, .stable noSource, .refl _, ?_⟩
              intro store receiving before row checked
              obtain ⟨firstRow, secondRow, left, right, rfl⟩ := request_parts checked
              exact ⟨secondRow, right, List.sublist_append_right _ _⟩
          | true =>
              refine ⟨[], _, .stable yesSource, .refl _, ?_⟩
              intro store receiving before row checked
              obtain ⟨firstRow, secondRow, left, right, rfl⟩ := request_parts checked
              exact ⟨firstRow, left, List.sublist_append_left _ _⟩
  | callable summary => cases summary with
    | summaryBranch condition yesSource noSource => cases condition with
      | summaryBoolean =>
          cases flag with
          | false =>
              refine ⟨[], _, .callable noSource, .refl _, ?_⟩
              intro store receiving before row checked
              obtain ⟨firstRow, secondRow, left, right, rfl⟩ := request_parts checked
              exact ⟨secondRow, right, List.sublist_append_right _ _⟩
          | true =>
              refine ⟨[], _, .callable yesSource, .refl _, ?_⟩
              intro store receiving before row checked
              obtain ⟨firstRow, secondRow, left, right, rfl⟩ := request_parts checked
              exact ⟨firstRow, left, List.sublist_append_left _ _⟩
  | branch condition yesSource noSource same =>
      have empty := SourceTemplates.expression_value_demand condition trivial
      subst_vars
      cases flag with
      | false =>
          refine ⟨_, _, noSource, same, ?_⟩
          intro store receiving before row checked
          have evaluated := RecursiveRequirements.checked_complete checked
          rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation condition trivial,
            RecursiveRecomposition.merge_empty_left] at evaluated
          obtain ⟨firstRow, secondRow, left, right, rfl⟩ := choice_parts (RecursiveRequirements.evaluate_sound evaluated)
          exact ⟨secondRow, right, List.sublist_append_right _ _⟩
      | true =>
          refine ⟨_, _, yesSource, .refl _, ?_⟩
          intro store receiving before row checked
          have evaluated := RecursiveRequirements.checked_complete checked
          rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation condition trivial,
            RecursiveRecomposition.merge_empty_left] at evaluated
          obtain ⟨firstRow, secondRow, left, right, rfl⟩ := choice_parts (RecursiveRequirements.evaluate_sound evaluated)
          exact ⟨firstRow, left, List.sublist_append_left _ _⟩

theorem spend_permutation (same : first.Perm second) (before : Phases) :
    spendAll before first = spendAll before second := by
  funext owner
  simp only [OwnerPhaseTransitions.spendAll_at, same.mem_iff]

theorem branch_preserves
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope
      (.branch (.boolean flag) yes no) stack output demand row) :
    ∃ remaining nextRow,
      SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope
        (if flag then yes else no) stack output remaining nextRow ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  cases source with
  | checked source unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨remaining, reduced, replacement, sameDemand, selected⟩ := branch_expression current
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
        have activeCheck := RecursiveRequirements.checked_prepend_iff.mp currentCheck
        obtain ⟨nextRow, nextCheck, included⟩ := selected _ _ _ _ activeCheck
        have nextPending := pendingCheck
        rw [spend_permutation sameDemand] at nextPending
        have includedWhole := included.append (List.Sublist.refl pendingRow)
        refine ⟨_, _, .checked (.checked replacement scopeTyped pending) unique
          (.sequence (RecursiveRequirements.checked_prepend_iff.mpr nextCheck) nextPending)
          (checked_footprint_subset accepted includedWhole.subset), ?_, includedWhole⟩
        exact sameDemand.append_right _

/-- The ordinary redexes whose operands have finished evaluation. -/
inductive Ready : Code → Prop where
  | bind (isValue : value.IsValue) : Ready (.bind parameter value body)
  | app (isValue : value.IsValue) : Ready (.app (.lambda parameter body) value)
  | branch : Ready (.branch (.boolean flag) yes no)

theorem ready_not_value (ready : Ready code) : ¬ code.IsValue := by
  cases ready <;> simp [Code.IsValue]

theorem ready_not_focus (ready : Ready code) (focus : Focus code child position) : False := by
  cases ready <;> cases focus <;> simp_all [Code.IsValue]

theorem ready_step_preserves
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row)
    (ready : Ready code) (step : RawStep ⟨code, scope, stack⟩ next created completed) :
    ∃ remaining nextRow,
      SourceTemplates.CheckedConfiguration operations policy contracts tables world outside
        next.scope next.expression next.stack output remaining nextRow ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ next.stack = stack ∧ created = [] ∧ completed = [] := by
  cases step with
  | focus plain focus tail => exact False.elim (ready_not_focus ready focus)
  | plug plain value closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveHandler handler value closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveCell identity payload answer savedScope scope value closed tail => exact False.elim (ready_not_value ready closed.1)
  | startCleanup action saved closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveClause ticket answer value closed scope caller tail => exact False.elim (ready_not_value ready closed.1)
  | bind parameter value body scope tail closed environmentReady =>
      exact ⟨_, _, bind_preserves source closed, .refl _, .refl _, rfl, rfl, rfl⟩
  | beta parameter body value scope tail closed closureReady =>
      exact ⟨_, _, beta_preserves source closed, .refl _, .refl _, rfl, rfl, rfl⟩
  | ifTrue yes no scope tail =>
      obtain ⟨remaining, nextRow, checked, same, included⟩ := branch_preserves source
      exact ⟨remaining, nextRow, checked, same, included, rfl, rfl, rfl⟩
  | ifFalse yes no scope tail =>
      obtain ⟨remaining, nextRow, checked, same, included⟩ := branch_preserves source
      exact ⟨remaining, nextRow, checked, same, included, rfl, rfl, rfl⟩
  | enterHandler | enterCell | enterCleanup | finishCleanup | capture | resume | discard | finishClose | retire | readCell | writeCell => cases ready

theorem ready_progress
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row)
    (ready : Ready code) : ∃ next, RawStep ⟨code, scope, stack⟩ next [] [] := by
  cases source with
  | checked source unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        have typed := SourceTemplates.expression_ports current scopeTyped
        change ScopedPorts.Typed operations.ports world ScopedPorts.TypeEnv.empty _ _ _ _ at typed
        cases ready with
        | bind isValue =>
            exact ⟨_, (ScopedPorts.typed_bind_value_progress typed isValue _ _).1⟩
        | app isValue =>
            obtain ⟨after, step, typedAfter⟩ := ScopedPorts.typed_application_value_progress typed trivial isValue _ _
            exact ⟨_, step⟩
        | @branch flag yes no =>
            cases flag
            · exact ⟨_, .ifFalse yes no _ _⟩
            · exact ⟨_, .ifTrue yes no _ _⟩

/-- Typing supplies lexical readiness, and preservation supplies the successor
    check. No successor admissibility or closed-substitution premise is added. -/
theorem ready_preserves
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row)
    (ready : Ready code) :
    ∃ next remaining nextRow,
      RawStep ⟨code, scope, stack⟩ next [] [] ∧
      SourceTemplates.CheckedConfiguration operations policy contracts tables world outside
        next.scope next.expression next.stack output remaining nextRow ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ next.stack = stack ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) []
        (OwnerPhaseTransitions.available (ownedTickets next.stack)) := by
  obtain ⟨next, step⟩ := ready_progress source ready
  obtain ⟨remaining, nextRow, checked, same, included, sameStack, created, completed⟩ := ready_step_preserves source ready step
  exact ⟨next, remaining, nextRow, step, checked, same, included, sameStack, sameStack.symm ▸ .nil⟩

namespace Examples
open SharedResumption.NestedExamples (contracts outer_known outerBoundary)
open SharedResumption.Examples (operations policy tables outside raw effect)
open SourceTemplates.Examples (records currentRequirements outerBoundaryRequirements current_source outer_boundary_source requirements derived_evaluation)

def bindRequirements : Requirements [19, 29] :=
  .sequence ((Requirements.sequence (.request [] []) currentRequirements).prepend (OwnerPhases.ofStack tables outerBoundary))
    outerBoundaryRequirements

theorem variable_resume : Expression operations policy contracts [] [effect] (.ticket 7 19)
    (Environment.empty.extend 99 .unit) (.resume 7 (.variable 99)) .unit [19, 29] currentRequirements :=
  .resume outer_known rfl rfl (.stable (.variable rfl (by simp [SharedResumption.NestedExamples.outer, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])))
    (fun _ member => member)
    (by simp [SharedResumption.NestedExamples.outer, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem bound_source : SourceTemplates.Configuration operations policy contracts tables [] (.ticket 7 19)
    (.bind 99 .unit (.resume 7 (.variable 99))) outerBoundary .unit [19, 29] bindRequirements records :=
  .checked (.bind (.stable .unit) variable_resume) (.bound (Owners.ports_lookup outer_known)) outer_boundary_source

theorem bound_checked : SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
    (.bind 99 .unit (.resume 7 (.variable 99))) outerBoundary .unit [19, 29] raw := by
  apply SourceTemplates.check_configuration bound_source (by decide) _ (by decide)
  simpa only [bindRequirements, requirements, Requirements.prepend, RecursiveRequirements.evaluate_sequence,
    RecursiveRecomposition.evaluate_empty, List.nil_append, spendAll, RecursiveRecomposition.merge_empty_left] using derived_evaluation

theorem bound_resume_preserved :
    RawStep ⟨.bind 99 .unit (.resume 7 (.variable 99)), .ticket 7 19, outerBoundary⟩
      ⟨.resume 7 .unit, .ticket 7 19, outerBoundary⟩ [] [] ∧
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      (.resume 7 .unit) outerBoundary .unit [19, 29] raw := by
  refine ⟨.bind _ _ _ _ _ CallableProtection.Examples.unit_closed ?_, bind_preserves bound_checked CallableProtection.Examples.unit_closed⟩
  intro name member
  simpa [Code.dependencies] using member

theorem bound_then_nested_resume : ∃ restored remaining,
    RawStep ⟨.resume 7 .unit, .ticket 7 19, outerBoundary⟩ ⟨.unit, .ticket 7 19, restored⟩ [] [.ticket 19] ∧
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      .unit restored .unit remaining raw ∧ remaining = [29] := by
  obtain ⟨owner, restored, remaining, step, checked, same, trace⟩ :=
    RecursiveRecomposition.resume_preserves bound_resume_preserved.2 CallableProtection.Examples.unit_closed
  obtain ⟨sameOwner, sameRemaining⟩ := List.cons.inj same
  subst owner
  exact ⟨restored, remaining, step, checked, sameRemaining.symm⟩

def branchRequirements : Requirements [19, 29] :=
  .sequence ((Requirements.sequence (.request [] []) (.choice currentRequirements currentRequirements (.refl _))).prepend
    (OwnerPhases.ofStack tables outerBoundary)) outerBoundaryRequirements

theorem branch_source : SourceTemplates.Configuration operations policy contracts tables [] (.ticket 7 19)
    (.branch (.boolean flag) (.resume 7 .unit) (.resume 7 .unit)) outerBoundary .unit [19, 29] branchRequirements records :=
  .checked (.branch (.stable .boolean) current_source current_source (.refl _))
    (.bound (Owners.ports_lookup outer_known)) outer_boundary_source

theorem branch_checked : SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
    (.branch (.boolean flag) (.resume 7 .unit) (.resume 7 .unit)) outerBoundary .unit [19, 29] (raw ++ raw) := by
  obtain ⟨firstRow, pendingRow, current, pending, same⟩ := RecursiveRequirements.checked_sequence_parts SourceTemplates.Examples.recursive_check
  have pendingEmpty : pendingRow = [] := by
    have evaluated := RecursiveRequirements.checked_complete pending
    simp only [outerBoundaryRequirements, RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent,
      RecursiveRecomposition.evaluate_empty, spendAll, OwnerPhaseTransitions.spend] at evaluated
    simpa [merge] using evaluated.symm
  subst pendingRow
  simp only [List.append_nil] at same
  subst firstRow
  have active := RecursiveRequirements.checked_prepend_iff.mp current
  have selected : Checked records (OwnerPhases.ofStack tables outerBoundary ++ [])
      (OwnerPhaseTransitions.available (ownedTickets outerBoundary))
      (.sequence (.request [] []) (.choice currentRequirements currentRequirements (.refl _))) (raw ++ raw) :=
    by
      have combined := Checked.sequence
        (SourceTemplates.Examples.empty_checked (before := OwnerPhaseTransitions.available (ownedTickets outerBoundary)))
        (Checked.choice (same := List.Perm.refl _) active active)
      simpa only [List.nil_append] using combined
  exact .checked branch_source (by decide)
    (by simpa only [branchRequirements, List.append_nil] using
      Checked.sequence (RecursiveRequirements.checked_prepend_iff.mpr selected) pending) (by decide)

theorem selected_branch_preserved : ∃ remaining nextRow,
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      (.resume 7 .unit) outerBoundary .unit remaining nextRow ∧
    [19, 29].Perm remaining ∧ nextRow.Sublist (raw ++ raw) :=
  branch_preserves (branch_checked (flag := false))

end Examples

end Ash.OneShot.RecursiveExpressions

#print axioms Ash.OneShot.RecursiveExpressions.substitution
#print axioms Ash.OneShot.RecursiveExpressions.bind_expression
#print axioms Ash.OneShot.RecursiveExpressions.beta_expression
#print axioms Ash.OneShot.RecursiveExpressions.replace_current
#print axioms Ash.OneShot.RecursiveExpressions.bind_preserves
#print axioms Ash.OneShot.RecursiveExpressions.beta_preserves
#print axioms Ash.OneShot.RecursiveExpressions.request_parts
#print axioms Ash.OneShot.RecursiveExpressions.choice_parts
#print axioms Ash.OneShot.RecursiveExpressions.branch_expression
#print axioms Ash.OneShot.RecursiveExpressions.spend_permutation
#print axioms Ash.OneShot.RecursiveExpressions.branch_preserves
#print axioms Ash.OneShot.RecursiveExpressions.ready_not_value
#print axioms Ash.OneShot.RecursiveExpressions.ready_not_focus
#print axioms Ash.OneShot.RecursiveExpressions.ready_step_preserves
#print axioms Ash.OneShot.RecursiveExpressions.ready_progress
#print axioms Ash.OneShot.RecursiveExpressions.ready_preserves
#print axioms Ash.OneShot.RecursiveExpressions.Examples.variable_resume
#print axioms Ash.OneShot.RecursiveExpressions.Examples.bound_source
#print axioms Ash.OneShot.RecursiveExpressions.Examples.bound_checked
#print axioms Ash.OneShot.RecursiveExpressions.Examples.bound_resume_preserved
#print axioms Ash.OneShot.RecursiveExpressions.Examples.bound_then_nested_resume
#print axioms Ash.OneShot.RecursiveExpressions.Examples.branch_source
#print axioms Ash.OneShot.RecursiveExpressions.Examples.branch_checked
#print axioms Ash.OneShot.RecursiveExpressions.Examples.selected_branch_preserved

#print axioms Ash.OneShot.RecursiveExpressions.lambda_beta_expression
