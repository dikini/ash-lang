import RecursiveConsumption

/-!
Ordinary execution and value completion for the state with both authenticated
continuation modes. These proofs reuse structural expression/context facts and
carry the collected closing records through actual stack changes.
-/

namespace Ash.OneShot.RecursiveExecution
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open SourceTemplates (Expression Segment)
open RecursiveRecords (Records CheckedState)
open RecursiveRequirements (Requirements Store Checked evaluate)
open OwnerPhaseTransitions (Phases Trace available spend spendAll)
open RecursiveExpressions (bind_expression beta_expression branch_expression spend_permutation Ready ready_not_value ready_not_focus)
open RecursiveContexts (focus_decompose prepare_plain context_plug plain_context plain_owners evaluate_plain)
open RecursiveCompletion (empty_head running_export retiredTickets)

/-- Rebuild a state with source-derived records and a successful finite check. -/
theorem check_state
    (source : SourceTemplates.Configuration operations policy contracts tables world scope code stack output demand requirements resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (evaluated : evaluate (resumes ++ disposals) [] (available (ownedTickets stack)) requirements = some row)
    (accepted : checkFootprint outside row = true) :
    CheckedState operations policy contracts tables world outside scope code stack output demand row :=
  .checked source closing unique (RecursiveRequirements.evaluate_sound evaluated) accepted

theorem replace_current {requirements : Requirements currentDemand}
    (replacement : Expression operations policy contracts world allowed nextScope Environment.empty next input currentDemand reduced)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports nextScope nextTicket)
    (pending : SourceTemplates.Segment operations policy contracts tables world stack input output pendingDemand pendingRequirements records)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (records ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
      (.sequence (requirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row)
    (accepted : checkFootprint outside row = true)
    (same : ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements) :
    CheckedState operations policy contracts tables world outside nextScope next stack output
      (currentDemand ++ pendingDemand) row := by
  apply check_state (.checked replacement scopeTyped pending) closing unique _ accepted
  have original := RecursiveRequirements.checked_complete checked
  simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend] at original ⊢
  rw [same]
  exact original

theorem bind_preserves
    (source : CheckedState operations policy contracts tables world outside scope
      (.bind parameter value body) stack output demand row)
    (closed : ClosedValue value) :
    CheckedState operations policy contracts tables world outside scope
      (body.subst parameter value) stack output demand row := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨reduced, replacement, same⟩ := bind_expression current closed
        exact replace_current replacement scopeTyped pending closing unique checked accepted same

theorem beta_preserves
    (source : CheckedState operations policy contracts tables world outside scope
      (.app (.lambda parameter body) value) stack output demand row)
    (closed : ClosedValue value) :
    CheckedState operations policy contracts tables world outside .none
      (body.subst parameter value) stack output demand row := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨reduced, replacement, same⟩ := beta_expression current closed
        exact replace_current replacement .none pending closing unique checked accepted same

theorem branch_preserves
    (source : CheckedState operations policy contracts tables world outside scope
      (.branch (.boolean flag) yes no) stack output demand row) :
    ∃ remaining nextRow,
      CheckedState operations policy contracts tables world outside scope
        (if flag then yes else no) stack output remaining nextRow ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨remaining, reduced, replacement, sameDemand, selected⟩ := branch_expression current
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
        have activeCheck := RecursiveRequirements.checked_prepend_iff.mp currentCheck
        obtain ⟨nextRow, nextCheck, included⟩ := selected _ _ _ _ activeCheck
        have nextPending := pendingCheck
        rw [spend_permutation sameDemand] at nextPending
        have includedWhole := included.append (List.Sublist.refl pendingRow)
        refine ⟨_, _, .checked (.checked replacement scopeTyped pending) closing unique
          (.sequence (RecursiveRequirements.checked_prepend_iff.mpr nextCheck) nextPending)
          (checked_footprint_subset accepted includedWhole.subset), ?_, includedWhole⟩
        exact sameDemand.append_right _

theorem ready_step_preserves
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row)
    (ready : Ready code) (step : RawStep ⟨code, scope, stack⟩ next created completed) :
    ∃ remaining nextRow,
      CheckedState operations policy contracts tables world outside
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
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row)
    (ready : Ready code) : ∃ next, RawStep ⟨code, scope, stack⟩ next [] [] := by
  cases source with
  | checked source closing unique checked accepted => cases source with
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
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row)
    (ready : Ready code) :
    ∃ next remaining nextRow,
      RawStep ⟨code, scope, stack⟩ next [] [] ∧
      CheckedState operations policy contracts tables world outside
        next.scope next.expression next.stack output remaining nextRow ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ next.stack = stack ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) []
        (OwnerPhaseTransitions.available (ownedTickets next.stack)) := by
  obtain ⟨next, step⟩ := ready_progress source ready
  obtain ⟨remaining, nextRow, checked, same, included, sameStack, created, completed⟩ := ready_step_preserves source ready step
  exact ⟨next, remaining, nextRow, step, checked, same, included, sameStack, sameStack.symm ▸ .nil⟩

theorem focus_preserves
    (source : CheckedState operations policy contracts tables world outside scope whole stack output demand row)
    (focus : Focus whole child position) :
    ∃ plain : PlainData,
      RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] ∧
      CheckedState operations policy contracts tables world outside scope child
        (.push (.plain plain) stack) output demand row ∧
      plain.context = position ∧ plain.scope = scope ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) []
        (OwnerPhaseTransitions.available (ownedTickets (.push (.plain plain) stack))) := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨input, childDemand, restDemand, currentReq, restReq, childSource, context, sameDemand, evaluation⟩ :=
          focus_decompose current focus
        obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ := prepare_plain current focus scopeTyped input
        have frame : SourceTemplates.Frame operations policy contracts world (.plain plain) input _ restDemand restReq :=
          .plain (by simpa only [contextSame, scopeSame] using context)
            (by simpa only [scopeSame] using scopeTyped) inputAnnotation outputAnnotation
        have step : RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] := by
          simpa only [scopeSame] using RawStep.focus plain (by simpa only [contextSame] using focus) stack
        refine ⟨plain, step, ?_, contextSame, scopeSame, .nil⟩
        rw [sameDemand, List.append_assoc]
        apply check_state (.checked childSource scopeTyped (.push frame pending)) (.push closing) unique _ accepted
        have oldEvaluation := RecursiveRequirements.checked_complete checked
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation] at oldEvaluation
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, plain_context,
          plain_owners, List.cons_append, evaluate_plain]
        simpa only [sameDemand, PhaseRechecking.spendAll_append, merge_assoc] using oldEvaluation

theorem plug_preserves
    (source : CheckedState operations policy contracts tables world outside scope value
      (.push (.plain plain) stack) output demand row)
    (closed : ClosedValue value) :
    CheckedState operations policy contracts tables world outside plain.scope (plain.context.plug value)
      stack output demand row := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        have empty := SourceTemplates.expression_value_demand current closed.1
        subst_vars
        cases closing with
        | push closing => cases pending with
        | push frame pending => cases frame with
          | plain context frameScope inputAnnotation outputAnnotation =>
              obtain ⟨combined, combinedSource, evaluation⟩ := context_plug context
                (((RecursiveRecomposition.value_summary current closed.1).change_allowed closed.1 _).expression _)
              apply check_state (.checked combinedSource frameScope pending) closing unique _ accepted
              have oldEvaluation := RecursiveRequirements.checked_complete checked
              simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                RecursiveRecomposition.value_evaluation current closed.1, RecursiveRecomposition.merge_empty_left,
                spendAll, plain_owners] at oldEvaluation
              simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
                RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left, spendAll]
              exact oldEvaluation

theorem value_closed
    (source : CheckedState operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue) : ClosedValue value := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        exact ScopedPorts.typed_value_closed (SourceTemplates.expression_ports current scopeTyped) isValue

theorem plug_progress
    (source : CheckedState operations policy contracts tables world outside scope value
      (.push (.plain plain) stack) output demand row)
    (isValue : value.IsValue) :
    RawStep ⟨value, scope, .push (.plain plain) stack⟩ ⟨plain.context.plug value, plain.scope, stack⟩ [] [] ∧
      CheckedState operations policy contracts tables world outside plain.scope (plain.context.plug value)
        stack output demand row ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets (.push (.plain plain) stack))) []
        (OwnerPhaseTransitions.available (ownedTickets stack)) := by
  have closed := value_closed source isValue
  exact ⟨.plug plain value closed scope stack, plug_preserves source closed, .nil⟩

/-- A value contributes no owner demand or immediate effect. Its complete
    current-state check therefore supplies the pending segment's exact check. -/
theorem value_pending
    (source : CheckedState operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue) :
    ∃ (input : Value) (requirements : Requirements demand) (records disposals : RecursiveRequirements.Store),
      SourceTemplates.ValueSummary operations policy contracts world Environment.empty [] value input ∧
      ScopedPorts.EffectScopeKnown contracts.ports scope ∧
      Segment operations policy contracts tables world stack input output demand requirements records ∧
      Records operations policy contracts tables world stack disposals ∧
      (ownedTickets stack).Nodup ∧ Checked (records ++ disposals) [] (available (ownedTickets stack)) requirements row ∧
      checkFootprint outside row = true := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        have empty := SourceTemplates.expression_value_demand current isValue
        subst_vars
        have summary := (RecursiveRecomposition.value_summary current isValue).change_allowed isValue []
        refine ⟨_, _, _, _, summary, ⟨_, scopeTyped⟩, pending, closing, unique, RecursiveRequirements.evaluate_sound ?_, accepted⟩
        have evaluation := RecursiveRequirements.checked_complete checked
        simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
          RecursiveRecomposition.value_evaluation current isValue, spendAll, RecursiveRecomposition.merge_empty_left] using evaluation

theorem value_source_configuration
    (summary : SourceTemplates.ValueSummary operations policy contracts world Environment.empty allowed code input)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (pending : Segment operations policy contracts tables world stack input output demand requirements records)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (records ++ disposals) [] (available (ownedTickets stack)) requirements row)
    (accepted : checkFootprint outside row = true) :
    CheckedState operations policy contracts tables world outside scope code stack output demand row := by
  have current : Checked (records ++ disposals) [] (available (ownedTickets stack))
      ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables stack)) [] :=
    Checked.request (row := []) (by simp [OwnerSource.exportAt, residual_empty])
  exact .checked (.checked (currentDemand := []) (pendingDemand := demand) (summary.expression _) scopeTyped pending) closing unique
    (by simpa only [List.nil_append] using Checked.sequence current checked) accepted

theorem value_configuration
    (summary : Summary operations world Environment.empty allowed code input [])
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (pending : Segment operations policy contracts tables world stack input output demand requirements records)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (records ++ disposals) [] (available (ownedTickets stack)) requirements row)
    (accepted : checkFootprint outside row = true) :
    CheckedState operations policy contracts tables world outside scope code stack output demand row :=
  value_source_configuration (.stable summary) scopeTyped pending closing unique checked accepted

theorem start_cleanup
    (source : CheckedState operations policy contracts tables world outside scope value (.push (.armed action) tail) output demand row)
    (closed : ClosedValue value) :
    CheckedState operations policy contracts tables world outside .none (.app action.action .unit)
      (.push (.running action value closed) tail) output demand row := by
  obtain ⟨input, requirements, records, disposals, summary, scopeTyped, pending, closing, unique, checked, accepted⟩ := value_pending source closed.1
  cases closing with
  | push closing => cases pending with
  | push head rest => cases head with
      | armed scopeKnown callback annotation =>
          rename_i tailDemand tailRequirements latent
          obtain ⟨callbackRow, tailRow, callbackCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
          have exported := RecursiveRequirements.checked_complete callbackCheck
          simp only [RecursiveRequirements.evaluate_prepend, RecursiveContexts.evaluate_request, List.append_nil] at exported
          have invocation : SourceTemplates.CallableSummary operations policy contracts world Environment.empty action.requests (.app action.action .unit) .unit latent :=
            .summaryApp (SourceCallableTransport.value_callable (callback.change_allowed action.closed.1 action.requests))
              .summaryUnit (fun _ member => member)
          have currentCheck : Checked (records ++ disposals) (OwnerPhases.ofStack tables (.push (.running action value closed) tail))
              (available (ownedTickets tail)) (.request [] latent) callbackRow := by
            apply Checked.request
            simpa only [List.nil_append, running_export, ownedTickets] using exported
          have currentPrefixed : Checked (records ++ disposals) [] (available (ownedTickets tail))
              ((Requirements.request [] latent).prepend (OwnerPhases.ofStack tables (.push (.running action value closed) tail))) callbackRow :=
            RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)
          have empty : Checked (records ++ disposals) [] (available (ownedTickets tail))
              ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables tail)) [] :=
            Checked.request (row := []) (by simp [OwnerSource.exportAt, residual_empty])
          have nextPending := Checked.sequence empty tailCheck
          rw [same] at accepted ⊢
          exact .checked (.checked (currentDemand := []) (pendingDemand := _) (.callable invocation) .none
            (.push (.running scopeKnown callback summary annotation) rest)) (.push closing) unique
            (by simpa only [List.nil_append, ownedTickets] using Checked.sequence currentPrefixed nextPending) accepted

theorem finish_cleanup
    (source : CheckedState operations policy contracts tables world outside scope .unit
      (.push (.running action value closed) tail) output demand row) :
    CheckedState operations policy contracts tables world outside action.scope value tail output demand row := by
  obtain ⟨input, requirements, records, disposals, summary, scopeTyped, pending, closing, unique, checked, accepted⟩ := value_pending source trivial
  cases closing with
  | push closing => cases pending with
  | push head rest => cases head with
      | running scopeKnown callback saved annotation =>
          obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
          exact value_source_configuration saved scopeTyped rest closing unique (empty_head checked) accepted

theorem finish_close
    (source : CheckedState operations policy contracts tables world outside scope .unit
      (.push (.closing identity caller) tail) output demand row) :
    CheckedState operations policy contracts tables world outside caller .unit tail output demand row := by
  obtain ⟨input, requirements, records, disposals, summary, scopeTyped, pending, closing, unique, checked, accepted⟩ := value_pending source trivial
  cases closing with
  | push closing => cases pending with
  | push head rest => cases head with
      | closing scopeKnown =>
          obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
          exact value_configuration (allowed := []) .unit scopeTyped rest closing unique (empty_head checked) accepted

theorem retire
    (source : CheckedState operations policy contracts tables world outside scope .unit
      (.push (.retiring owner) tail) output demand row) :
    ∃ remaining, demand = owner :: remaining ∧
      CheckedState operations policy contracts tables world outside scope .unit tail output remaining row ∧
      Trace (available (ownedTickets (.push (.retiring owner) tail))) [owner] (available (ownedTickets tail)) := by
  obtain ⟨input, requirements, records, disposals, summary, ⟨ticket, scopeTyped⟩, pending, closing, unique, checked, accepted⟩ := value_pending source trivial
  cases closing with
  | push closing => cases pending with
  | push head rest => cases head with
      | retiring known =>
          rename_i tailDemand tailRequirements contract
          obtain ⟨firstRow, tailRow, firstCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
          have ready := OwnerPhaseTransitions.trace_available (RecursiveRequirements.checked_trace firstCheck) owner List.mem_cons_self
          have firstEmpty : firstRow = [] := by
            have evaluated := RecursiveRequirements.checked_complete firstCheck
            simpa only [Requirements.prepend, RecursiveClosing.evaluate_retire, if_pos ready, Option.some.injEq] using evaluated.symm
          subst firstRow
          have phases := OwnerPhaseTransitions.spend_available_cons (List.nodup_cons.mp unique).1
          have next : Checked (records ++ disposals) [] (available (ownedTickets tail)) tailRequirements tailRow := by
            simpa only [spendAll, ownedTickets, phases] using tailCheck
          refine ⟨_, rfl, ?_, .cons ready ?_⟩
          · exact value_configuration (allowed := []) .unit scopeTyped rest closing (List.nodup_cons.mp unique).2
              (by simpa only [same, List.nil_append] using next) accepted
          · simpa only [ownedTickets, phases] using (Trace.nil (before := available (ownedTickets tail)))


theorem leave_handler
    (source : CheckedState operations policy contracts tables world outside scope value
      (.push (.handler handler) tail) output demand row) (isValue : value.IsValue) :
    CheckedState operations policy contracts tables world outside handler.scope value tail output demand row := by
  obtain ⟨input, requirements, records, disposals, summary, scopeTyped, pending, closing, unique, checked, accepted⟩ := value_pending source isValue
  cases closing with
  | push closing => cases pending with
  | push head rest => cases head with
      | handler typed annotation => cases typed with
          | handler scopeKnown clauses coverage distinct =>
              obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
              exact value_source_configuration summary scopeTyped rest closing unique (empty_head checked) accepted

theorem leave_cell
    (source : CheckedState operations policy contracts tables world outside scope value
      (.push (.cell identity payload caller answer) tail) output demand row) (isValue : value.IsValue) :
    CheckedState operations policy contracts tables world outside caller value tail output demand row := by
  obtain ⟨input, requirements, records, disposals, summary, scopeTyped, pending, closing, unique, checked, accepted⟩ := value_pending source isValue
  cases closing with
  | push closing => cases pending with
  | push head rest => cases head with
      | cell scopeKnown noEscape annotation =>
          obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
          exact value_source_configuration summary scopeTyped rest closing unique (empty_head checked) accepted

theorem leave_clause
    (source : CheckedState operations policy contracts tables world outside scope value
      (.spent owner answer caller tail) output demand row) (isValue : value.IsValue) :
    CheckedState operations policy contracts tables world outside caller value tail output demand row := by
  obtain ⟨input, requirements, records, disposals, summary, scopeTyped, pending, closing, unique, checked, accepted⟩ := value_pending source isValue
  cases closing with
  | spent closing => cases pending with
  | spent known annotation scopeKnown rest =>
      obtain ⟨firstRow, tailRow, firstCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have evaluated := RecursiveRequirements.checked_complete firstCheck
      simp only [RecursiveRecomposition.evaluate_spent] at evaluated
      split at evaluated
      · have firstEmpty := Option.some.inj evaluated.symm
        subst firstRow
        obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
        exact value_source_configuration summary scopeTyped rest closing unique
          (by simpa only [same, List.nil_append, spendAll, ownedTickets] using tailCheck) accepted
      · cases evaluated

/-- Every raw step from a value preserves this recursive source check. The
    ticket demand changes by exactly the emitted ticket-completion events. -/
theorem value_step_preserves
    (source : CheckedState operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue)
    (step : RawStep ⟨value, scope, stack⟩ next created completed) :
    ∃ remaining, CheckedState operations policy contracts tables world outside next.scope next.expression next.stack output remaining row ∧
      demand = retiredTickets completed ++ remaining ∧ created = [] ∧
      Trace (available (ownedTickets stack)) (retiredTickets completed) (available (ownedTickets next.stack)) := by
  cases step <;> try cases isValue
  case focus => exact False.elim (ScopedPorts.focus_is_not_value (by assumption) isValue)
  case plug => exact ⟨_, plug_preserves source (by assumption), rfl, rfl, .nil⟩
  case leaveHandler => exact ⟨_, leave_handler source (by exact (show ClosedValue _ from by assumption).1), rfl, rfl, .nil⟩
  case leaveCell => exact ⟨_, leave_cell source (by exact (show ClosedValue _ from by assumption).1), rfl, rfl, .nil⟩
  case startCleanup => exact ⟨_, start_cleanup source (by assumption), rfl, rfl, .nil⟩
  case finishCleanup => exact ⟨_, finish_cleanup source, rfl, rfl, .nil⟩
  case leaveClause => exact ⟨_, leave_clause source (by exact (show ClosedValue _ from by assumption).1), rfl, rfl, .nil⟩
  case finishClose => exact ⟨_, finish_close source, rfl, rfl, .nil⟩
  case retire =>
    obtain ⟨remaining, same, checked, transition⟩ := retire source
    exact ⟨remaining, checked, same, rfl, transition⟩


theorem value_progress
    (source : CheckedState operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue) :
    stack = .nil ∨ ∃ next completed, RawStep ⟨value, scope, stack⟩ next [] completed := by
  obtain ⟨input, requirements, records, disposals, summary, scopeTyped, pending, closing, unique, checked, accepted⟩ := value_pending source isValue
  have closed := ScopedPorts.typed_value_closed (summary.ports .none) isValue
  cases stack with
  | nil => exact Or.inl rfl
  | live owner inputType answerType capture caller tail =>
      cases pending with
      | live known inputAnnotation answerAnnotation scopeKnown held saved rest =>
          have evaluation := RecursiveRequirements.checked_complete checked
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent,
            ownedTickets, available, List.mem_cons_self, if_true, reduceCtorEq, if_false, merge] at evaluation
  | spent owner answer caller tail => exact Or.inr ⟨_, [], .leaveClause owner answer value closed scope caller tail⟩
  | push frame tail =>
      right
      cases pending with
      | push head rest => cases frame with
          | plain plain => exact ⟨_, [], .plug plain value closed scope tail⟩
          | handler handler => exact ⟨_, [], .leaveHandler handler value closed scope tail⟩
          | cell identity payload caller answer => exact ⟨_, [.resource identity], .leaveCell identity payload answer caller scope value closed tail⟩
          | armed action => exact ⟨_, [], .startCleanup action value closed scope tail⟩
          | running action saved savedClosed => cases head with
              | running scopeKnown callback savedSource annotation =>
                  have unit := ScopedPortJoint.scoped_unit_value (summary.ports .none) isValue
                  subst value
                  exact ⟨_, [.cleanup action.identity], .finishCleanup action saved savedClosed scope tail⟩
          | unwinding action => cases head
          | closing identity caller => cases head with
              | closing scopeKnown =>
                  have unit := ScopedPortJoint.scoped_unit_value (summary.ports .none) isValue
                  subst value
                  exact ⟨_, [.close identity], .finishClose identity scope caller tail⟩
          | retiring owner => cases head with
              | retiring known =>
                  have unit := ScopedPortJoint.scoped_unit_value (summary.ports .none) isValue
                  subst value
                  exact ⟨_, [.ticket owner], .retire owner scope tail⟩

theorem value_preserves
    (source : CheckedState operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue) :
    stack = .nil ∨ ∃ next completed remaining,
      RawStep ⟨value, scope, stack⟩ next [] completed ∧
      CheckedState operations policy contracts tables world outside next.scope next.expression next.stack output remaining row ∧
      demand = retiredTickets completed ++ remaining ∧
      Trace (available (ownedTickets stack)) (retiredTickets completed) (available (ownedTickets next.stack)) := by
  rcases value_progress source isValue with terminal | ⟨next, completed, step⟩
  · exact Or.inl terminal
  · obtain ⟨remaining, checked, same, created, transition⟩ := value_step_preserves source isValue step
    exact Or.inr ⟨next, completed, remaining, step, checked, same, transition⟩


namespace Examples
open RecursiveRecords.Examples (operations policy tables)
open RecursiveConsumption.Examples (contracts binding captured whole innerBoundary mixed_actual_resume mixed_resume_preserved)

def outerSpent : Stack := .spent 23 .unit .none .nil
def pending : Stack := innerBoundary.append outerSpent
def innerSpent : Stack := .spent 19 .unit .none outerSpent
def closing : Stack := .push (.closing 41 (.ticket 0 19)) innerSpent

theorem bind_plugged :
    RawStep ⟨.unit, .ticket 1 23, captured.append outerSpent⟩
      ⟨.bind 99 .unit (.discard 0), .ticket 0 19, pending⟩ [] [] ∧
    CheckedState operations policy contracts tables [] [] (.ticket 0 19)
      (.bind 99 .unit (.discard 0)) pending .unit [19] [] :=
  ⟨.plug binding .unit CallableProtection.Examples.unit_closed (.ticket 1 23) pending,
    plug_preserves mixed_resume_preserved CallableProtection.Examples.unit_closed⟩

theorem bind_reduced :
    RawStep ⟨.bind 99 .unit (.discard 0), .ticket 0 19, pending⟩
      ⟨.discard 0, .ticket 0 19, pending⟩ [] [] ∧
    CheckedState operations policy contracts tables [] [] (.ticket 0 19) (.discard 0) pending .unit [19] [] :=
  ⟨.bind 99 .unit (.discard 0) (.ticket 0 19) pending CallableProtection.Examples.unit_closed
      (by simp [ClosedExcept, Code.dependencies]),
    bind_preserves bind_plugged.2 CallableProtection.Examples.unit_closed⟩

theorem nested_disposed :
    RawStep ⟨.discard 0, .ticket 0 19, pending⟩ ⟨.unit, .ticket 0 19, closing⟩ [.close 41] [.ticket 19] ∧
    CheckedState operations policy contracts tables [] [] (.ticket 0 19) .unit closing .unit [] [] := by
  obtain ⟨remaining, checked, same, transition⟩ := RecursiveConsumption.discard_cut_preserves
    (front := .nil) bind_reduced.2 rfl (by rfl) 41
  have empty : remaining = [] := (List.cons.inj same).2.symm
  exact ⟨.discard 0 19 41 (.ticket 0 19) .none .unit .unit .nil .nil outerSpent [] rfl rfl,
    empty ▸ checked⟩

theorem closing_finished :
    RawStep ⟨.unit, .ticket 0 19, closing⟩ ⟨.unit, .ticket 0 19, innerSpent⟩ [] [.close 41] ∧
    CheckedState operations policy contracts tables [] [] (.ticket 0 19) .unit innerSpent .unit [] [] :=
  ⟨.finishClose 41 (.ticket 0 19) (.ticket 0 19) innerSpent, finish_close nested_disposed.2⟩

theorem inner_returned :
    RawStep ⟨.unit, .ticket 0 19, innerSpent⟩ ⟨.unit, .none, outerSpent⟩ [] [] ∧
    CheckedState operations policy contracts tables [] [] .none .unit outerSpent .unit [] [] :=
  ⟨.leaveClause 19 .unit .unit CallableProtection.Examples.unit_closed (.ticket 0 19) .none outerSpent,
    leave_clause closing_finished.2 trivial⟩

theorem outer_returned :
    RawStep ⟨.unit, .none, outerSpent⟩ ⟨.unit, .none, .nil⟩ [] [] ∧
    CheckedState operations policy contracts tables [] [] .none .unit .nil .unit [] [] :=
  ⟨.leaveClause 23 .unit .unit CallableProtection.Examples.unit_closed .none .none .nil,
    leave_clause inner_returned.2 trivial⟩

def initial : RunState := ⟨⟨.resume 1 .unit, .ticket 1 23, whole⟩, [.ticket 23, .ticket 19], []⟩
def terminal : RunState := ⟨⟨.unit, .none, .nil⟩, [.ticket 23, .ticket 19, .close 41], [.close 41, .ticket 19, .ticket 23]⟩

theorem mixed_trace : RawTrace initial.configuration terminal.configuration [.close 41] [.close 41, .ticket 19, .ticket 23] :=
  .next mixed_actual_resume.1 (.next bind_plugged.1 (.next bind_reduced.1 (.next nested_disposed.1
    (.next closing_finished.1 (.next inner_returned.1 (.next outer_returned.1 (.refl _)))))))

theorem mixed_execution : RunSteps initial terminal :=
  raw_trace_enacts mixed_trace (issued := [.ticket 23, .ticket 19]) (completed := []) (by decide)

theorem initial_ledger : Ledger initial.erase := ⟨.refl _, by decide⟩

theorem terminal_ledger : Ledger terminal.erase :=
  run_steps_preserve_ledger mixed_execution initial_ledger

/-- This complete concrete run preserves the recursive check at each state and
    the actual lifetime ledger. The initial captured state is supplied, not
    derived from general handler installation. -/
theorem mixed_completion :
    RunSteps initial terminal ∧
    CheckedState operations policy contracts tables [] [] terminal.configuration.scope
      terminal.configuration.expression terminal.configuration.stack .unit [] [] ∧
    terminal.configuration.expression.IsValue ∧ terminal.configuration.stack = .nil ∧
    terminal.completed.Nodup :=
  ⟨mixed_execution, outer_returned.2, trivial, rfl, ledger_no_double_completion terminal_ledger⟩

end Examples

end Ash.OneShot.RecursiveExecution

#print axioms Ash.OneShot.RecursiveExecution.check_state
#print axioms Ash.OneShot.RecursiveExecution.replace_current
#print axioms Ash.OneShot.RecursiveExecution.bind_preserves
#print axioms Ash.OneShot.RecursiveExecution.beta_preserves
#print axioms Ash.OneShot.RecursiveExecution.branch_preserves
#print axioms Ash.OneShot.RecursiveExecution.ready_step_preserves
#print axioms Ash.OneShot.RecursiveExecution.ready_progress
#print axioms Ash.OneShot.RecursiveExecution.ready_preserves
#print axioms Ash.OneShot.RecursiveExecution.focus_preserves
#print axioms Ash.OneShot.RecursiveExecution.plug_preserves
#print axioms Ash.OneShot.RecursiveExecution.value_closed
#print axioms Ash.OneShot.RecursiveExecution.plug_progress
#print axioms Ash.OneShot.RecursiveExecution.value_pending
#print axioms Ash.OneShot.RecursiveExecution.value_configuration
#print axioms Ash.OneShot.RecursiveExecution.start_cleanup
#print axioms Ash.OneShot.RecursiveExecution.finish_cleanup
#print axioms Ash.OneShot.RecursiveExecution.finish_close
#print axioms Ash.OneShot.RecursiveExecution.retire
#print axioms Ash.OneShot.RecursiveExecution.leave_handler
#print axioms Ash.OneShot.RecursiveExecution.leave_cell
#print axioms Ash.OneShot.RecursiveExecution.leave_clause
#print axioms Ash.OneShot.RecursiveExecution.value_step_preserves
#print axioms Ash.OneShot.RecursiveExecution.value_progress
#print axioms Ash.OneShot.RecursiveExecution.value_preserves

#print axioms Ash.OneShot.RecursiveExecution.Examples.bind_plugged
#print axioms Ash.OneShot.RecursiveExecution.Examples.bind_reduced
#print axioms Ash.OneShot.RecursiveExecution.Examples.nested_disposed
#print axioms Ash.OneShot.RecursiveExecution.Examples.closing_finished
#print axioms Ash.OneShot.RecursiveExecution.Examples.inner_returned
#print axioms Ash.OneShot.RecursiveExecution.Examples.outer_returned
#print axioms Ash.OneShot.RecursiveExecution.Examples.mixed_trace
#print axioms Ash.OneShot.RecursiveExecution.Examples.mixed_execution
#print axioms Ash.OneShot.RecursiveExecution.Examples.initial_ledger
#print axioms Ash.OneShot.RecursiveExecution.Examples.terminal_ledger
#print axioms Ash.OneShot.RecursiveExecution.Examples.mixed_completion

#print axioms Ash.OneShot.RecursiveExecution.value_source_configuration
