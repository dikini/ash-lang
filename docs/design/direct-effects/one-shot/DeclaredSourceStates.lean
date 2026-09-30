import DeclaredSourceClosing
import DeclaredSourceContexts
import DeclaredSourceExpressions

/-! Checked states retaining hereditary evidence in current code and every
active or saved frame, including exact hereditary closing records. Erasure
recovers RecursiveRecords and its checker. This does not assert preservation
of every step. -/
namespace Ash.OneShot.DeclaredSourceStates
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSources (Expression)
open DeclaredSourceFrames (Segment)
open DeclaredSourceClosing (Records)
open RecursiveRequirements (Requirements Store Checked evaluate)
open OwnerPhaseTransitions (Phases Trace available spend spendAll)
open DeclaredSourceContexts (focus_decompose context_plug)
open DeclaredSourceExpressions (bind_expression beta_expression branch_expression)
open RecursiveExpressions (spend_permutation Ready ready_not_value ready_not_focus)
open RecursiveContexts (prepare_plain plain_context plain_owners evaluate_plain)
open RecursiveCompletion (empty_head running_export retiredTickets)

inductive Configuration (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    Execution.Scope → Code → Stack → Value → (demand : List Nat) → Requirements demand → Store → Prop where
  | checked (current : Expression operations policy contracts world allowed scope Environment.empty code input currentDemand currentRequirements)
      (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
      (pending : Segment operations policy contracts tables world stack input output pendingDemand pendingRequirements records) :
      Configuration operations policy contracts tables world scope code stack output (currentDemand ++ pendingDemand)
        (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) records

inductive CheckedState (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (outside : ProtectionContracts.Context)
    (scope : Execution.Scope) (code : Code) (stack : Stack) (output : Value) (demand : List Nat) (row : Footprint) : Prop where
  | checked (source : Configuration operations policy contracts tables world scope code stack output demand requirements resumes)
      (closing : Records operations policy contracts tables world stack disposals)
      (unique : (ownedTickets stack).Nodup)
      (evaluated : Checked (resumes ++ disposals) [] (available (ownedTickets stack)) requirements row)
      (accepted : checkFootprint outside row = true) :
      CheckedState operations policy contracts tables world outside scope code stack output demand row

theorem configuration_erase
    (source : Configuration operations policy contracts tables world scope code stack output demand requirements resumes) :
    SourceTemplates.Configuration operations policy contracts tables world scope code stack output demand requirements resumes := by
  cases source with
  | checked current scopeTyped pending =>
      exact .checked (DeclaredSources.expression_erase current) scopeTyped pending.erase

theorem checked_state_erase
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row) :
    RecursiveRecords.CheckedState operations policy contracts tables world outside scope code stack output demand row := by
  cases source with
  | checked current closing unique checked accepted =>
      exact .checked (configuration_erase current) (DeclaredSourceClosing.records_erase closing) unique checked accepted

theorem check_state
    (source : Configuration operations policy contracts tables world scope code stack output demand requirements resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (evaluated : evaluate (resumes ++ disposals) [] (available (ownedTickets stack)) requirements = some row)
    (accepted : checkFootprint outside row = true) :
    CheckedState operations policy contracts tables world outside scope code stack output demand row :=
  .checked source closing unique (RecursiveRequirements.evaluate_sound evaluated) accepted

theorem replace_current {requirements : Requirements currentDemand}
    (replacement : Expression operations policy contracts world allowed nextScope Environment.empty next input currentDemand reduced)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports nextScope nextTicket)
    (pending : Segment operations policy contracts tables world stack input output pendingDemand pendingRequirements records)
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
    (ready : Ready code) : ∃ next, RawStep ⟨code, scope, stack⟩ next [] [] :=
  RecursiveExecution.ready_progress (checked_state_erase source) ready

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
        obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ := prepare_plain (DeclaredSources.expression_erase current) focus scopeTyped input
        have frame : DeclaredSourceFrames.Frame operations policy contracts tables world (.plain plain) input _ restDemand restReq :=
          .plain (by simpa only [contextSame, scopeSame] using context)
            (by simpa only [scopeSame] using scopeTyped) inputAnnotation outputAnnotation
        have step : RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] := by
          simpa only [scopeSame] using RawStep.focus plain (by simpa only [contextSame] using focus) stack
        refine ⟨plain, step, ?_, contextSame, scopeSame, .nil⟩
        rw [sameDemand, List.append_assoc]
        apply check_state (.checked childSource scopeTyped (DeclaredSourceFrames.push frame pending)) (.push closing) unique _ accepted
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
        have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase current) closed.1
        subst_vars
        cases closing with
        | push closing => cases pending with
        | push frame erasedFrame pending => cases frame with
          | plain context frameScope inputAnnotation outputAnnotation =>
              obtain ⟨combined, combinedSource, evaluation⟩ := context_plug context
                (DeclaredSourceValues.expression (DeclaredSourceValues.change_allowed (DeclaredSourceValues.value_summary current closed.1) closed.1 _) _)
              apply check_state (.checked combinedSource frameScope pending) closing unique _ accepted
              have oldEvaluation := RecursiveRequirements.checked_complete checked
              simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase current) closed.1, RecursiveRecomposition.merge_empty_left,
                spendAll, plain_owners] at oldEvaluation
              simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
                RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left, spendAll]
              exact oldEvaluation

theorem value_closed
    (source : CheckedState operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue) : ClosedValue value :=
  RecursiveExecution.value_closed (checked_state_erase source) isValue

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


theorem value_pending
    (source : CheckedState operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue) :
    ∃ (input : Value) (requirements : Requirements demand) (records disposals : RecursiveRequirements.Store),
      DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty [] value input ∧
      ScopedPorts.EffectScopeKnown contracts.ports scope ∧
      Segment operations policy contracts tables world stack input output demand requirements records ∧
      Records operations policy contracts tables world stack disposals ∧
      (ownedTickets stack).Nodup ∧ Checked (records ++ disposals) [] (available (ownedTickets stack)) requirements row ∧
      checkFootprint outside row = true := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase current) isValue
        subst_vars
        have summary := DeclaredSourceValues.change_allowed (DeclaredSourceValues.value_summary current isValue) isValue []
        refine ⟨_, _, _, _, summary, ⟨_, scopeTyped⟩, pending, closing, unique, RecursiveRequirements.evaluate_sound ?_, accepted⟩
        have evaluation := RecursiveRequirements.checked_complete checked
        simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
          RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase current) isValue, spendAll, RecursiveRecomposition.merge_empty_left] using evaluation

theorem value_source_configuration
    (summary : DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty allowed code input)
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
  exact .checked (.checked (currentDemand := []) (pendingDemand := demand) (DeclaredSourceValues.expression summary _) scopeTyped pending) closing unique
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
  value_source_configuration (DeclaredSourceValues.from_legacy summary) scopeTyped pending closing unique checked accepted

theorem start_cleanup
    (source : CheckedState operations policy contracts tables world outside scope value (.push (.armed action) tail) output demand row)
    (closed : ClosedValue value) :
    CheckedState operations policy contracts tables world outside .none (.app action.action .unit)
      (.push (.running action value closed) tail) output demand row := by
  obtain ⟨input, requirements, records, disposals, summary, scopeTyped, pending, closing, unique, checked, accepted⟩ := value_pending source closed.1
  cases closing with
  | push closing => cases pending with
  | push head erasedHead rest => cases head with
      | armed scopeKnown callback annotation =>
          rename_i tailDemand tailRequirements latent
          obtain ⟨callbackRow, tailRow, callbackCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
          have exported := RecursiveRequirements.checked_complete callbackCheck
          simp only [RecursiveRequirements.evaluate_prepend, RecursiveContexts.evaluate_request, List.append_nil] at exported
          have invocation : DeclaredSources.Callable operations policy contracts world Environment.empty action.requests (.app action.action .unit) .unit latent :=
            .summaryApp (DeclaredSourceValues.change_allowed callback action.closed.1 action.requests)
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
            (DeclaredSourceFrames.push (.running scopeKnown callback summary annotation) rest)) (.push closing) unique
            (by simpa only [List.nil_append, ownedTickets] using Checked.sequence currentPrefixed nextPending) accepted

theorem finish_cleanup
    (source : CheckedState operations policy contracts tables world outside scope .unit
      (.push (.running action value closed) tail) output demand row) :
    CheckedState operations policy contracts tables world outside action.scope value tail output demand row := by
  obtain ⟨input, requirements, records, disposals, summary, scopeTyped, pending, closing, unique, checked, accepted⟩ := value_pending source trivial
  cases closing with
  | push closing => cases pending with
  | push head erasedHead rest => cases head with
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
  | push head erasedHead rest => cases head with
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
  | push head erasedHead rest => cases head with
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
  | push head erasedHead rest => cases head with
      | handler typed annotation declarations capabilities modes => cases typed with
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
  | push head erasedHead rest => cases head with
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
    stack = .nil ∨ ∃ next completed, RawStep ⟨value, scope, stack⟩ next [] completed :=
  RecursiveExecution.value_progress (checked_state_erase source) isValue

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



end Ash.OneShot.DeclaredSourceStates

#print axioms Ash.OneShot.DeclaredSourceStates.configuration_erase
#print axioms Ash.OneShot.DeclaredSourceStates.checked_state_erase
#print axioms Ash.OneShot.DeclaredSourceStates.check_state
#print axioms Ash.OneShot.DeclaredSourceStates.replace_current
#print axioms Ash.OneShot.DeclaredSourceStates.focus_preserves
#print axioms Ash.OneShot.DeclaredSourceStates.plug_preserves
#print axioms Ash.OneShot.DeclaredSourceStates.value_closed
#print axioms Ash.OneShot.DeclaredSourceStates.plug_progress
#print axioms Ash.OneShot.DeclaredSourceStates.bind_preserves
#print axioms Ash.OneShot.DeclaredSourceStates.beta_preserves
#print axioms Ash.OneShot.DeclaredSourceStates.branch_preserves
#print axioms Ash.OneShot.DeclaredSourceStates.ready_step_preserves
#print axioms Ash.OneShot.DeclaredSourceStates.ready_progress
#print axioms Ash.OneShot.DeclaredSourceStates.ready_preserves
#print axioms Ash.OneShot.DeclaredSourceStates.value_pending
#print axioms Ash.OneShot.DeclaredSourceStates.value_source_configuration
#print axioms Ash.OneShot.DeclaredSourceStates.value_configuration
#print axioms Ash.OneShot.DeclaredSourceStates.start_cleanup
#print axioms Ash.OneShot.DeclaredSourceStates.finish_cleanup
#print axioms Ash.OneShot.DeclaredSourceStates.finish_close
#print axioms Ash.OneShot.DeclaredSourceStates.retire
#print axioms Ash.OneShot.DeclaredSourceStates.leave_handler
#print axioms Ash.OneShot.DeclaredSourceStates.leave_cell
#print axioms Ash.OneShot.DeclaredSourceStates.leave_clause
#print axioms Ash.OneShot.DeclaredSourceStates.value_step_preserves
#print axioms Ash.OneShot.DeclaredSourceStates.value_progress
#print axioms Ash.OneShot.DeclaredSourceStates.value_preserves
