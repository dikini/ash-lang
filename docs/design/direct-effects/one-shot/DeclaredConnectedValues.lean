import DeclaredConnectedHandlers

/-! Returned values keep the actual structural pending-segment derivation.
Value transport changes only the current value's immediate allowed row; it does
not reconstruct or independently choose stored context annotations.
-/
namespace Ash.OneShot.DeclaredConnectedSources
open ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available spendAll Trace)
open RecursiveCompletion (empty_head retiredTickets)

theorem value_pending
    (state : State operations policy contracts tables actions world outside scope value stack output demand row)
    (isValue : value.IsValue) :
    ∃ (input : Value) (incoming : List Instance) (requirements : Requirements demand)
      (records disposals : RecursiveRequirements.Store),
      DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty [] value input ∧
      ScopedPorts.EffectScopeKnown contracts.ports scope ∧
      Segment operations policy contracts tables actions world stack input output demand requirements records incoming [] ∧
      DeclaredSourceClosing.Records operations policy contracts tables world stack disposals ∧
      (ownedTickets stack).Nodup ∧ Checked (records ++ disposals) [] (available (ownedTickets stack)) requirements row ∧
      ProtectionContracts.checkFootprint outside row = true := by
  cases state with
  | checked current scopeTyped pending closing unique checked accepted accounting =>
      subst demand
      have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase current) isValue
      subst_vars
      have summary := DeclaredSourceValues.change_allowed (DeclaredSourceValues.value_summary current isValue) isValue []
      refine ⟨_, _, _, _, _, summary, ⟨_, scopeTyped⟩, pending, closing, unique, RecursiveRequirements.evaluate_sound ?_, accepted⟩
      have evaluation := RecursiveRequirements.checked_complete checked
      simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase current) isValue, spendAll,
        RecursiveRecomposition.merge_empty_left] using evaluation

theorem value_configuration
    (summary : DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty [] code input)
    (isValue : code.IsValue)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (pending : Segment operations policy contracts tables actions world stack input output demand requirements records incoming [])
    (closing : DeclaredSourceClosing.Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (records ++ disposals) [] (available (ownedTickets stack)) requirements row)
    (accepted : ProtectionContracts.checkFootprint outside row = true) :
    State operations policy contracts tables actions world outside scope code stack output demand row := by
  have current : Checked (records ++ disposals) [] (available (ownedTickets stack))
      ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables stack)) [] :=
    Checked.request (row := []) (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  exact .checked (DeclaredSourceValues.expression (DeclaredSourceValues.change_allowed summary isValue incoming) _) scopeTyped
    pending closing unique (by simpa only [List.nil_append] using Checked.sequence current checked) accepted rfl

theorem finish_cleanup
    (state : State operations policy contracts tables actions world outside scope .unit
      (.push (.running action value closed) tail) output demand row) :
    State operations policy contracts tables actions world outside action.scope value tail output demand row := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    unique, checked, accepted⟩ := value_pending state trivial
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
      | retained kind source interface => cases source with
          | running scopeKnown callback saved annotation =>
              obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
              exact value_configuration saved closed.1 scopeTyped rest closing unique (empty_head checked) accepted

theorem finish_close
    (state : State operations policy contracts tables actions world outside scope .unit
      (.push (.closing identity caller) tail) output demand row) :
    State operations policy contracts tables actions world outside caller .unit tail output demand row := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    unique, checked, accepted⟩ := value_pending state trivial
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
      | retained kind source interface => cases source with
          | closing scopeKnown =>
              obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
              exact value_configuration .summaryUnit trivial scopeTyped rest closing unique (empty_head checked) accepted

theorem leave_handler
    (state : State operations policy contracts tables actions world outside scope value
      (.push (.handler handler) tail) output demand row) (isValue : value.IsValue) :
    State operations policy contracts tables actions world outside handler.scope value tail output demand row := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    unique, checked, accepted⟩ := value_pending state isValue
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
      | retained kind source interface => cases kind
      | handler scope annotation clauses coverage uniqueClauses declarations capabilities modes =>
          obtain ⟨ticket, scopeTyped⟩ := scope
          exact value_configuration summary isValue scopeTyped rest closing unique (empty_head checked) accepted

theorem leave_cell
    (state : State operations policy contracts tables actions world outside scope value
      (.push (.cell identity payload caller answer) tail) output demand row) (isValue : value.IsValue) :
    State operations policy contracts tables actions world outside caller value tail output demand row := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    unique, checked, accepted⟩ := value_pending state isValue
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
      | retained kind source interface => cases source with
          | cell scopeKnown noEscape annotation =>
              obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
              exact value_configuration summary isValue scopeTyped rest closing unique (empty_head checked) accepted

theorem leave_clause
    (state : State operations policy contracts tables actions world outside scope value
      (.spent owner answer caller tail) output demand row) (isValue : value.IsValue) :
    State operations policy contracts tables actions world outside caller value tail output demand row := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    unique, checked, accepted⟩ := value_pending state isValue
  cases closing with
  | spent closing => cases pending with
  | spent known annotation scope rest bound =>
      obtain ⟨firstRow, tailRow, firstCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have evaluated := RecursiveRequirements.checked_complete firstCheck
      simp only [RecursiveRecomposition.evaluate_spent] at evaluated
      split at evaluated
      · have firstEmpty := Option.some.inj evaluated.symm
        subst firstRow
        obtain ⟨ticket, scopeTyped⟩ := scope
        exact value_configuration summary isValue scopeTyped rest closing unique
          (by simpa only [same, List.nil_append, spendAll, ownedTickets] using tailCheck) accepted
      · cases evaluated

theorem start_cleanup
    (state : State operations policy contracts tables actions world outside scope value
      (.push (.armed action) tail) output demand row)
    (closed : ClosedValue value) :
    State operations policy contracts tables actions world outside .none (.app action.action .unit)
      (.push (.running action value closed) tail) output demand row := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, scopeTyped, pending, closing,
    unique, checked, accepted⟩ := value_pending state closed.1
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
      | retained kind source interface => cases source with
          | armed scopeKnown callback annotation =>
              rename_i latent
              cases interface with
              | armed caller callable requests =>
                  obtain ⟨callbackRow, tailRow, callbackCheck, tailCheck, same⟩ :=
                    RecursiveRequirements.checked_sequence_parts checked
                  have exported := RecursiveRequirements.checked_complete callbackCheck
                  simp only [RecursiveRequirements.evaluate_prepend, RecursiveContexts.evaluate_request, List.append_nil] at exported
                  have invocation : DeclaredSources.Callable operations policy contracts world Environment.empty
                      action.requests (.app action.action .unit) .unit latent :=
                    .summaryApp (DeclaredSourceValues.change_allowed callback action.closed.1 action.requests)
                      .summaryUnit (fun _ member => member)
                  have currentCheck : Checked (records ++ disposals)
                      (OwnerPhases.ofStack tables (.push (.running action value closed) tail))
                      (available (ownedTickets tail)) (.request [] latent) callbackRow := by
                    apply Checked.request
                    simpa only [List.nil_append, RecursiveCompletion.running_export, ownedTickets] using exported
                  have currentPrefixed : Checked (records ++ disposals) [] (available (ownedTickets tail))
                      ((Requirements.request [] latent).prepend
                        (OwnerPhases.ofStack tables (.push (.running action value closed) tail))) callbackRow :=
                    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)
                  have empty : Checked (records ++ disposals) [] (available (ownedTickets tail))
                      ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables tail)) [] :=
                    Checked.request (row := []) (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
                  have savedTyped : ScopedPorts.Typed operations.ports world ScopedPorts.TypeEnv.empty .none [] value
                      (ScopedPorts.eraseType action.answer) := by
                    have environmentSame : Environment.empty.ports = ScopedPorts.TypeEnv.empty := by funext name; rfl
                    simpa only [← annotation, environmentSame] using (DeclaredSourceValues.erase summary).ports .none
                  have nextPending := Checked.sequence empty tailCheck
                  rw [same] at accepted ⊢
                  exact .checked (.callable invocation) .none
                    (.push (.retained .running (.running scopeKnown callback summary annotation)
                      (.running caller callable savedTyped requests)) rest requests)
                    (.push closing) unique
                    (by simpa only [List.nil_append, ownedTickets] using Checked.sequence currentPrefixed nextPending)
                    accepted rfl

theorem retire
    (state : State operations policy contracts tables actions world outside scope .unit
      (.push (.retiring owner) tail) output demand row) :
    ∃ remaining, demand = owner :: remaining ∧
      State operations policy contracts tables actions world outside scope .unit tail output remaining row ∧
      Trace (available (ownedTickets (.push (.retiring owner) tail))) [owner] (available (ownedTickets tail)) := by
  obtain ⟨input, incoming, requirements, records, disposals, summary, ⟨ticket, scopeTyped⟩, pending, closing,
    unique, checked, accepted⟩ := value_pending state trivial
  cases closing with
  | push closing => cases pending with
  | push head rest bound => cases head with
      | retained kind source interface => cases source with
          | retiring known =>
              obtain ⟨firstRow, tailRow, firstCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
              have ready := OwnerPhaseTransitions.trace_available (RecursiveRequirements.checked_trace firstCheck) owner List.mem_cons_self
              have firstEmpty : firstRow = [] := by
                have evaluated := RecursiveRequirements.checked_complete firstCheck
                simpa only [Requirements.prepend, RecursiveClosing.evaluate_retire, if_pos ready, Option.some.injEq] using evaluated.symm
              subst firstRow
              have phases := OwnerPhaseTransitions.spend_available_cons (List.nodup_cons.mp unique).1
              have next := tailCheck
              simp only [spendAll, ownedTickets, phases] at next
              refine ⟨_, rfl, ?_, .cons ready ?_⟩
              · exact value_configuration .summaryUnit trivial scopeTyped rest closing (List.nodup_cons.mp unique).2
                  (by simpa only [same, List.nil_append] using next) accepted
              · simpa only [ownedTickets, phases] using (Trace.nil (before := available (ownedTickets tail)))

theorem value_state_preserves
    (state : State operations policy contracts tables actions world outside scope value stack output demand row)
    (isValue : value.IsValue)
    (step : RawStep ⟨value, scope, stack⟩ next created completed) :
    ∃ remaining, State operations policy contracts tables actions world outside next.scope next.expression next.stack output remaining row ∧
      demand = retiredTickets completed ++ remaining ∧ created = [] ∧
      Trace (available (ownedTickets stack)) (retiredTickets completed) (available (ownedTickets next.stack)) := by
  cases step <;> try cases isValue
  case focus => exact False.elim (ScopedPorts.focus_is_not_value (by assumption) isValue)
  case plug => exact ⟨_, plug state (by assumption), rfl, rfl, .nil⟩
  case leaveHandler => exact ⟨_, leave_handler state (show ClosedValue _ from by assumption).1, rfl, rfl, .nil⟩
  case leaveCell => exact ⟨_, leave_cell state (show ClosedValue _ from by assumption).1, rfl, rfl, .nil⟩
  case startCleanup => exact ⟨_, start_cleanup state (by assumption), rfl, rfl, .nil⟩
  case finishCleanup => exact ⟨_, finish_cleanup state, rfl, rfl, .nil⟩
  case leaveClause => exact ⟨_, leave_clause state (show ClosedValue _ from by assumption).1, rfl, rfl, .nil⟩
  case finishClose => exact ⟨_, finish_close state, rfl, rfl, .nil⟩
  case retire =>
    obtain ⟨remaining, same, checked, transition⟩ := retire state
    exact ⟨remaining, checked, same, rfl, transition⟩

theorem value_step_preserves
    (before : Run operations declarations policy registry tables state output demand row bound)
    (isValue : state.execution.configuration.expression.IsValue)
    (raw : RawStep state.execution.configuration after created discharged) :
    ∃ remaining,
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after created discharged) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after created discharged) output remaining row bound ∧
      demand = retiredTickets discharged ++ remaining ∧ created = [] := by
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  obtain ⟨remaining, next, accounting, noCreated, trace⟩ := value_state_preserves source isValue raw
  subst created
  obtain ⟨oldRemaining, step, current, oldAccounting, empty⟩ :=
    DeclaredExecution.value_step_preserves before.current isValue raw
  have freshOwners : (state.execution.issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  refine ⟨remaining, step, ?_, accounting, rfl⟩
  apply assemble_entry before.current raw freshOwners current.names.unique step.checks usage history retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

theorem value_progress
    (before : Run operations declarations policy registry tables state output demand row bound)
    (isValue : state.execution.configuration.expression.IsValue) :
    state.execution.configuration.stack = .nil ∨
    ∃ after discharged remaining,
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] discharged) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] discharged) output remaining row bound ∧
      demand = retiredTickets discharged ++ remaining := by
  rcases DeclaredSourceStates.value_progress before.current.source isValue with terminal | ⟨after, discharged, raw⟩
  · exact Or.inl terminal
  · obtain ⟨remaining, step, next, accounting, empty⟩ := value_step_preserves before isValue raw
    exact Or.inr ⟨after, discharged, remaining, step, next, accounting⟩

end Ash.OneShot.DeclaredConnectedSources

#print axioms Ash.OneShot.DeclaredConnectedSources.value_pending
#print axioms Ash.OneShot.DeclaredConnectedSources.value_configuration
#print axioms Ash.OneShot.DeclaredConnectedSources.finish_cleanup
#print axioms Ash.OneShot.DeclaredConnectedSources.finish_close
#print axioms Ash.OneShot.DeclaredConnectedSources.leave_handler
#print axioms Ash.OneShot.DeclaredConnectedSources.leave_cell
#print axioms Ash.OneShot.DeclaredConnectedSources.leave_clause
#print axioms Ash.OneShot.DeclaredConnectedSources.start_cleanup
#print axioms Ash.OneShot.DeclaredConnectedSources.retire
#print axioms Ash.OneShot.DeclaredConnectedSources.value_state_preserves
#print axioms Ash.OneShot.DeclaredConnectedSources.value_step_preserves
#print axioms Ash.OneShot.DeclaredConnectedSources.value_progress
