import RecursiveClosing

/-!
Actual cleanup and value-completion transitions preserve the current recursive
source check. These are execution joins; admission of live disposal records and
the full resource/access and name-history invariants remain separate obligations.
-/

namespace Ash.OneShot.RecursiveCompletion
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open SourceTemplates (Expression Segment CheckedConfiguration)
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (Phases Trace available spend spendAll)

/-- A value contributes no owner demand or immediate effect. Its complete
    current-state check therefore supplies the pending segment's exact check. -/
theorem value_pending
    (source : CheckedConfiguration operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue) :
    ∃ (input : Value) (requirements : Requirements demand) (records : RecursiveRequirements.Store),
      SourceTemplates.ValueSummary operations policy contracts world Environment.empty [] value input ∧
      ScopedPorts.EffectScopeKnown contracts.ports scope ∧
      Segment operations policy contracts tables world stack input output demand requirements records ∧
      (ownedTickets stack).Nodup ∧ Checked records [] (available (ownedTickets stack)) requirements row ∧
      checkFootprint outside row = true := by
  cases source with
  | checked source unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        have empty := SourceTemplates.expression_value_demand current isValue
        subst_vars
        have summary := (RecursiveRecomposition.value_summary current isValue).change_allowed isValue []
        refine ⟨_, _, _, summary, ⟨_, scopeTyped⟩, pending, unique, RecursiveRequirements.evaluate_sound ?_, accepted⟩
        have evaluation := RecursiveRequirements.checked_complete checked
        simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
          RecursiveRecomposition.value_evaluation current isValue, spendAll, RecursiveRecomposition.merge_empty_left] using evaluation

theorem value_source_configuration
    (summary : SourceTemplates.ValueSummary operations policy contracts world Environment.empty allowed code input)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (pending : Segment operations policy contracts tables world stack input output demand requirements records)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked records [] (available (ownedTickets stack)) requirements row)
    (accepted : checkFootprint outside row = true) :
    CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row := by
  have current : Checked records [] (available (ownedTickets stack))
      ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables stack)) [] :=
    Checked.request (row := []) (by simp [OwnerSource.exportAt, residual_empty])
  exact .checked (.checked (currentDemand := []) (pendingDemand := demand) (summary.expression _) scopeTyped pending) unique
    (by simpa only [List.nil_append] using Checked.sequence current checked) accepted

theorem value_configuration
    (summary : Summary operations world Environment.empty allowed code input [])
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (pending : Segment operations policy contracts tables world stack input output demand requirements records)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked records [] (available (ownedTickets stack)) requirements row)
    (accepted : checkFootprint outside row = true) :
    CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row :=
  value_source_configuration (.stable summary) scopeTyped pending unique checked accepted

theorem empty_head
    (checked : Checked records receiving before
      (.sequence ((Requirements.request [] []).prepend nearer) requirements) row) :
    Checked records receiving before requirements row := by
  apply RecursiveRequirements.evaluate_sound
  have evaluated := RecursiveRequirements.checked_complete checked
  simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
    RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left] using evaluated

theorem running_export (action : ActionData) (value : Code) (closed : ClosedValue value) :
    OwnerSource.exportAt (OwnerPhases.ofStack tables (.push (.running action value closed) tail)) before latent =
      OwnerSource.exportAt (OwnerPhases.ofStack tables tail) before (qualify true latent) := by
  simp only [OwnerPhases.ofStack, OwnerPhases.frameEntry, ExecFrame.erase, ActionData.erase,
    ProtectionContexts.frameProtected, OwnerPhaseTransitions.project, OwnerSource.exportAt,
    residualize, DisposalProtection.through_barrier]

theorem start_cleanup
    (source : CheckedConfiguration operations policy contracts tables world outside scope value (.push (.armed action) tail) output demand row)
    (closed : ClosedValue value) :
    CheckedConfiguration operations policy contracts tables world outside .none (.app action.action .unit)
      (.push (.running action value closed) tail) output demand row := by
  obtain ⟨input, requirements, records, summary, scopeTyped, pending, unique, checked, accepted⟩ := value_pending source closed.1
  cases pending with
  | push head rest => cases head with
      | armed scopeKnown callback annotation =>
          rename_i tailDemand tailRequirements latent
          obtain ⟨callbackRow, tailRow, callbackCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
          have exported := RecursiveRequirements.checked_complete callbackCheck
          simp only [RecursiveRequirements.evaluate_prepend, RecursiveContexts.evaluate_request, List.append_nil] at exported
          have invocation : SourceTemplates.CallableSummary operations policy contracts world Environment.empty action.requests (.app action.action .unit) .unit latent :=
            .summaryApp (SourceCallableTransport.value_callable (callback.change_allowed action.closed.1 action.requests))
              .summaryUnit (fun _ member => member)
          have currentCheck : Checked records (OwnerPhases.ofStack tables (.push (.running action value closed) tail))
              (available (ownedTickets tail)) (.request [] latent) callbackRow := by
            apply Checked.request
            simpa only [List.nil_append, running_export, ownedTickets] using exported
          have currentPrefixed : Checked records [] (available (ownedTickets tail))
              ((Requirements.request [] latent).prepend (OwnerPhases.ofStack tables (.push (.running action value closed) tail))) callbackRow :=
            RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)
          have empty : Checked records [] (available (ownedTickets tail))
              ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables tail)) [] :=
            Checked.request (row := []) (by simp [OwnerSource.exportAt, residual_empty])
          have nextPending := Checked.sequence empty tailCheck
          rw [same] at accepted ⊢
          exact .checked (.checked (currentDemand := []) (pendingDemand := _) (.callable invocation) .none
            (.push (.running scopeKnown callback summary annotation) rest)) unique
            (by simpa only [List.nil_append, ownedTickets] using Checked.sequence currentPrefixed nextPending) accepted

theorem finish_cleanup
    (source : CheckedConfiguration operations policy contracts tables world outside scope .unit
      (.push (.running action value closed) tail) output demand row) :
    CheckedConfiguration operations policy contracts tables world outside action.scope value tail output demand row := by
  obtain ⟨input, requirements, records, summary, scopeTyped, pending, unique, checked, accepted⟩ := value_pending source trivial
  cases pending with
  | push head rest => cases head with
      | running scopeKnown callback saved annotation =>
          obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
          exact value_source_configuration saved scopeTyped rest unique (empty_head checked) accepted

theorem finish_close
    (source : CheckedConfiguration operations policy contracts tables world outside scope .unit
      (.push (.closing identity caller) tail) output demand row) :
    CheckedConfiguration operations policy contracts tables world outside caller .unit tail output demand row := by
  obtain ⟨input, requirements, records, summary, scopeTyped, pending, unique, checked, accepted⟩ := value_pending source trivial
  cases pending with
  | push head rest => cases head with
      | closing scopeKnown =>
          obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
          exact value_configuration (allowed := []) .unit scopeTyped rest unique (empty_head checked) accepted

theorem retire
    (source : CheckedConfiguration operations policy contracts tables world outside scope .unit
      (.push (.retiring owner) tail) output demand row) :
    ∃ remaining, demand = owner :: remaining ∧
      CheckedConfiguration operations policy contracts tables world outside scope .unit tail output remaining row ∧
      Trace (available (ownedTickets (.push (.retiring owner) tail))) [owner] (available (ownedTickets tail)) := by
  obtain ⟨input, requirements, records, summary, ⟨ticket, scopeTyped⟩, pending, unique, checked, accepted⟩ := value_pending source trivial
  cases pending with
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
          have next : Checked records [] (available (ownedTickets tail)) tailRequirements tailRow := by
            simpa only [spendAll, ownedTickets, phases] using tailCheck
          refine ⟨_, rfl, ?_, .cons ready ?_⟩
          · exact value_configuration (allowed := []) .unit scopeTyped rest (List.nodup_cons.mp unique).2
              (by simpa only [same, List.nil_append] using next) accepted
          · simpa only [ownedTickets, phases] using (Trace.nil (before := available (ownedTickets tail)))


theorem leave_handler
    (source : CheckedConfiguration operations policy contracts tables world outside scope value
      (.push (.handler handler) tail) output demand row) (isValue : value.IsValue) :
    CheckedConfiguration operations policy contracts tables world outside handler.scope value tail output demand row := by
  obtain ⟨input, requirements, records, summary, scopeTyped, pending, unique, checked, accepted⟩ := value_pending source isValue
  cases pending with
  | push head rest => cases head with
      | handler typed annotation => cases typed with
          | handler scopeKnown clauses coverage distinct =>
              obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
              exact value_source_configuration summary scopeTyped rest unique (empty_head checked) accepted

theorem leave_cell
    (source : CheckedConfiguration operations policy contracts tables world outside scope value
      (.push (.cell identity payload caller answer) tail) output demand row) (isValue : value.IsValue) :
    CheckedConfiguration operations policy contracts tables world outside caller value tail output demand row := by
  obtain ⟨input, requirements, records, summary, scopeTyped, pending, unique, checked, accepted⟩ := value_pending source isValue
  cases pending with
  | push head rest => cases head with
      | cell scopeKnown noEscape annotation =>
          obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
          exact value_source_configuration summary scopeTyped rest unique (empty_head checked) accepted

theorem leave_clause
    (source : CheckedConfiguration operations policy contracts tables world outside scope value
      (.spent owner answer caller tail) output demand row) (isValue : value.IsValue) :
    CheckedConfiguration operations policy contracts tables world outside caller value tail output demand row := by
  obtain ⟨input, requirements, records, summary, scopeTyped, pending, unique, checked, accepted⟩ := value_pending source isValue
  cases pending with
  | spent known annotation scopeKnown rest =>
      obtain ⟨firstRow, tailRow, firstCheck, tailCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have evaluated := RecursiveRequirements.checked_complete firstCheck
      simp only [RecursiveRecomposition.evaluate_spent] at evaluated
      split at evaluated
      · have firstEmpty := Option.some.inj evaluated.symm
        subst firstRow
        obtain ⟨ticket, scopeTyped⟩ := SharedClosingSource.scope_effects scopeKnown
        exact value_source_configuration summary scopeTyped rest unique
          (by simpa only [same, List.nil_append, spendAll, ownedTickets] using tailCheck) accepted
      · cases evaluated

def retiredTickets (events : List Owner) : List Nat :=
  events.filterMap (fun event => match event with | .ticket owner => some owner | _ => none)

/-- Every raw step from a value preserves this recursive source check. The
    ticket demand changes by exactly the emitted ticket-completion events. -/
theorem value_step_preserves
    (source : CheckedConfiguration operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue)
    (step : RawStep ⟨value, scope, stack⟩ next created completed) :
    ∃ remaining, CheckedConfiguration operations policy contracts tables world outside next.scope next.expression next.stack output remaining row ∧
      demand = retiredTickets completed ++ remaining ∧ created = [] ∧
      Trace (available (ownedTickets stack)) (retiredTickets completed) (available (ownedTickets next.stack)) := by
  cases step <;> try cases isValue
  case focus => exact False.elim (ScopedPorts.focus_is_not_value (by assumption) isValue)
  case plug => exact ⟨_, RecursiveContexts.plug_preserves source (by assumption), rfl, rfl, .nil⟩
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
    (source : CheckedConfiguration operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue) :
    stack = .nil ∨ ∃ next completed, RawStep ⟨value, scope, stack⟩ next [] completed := by
  obtain ⟨input, requirements, records, summary, scopeTyped, pending, unique, checked, accepted⟩ := value_pending source isValue
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
    (source : CheckedConfiguration operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue) :
    stack = .nil ∨ ∃ next completed remaining,
      RawStep ⟨value, scope, stack⟩ next [] completed ∧
      CheckedConfiguration operations policy contracts tables world outside next.scope next.expression next.stack output remaining row ∧
      demand = retiredTickets completed ++ remaining ∧
      Trace (available (ownedTickets stack)) (retiredTickets completed) (available (ownedTickets next.stack)) := by
  rcases value_progress source isValue with terminal | ⟨next, completed, step⟩
  · exact Or.inl terminal
  · obtain ⟨remaining, checked, same, created, transition⟩ := value_step_preserves source isValue step
    exact Or.inr ⟨next, completed, remaining, step, checked, same, transition⟩


namespace Examples

def operations : Operations := fun _ _ => none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, true⟩
def tables : CallableProtectionFrames.Tables := fun _ => []
def inner : Owners.Contract := ⟨.unit, .unit, false, [], [], [], some [], [], []⟩
def outer : Owners.Contract := { inner with closeDemand := [19] }
def contracts : Owners.Contracts := fun owner => if owner = 19 then some inner else if owner = 23 then some outer else none

theorem inner_known : contracts 19 = some inner := rfl
theorem outer_known : contracts 23 = some outer := rfl

def callback : Code := .lambda 0 .unit

theorem callback_source : Summary operations [] Environment.empty [] callback (.function .unit .unit [] []) [] :=
  .lambda .unit (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

def action : ActionData := ⟨7, callback, ScopedPorts.typed_value_closed (CoherentSourceTypes.port_typing callback_source .none) trivial,
  .none, .unit, []⟩
theorem unitClosed : ClosedValue Code.unit := CallableProtection.Examples.unit_closed
def fixed : Stack := .push (.closing 41 .none) (.spent 23 .unit .none .nil)
def plan : List CloseEntry := [.invoke action, .retire 19]
def initial : Stack := (closeControl .none plan).append fixed
def running : Stack := .push (.running action .unit unitClosed) (.push (.retiring 19) fixed)
def fixedRequirements : Requirements [] :=
  .sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (.spent 23 .unit .none .nil)))
    (.sequence (.spent 23) (.request [] []))

theorem fixed_source : Segment operations policy contracts tables [] fixed .unit .unit [] fixedRequirements [] :=
  .push (.closing ⟨.none, .none⟩) (.spent outer_known rfl ⟨.none, .none⟩ .nil)

theorem fixed_check : Checked [] [] (available (ownedTickets fixed)) fixedRequirements [] := by
  apply RecursiveRequirements.evaluate_sound
  simp [fixedRequirements, RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
    RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.evaluate_spent, spendAll,
    RecursiveRecomposition.merge_empty_left, fixed, ownedTickets, available]

theorem initial_checked : CheckedConfiguration operations policy contracts tables [] [] .none .unit initial .unit [19] [] := by
  have rows : SourceClosingRows.Rows operations policy contracts [] plan [] :=
    .invoke (action := action) (latent := []) (.stable callback_source) (.retire inner_known .nil)
  exact RecursiveClosing.materialized_configuration (tailRow := []) (closingRow := []) rows .none fixed_source fixed_check
    (by decide) (by
      intro owner member
      have same : owner = 19 := by simpa [plan, OwnerClosingSource.retirements] using member
      subst owner
      simp [fixed, OwnerPhases.ofStack, OwnerPhases.frameEntry, OwnerPhases.names])
    (by simp [OwnerSource.exportAt, residual_empty]) (by decide)

theorem callback_started :
    RawStep ⟨.unit, .none, initial⟩ ⟨.app callback .unit, .none, running⟩ [] [] ∧
    CheckedConfiguration operations policy contracts tables [] [] .none (.app callback .unit) running .unit [19] [] := by
  have step : RawStep ⟨.unit, .none, initial⟩ ⟨.app callback .unit, .none, running⟩ [] [] :=
    .startCleanup action .unit unitClosed .none (.push (.retiring 19) fixed)
  obtain ⟨remaining, checked, same, created, transition⟩ := value_step_preserves initial_checked trivial step
  exact ⟨step, by simpa only [retiredTickets, List.filterMap_nil, List.nil_append] using same ▸ checked⟩

theorem callback_returned :
    RawStep ⟨.app callback .unit, .none, running⟩ ⟨.unit, .none, running⟩ [] [] ∧
    CheckedConfiguration operations policy contracts tables [] [] .none .unit running .unit [19] [] :=
  ⟨.beta 0 .unit .unit .none running unitClosed action.closed,
    RecursiveExpressions.beta_preserves callback_started.2 unitClosed⟩

theorem callback_finished :
    RawStep ⟨.unit, .none, running⟩ ⟨.unit, .none, .push (.retiring 19) fixed⟩ [] [.cleanup 7] ∧
    CheckedConfiguration operations policy contracts tables [] [] .none .unit (.push (.retiring 19) fixed) .unit [19] [] :=
  ⟨.finishCleanup action .unit unitClosed .none (.push (.retiring 19) fixed), finish_cleanup callback_returned.2⟩

theorem owner_retired :
    RawStep ⟨.unit, .none, .push (.retiring 19) fixed⟩ ⟨.unit, .none, fixed⟩ [] [.ticket 19] ∧
    CheckedConfiguration operations policy contracts tables [] [] .none .unit fixed .unit [] [] := by
  obtain ⟨remaining, same, checked, transition⟩ := retire callback_finished.2
  have empty : remaining = [] := (List.cons.inj same).2.symm
  exact ⟨.retire 19 .none fixed, empty ▸ checked⟩

theorem closing_finished :
    RawStep ⟨.unit, .none, fixed⟩ ⟨.unit, .none, .spent 23 .unit .none .nil⟩ [] [.close 41] ∧
    CheckedConfiguration operations policy contracts tables [] [] .none .unit (.spent 23 .unit .none .nil) .unit [] [] :=
  ⟨.finishClose 41 .none .none (.spent 23 .unit .none .nil), finish_close owner_retired.2⟩

theorem returned_to_caller :
    RawStep ⟨.unit, .none, .spent 23 .unit .none .nil⟩ ⟨.unit, .none, .nil⟩ [] [] ∧
    CheckedConfiguration operations policy contracts tables [] [] .none .unit .nil .unit [] [] :=
  ⟨.leaveClause 23 .unit .unit unitClosed .none .none .nil, leave_clause closing_finished.2 trivial⟩

end Examples

end Ash.OneShot.RecursiveCompletion

#print axioms Ash.OneShot.RecursiveCompletion.value_pending
#print axioms Ash.OneShot.RecursiveCompletion.value_configuration
#print axioms Ash.OneShot.RecursiveCompletion.empty_head
#print axioms Ash.OneShot.RecursiveCompletion.running_export
#print axioms Ash.OneShot.RecursiveCompletion.start_cleanup
#print axioms Ash.OneShot.RecursiveCompletion.finish_cleanup
#print axioms Ash.OneShot.RecursiveCompletion.finish_close
#print axioms Ash.OneShot.RecursiveCompletion.retire
#print axioms Ash.OneShot.RecursiveCompletion.leave_handler
#print axioms Ash.OneShot.RecursiveCompletion.leave_cell
#print axioms Ash.OneShot.RecursiveCompletion.leave_clause
#print axioms Ash.OneShot.RecursiveCompletion.value_step_preserves
#print axioms Ash.OneShot.RecursiveCompletion.value_progress
#print axioms Ash.OneShot.RecursiveCompletion.value_preserves
#print axioms Ash.OneShot.RecursiveCompletion.Examples.inner_known
#print axioms Ash.OneShot.RecursiveCompletion.Examples.outer_known
#print axioms Ash.OneShot.RecursiveCompletion.Examples.callback_source
#print axioms Ash.OneShot.RecursiveCompletion.Examples.unitClosed
#print axioms Ash.OneShot.RecursiveCompletion.Examples.fixed_source
#print axioms Ash.OneShot.RecursiveCompletion.Examples.fixed_check
#print axioms Ash.OneShot.RecursiveCompletion.Examples.initial_checked
#print axioms Ash.OneShot.RecursiveCompletion.Examples.callback_started
#print axioms Ash.OneShot.RecursiveCompletion.Examples.callback_returned
#print axioms Ash.OneShot.RecursiveCompletion.Examples.callback_finished
#print axioms Ash.OneShot.RecursiveCompletion.Examples.owner_retired
#print axioms Ash.OneShot.RecursiveCompletion.Examples.closing_finished
#print axioms Ash.OneShot.RecursiveCompletion.Examples.returned_to_caller

#print axioms Ash.OneShot.RecursiveCompletion.value_source_configuration
