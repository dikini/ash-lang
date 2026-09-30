import RecursiveCells

/-!
Actual interpretation selection for a checked value-operand request. This joins
the existing residual checker and physical stack-resolution proofs; it does
not assume a source cut or a builtin update supplied by the caller.
-/

namespace Ash.OneShot.RecursiveRequestProgress
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open SourceTemplates (Expression Segment)
open RecursiveRecords (CheckedState)
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (available spendAll)

theorem request_evaluation
    (source : Expression operations policy contracts world allowed scope environment
      (.perform (Instantiation.freezeEffect requested) operation operand) result demand requirements)
    (isValue : operand.IsValue) :
    evaluate store receiving before requirements =
      OwnerSource.exportAt receiving before [⟨requested, operation, false⟩] :=
  RecursiveDispatch.request_evaluation source isValue

theorem admitted_selection (admitted : Admitted context request) :
    ∃ target mode, ProtectionContexts.select request.effect (erase context) request.held = some (target, mode) := by
  induction admitted with
  | barrier next ih => exact ih
  | builtin_hit same =>
      simp only [erase, ProtectionContexts.select, same, if_true]
      exact ⟨_, _, rfl⟩
  | builtin_miss different next ih | handler_miss different next ih =>
      simpa only [erase, ProtectionContexts.select, if_neg different] using ih
  | handler_hit same known supported row body ih =>
      simp only [erase, ProtectionContexts.select, same, if_true]
      exact ⟨_, _, rfl⟩

theorem current_request_admitted
    (source : CheckedState operations policy contracts tables world [] scope
      (.perform (Instantiation.freezeEffect requested) operation operand) stack output demand row)
    (isValue : operand.IsValue) :
    Admitted (CallableProtectionFrames.contextOf tables stack) ⟨requested, operation, false⟩ := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
        have evaluated := RecursiveRequirements.checked_complete currentCheck
        simp only [RecursiveRequirements.evaluate_prepend, List.append_nil, request_evaluation current isValue,
          OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] at evaluated
        have allowed := checked_footprint_subset accepted (List.sublist_append_left currentRow pendingRow).subset
        have checkedRequest : checkFootprint (CallableProtectionFrames.contextOf tables stack ++ [])
            [⟨requested, operation, false⟩] = true :=
          residual_admitted_iff.mpr ⟨currentRow, evaluated, allowed⟩
        exact check_footprint_iff.mp (by simpa only [List.append_nil] using checkedRequest) _ List.mem_cons_self

theorem current_request_resolves
    (source : CheckedState operations policy contracts tables world [] scope
      (.perform (Instantiation.freezeEffect requested) operation operand) stack output demand row)
    (isValue : operand.IsValue) :
    ∃ target, stack.erase.resolve requested = some target := by
  obtain ⟨target, mode, selected⟩ := admitted_selection (current_request_admitted source isValue)
  rw [CallableProtectionFrames.context_realizes] at selected
  have resolved := ProtectionContexts.select_target (requested := requested) (incoming := false) stack.erase
  rw [selected] at resolved
  exact ⟨target, resolved.symm⟩

/-- The mode proof needs the admitted request row. Its value payload may
    retain a full handler-bearing body that the old stable summary cannot type. -/
theorem request_footprint
    (source : CheckedState operations policy contracts tables world [] scope
      (.perform (Instantiation.freezeEffect requested) operation operand) stack output demand row)
    (isValue : operand.IsValue) :
    checkRequest (CallableProtectionFrames.contextOf tables stack) ⟨requested, operation, false⟩ = true :=
  check_request_complete (current_request_admitted source isValue)

theorem protected_disposal_denied
    (source : CheckedState operations policy contracts (CallableProtectionFrames.policyTables policy rows) world [] scope
      (.perform (Instantiation.freezeEffect requested) operation operand) stack output demand row)
    (isValue : operand.IsValue)
    (cut : HandlerCut requested stack capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (held : capture.erase.protected ≠ []) : (policy binder).dispose = false := by
  obtain ⟨contract, known, permitted⟩ := CallableProtectionFrames.cut_contract cut (request_footprint source isValue)
  have same := (CallableProtectionFrames.clause_lookup (policy := policy) (rows := rows handler) clause).symm.trans known
  cases Option.some.inj same
  apply (mode_check_iff.mp permitted)
  simp [ProtectionContexts.protected_mode_iff.mpr held]

theorem state_ports
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row) :
    ScopedPorts.ConfigurationTyped operations.ports contracts.ports.types world ⟨code, scope, stack⟩ output.port := by
  cases source with
  | checked source closing unique checked accepted => exact SourceTemplates.configuration_ports source

/-- Canonical forms and physical resolution derive the builtin operands and
    update. The previously proved read/write theorems supply preservation. -/
theorem builtin_progress
    (signature : operations.ports = ScopedPorts.withCellSignatures users)
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect (.cell identity)) operation operand) stack output demand row)
    (isValue : operand.IsValue)
    (resolved : stack.erase.resolve (.cell identity) = some (.builtin identity)) :
    ∃ next nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) operation operand, scope, stack⟩ next [] [] ∧
      CheckedState operations policy contracts tables world outside next.scope next.expression next.stack output demand nextRow ∧
      nextRow.Sublist row ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets stack)) [] (available (ownedTickets next.stack)) := by
  obtain ⟨old, update⟩ := ScopedTyping.cell_selection_of_resolution stack resolved
  obtain ⟨answer, expression, retained⟩ := state_ports source
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, known, allowed, operandTyped⟩ := ScopedPorts.typed_perform_inversion expression
      rw [signature] at known
      cases operation with
      | zero =>
          simp only [ScopedPorts.withCellSignatures, Option.some.injEq, Prod.mk.injEq] at known
          obtain ⟨rfl, rfl⟩ := known
          obtain rfl := ScopedPorts.typed_reference_value operandTyped isValue
          obtain ⟨after, selected⟩ := update old
          obtain ⟨nextRow, step, checked, included, trace⟩ := RecursiveCells.read_preserves (by rw [signature]; rfl) source selected
          exact ⟨_, nextRow, step, checked, included, trace⟩
      | succ operation => cases operation with
        | zero =>
            simp only [ScopedPorts.withCellSignatures, Option.some.injEq, Prod.mk.injEq] at known
            obtain ⟨rfl, rfl⟩ := known
            obtain ⟨reference, number, rfl, referenceValue, numberValue, referenceTyped, numberTyped⟩ :=
              ScopedPorts.typed_product_value operandTyped isValue
            obtain rfl := ScopedPorts.typed_reference_value referenceTyped referenceValue
            obtain ⟨new, rfl⟩ := ScopedPorts.typed_integer_value numberTyped numberValue
            obtain ⟨after, selected⟩ := update new
            obtain ⟨nextRow, step, checked, included, trace⟩ := RecursiveCells.write_preserves (by rw [signature]; rfl) source selected
            exact ⟨_, nextRow, step, checked, included, trace⟩
        | succ operation => cases known

/-- A closed checked request either takes a preserved builtin step or selects
    the actual nearest source-handler cut. Handler-clause admission is separate. -/
theorem request_selection
    (signature : operations.ports = ScopedPorts.withCellSignatures users)
    (source : CheckedState operations policy contracts tables world [] scope
      (.perform (Instantiation.freezeEffect requested) operation operand) stack output demand row)
    (isValue : operand.IsValue) :
    (∃ next nextRow,
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩ next [] [] ∧
      CheckedState operations policy contracts tables world [] next.scope next.expression next.stack output demand nextRow ∧
      nextRow.Sublist row) ∨
    (∃ capture tail handler, HandlerCut requested stack capture tail handler) := by
  obtain ⟨target, resolved⟩ := current_request_resolves source isValue
  cases target with
  | builtin identity =>
      obtain rfl := ScopedTyping.builtin_resolution_instance stack resolved
      obtain ⟨next, nextRow, step, checked, included, trace⟩ := builtin_progress signature source isValue resolved
      exact Or.inl ⟨next, nextRow, step, checked, included⟩
  | source activation =>
      obtain ⟨capture, tail, handler, cut, same⟩ := ScopedTyping.handler_selection_of_resolution stack resolved
      exact Or.inr ⟨capture, tail, handler, cut⟩

/-- Reuse typed capture to obtain an actual raw request step at a fresh
    historical slot. Only the builtin branch above already preserves the full
    recursive check; capture preservation still requires structural clauses. -/
theorem request_progress
    (signature : operations.ports = ScopedPorts.withCellSignatures users)
    (source : CheckedState operations policy contracts tables world [] scope
      (.perform (Instantiation.freezeEffect requested) operation operand) stack output demand row)
    (isValue : operand.IsValue) (fresh : contracts.ports.types owner = none) :
    ∃ next created,
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩ next created [] := by
  rcases request_selection signature source isValue with ⟨next, nextRow, step, checked, included⟩ | ⟨capture, tail, handler, cut⟩
  · exact ⟨next, [], step⟩
  · obtain ⟨parameter, binder, body, input, step, extension, typed⟩ :=
      ScopedPorts.capture_constructs_typed_configuration cut (state_ports source) isValue fresh
    exact ⟨_, [.ticket owner], step⟩

theorem unhandled_request_rejected
    (unhandled : stack.erase.resolve requested = none) (isValue : operand.IsValue) :
    ¬ CheckedState operations policy contracts tables world [] scope
      (.perform (Instantiation.freezeEffect requested) operation operand) stack output demand row := by
  intro source
  obtain ⟨target, resolved⟩ := current_request_resolves source isValue
  rw [unhandled] at resolved
  cases resolved

/-- The established registry-history bridge and fresh-owner theorem supply
    allocation, and the existing ledger theorem checks the actual event. -/
theorem request_run_progress {registry : Owners.Registry}
    (signature : operations.ports = ScopedPorts.withCellSignatures users)
    (source : CheckedState operations policy registry.contracts tables world [] scope
      (.perform (Instantiation.freezeEffect requested) operation operand) stack output demand row)
    (isValue : operand.IsValue)
    (history : ScopedPortJoint.RegistryHistory registry.runtime.joint issued)
    (ledger : Ledger (⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩,
      issued, completed⟩ : RunState).erase) :
    ∃ after,
      RunStep ⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩ after ∧
      Ledger after.erase := by
  let before : RunState := ⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩
  rcases request_selection signature source isValue with ⟨next, nextRow, raw, checked, included⟩ | ⟨capture, tail, handler, cut⟩
  · have step := RunStep.event before next [] [] raw (by simpa only [before, RunState.erase, List.append_nil] using ledger.2)
    exact ⟨_, step, run_step_preserves_ledger step ledger⟩
  · obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) ledger.2
    have absent := ScopedPortJoint.registry_fresh history fresh
    have freshTypes : registry.contracts.ports.types owner = none := by
      rw [Owners.registry_ports]
      simp only [ScopedPorts.EffectTickets.types, ScopedPortJoint.Registry.effects, absent, Option.map_none]
    obtain ⟨parameter, binder, body, input, raw, extension, typed⟩ :=
      ScopedPorts.capture_constructs_typed_configuration cut (state_ports source) isValue freshTypes
    have step := RunStep.event before _ [.ticket owner] [] raw fresh
    exact ⟨_, step, run_step_preserves_ledger step ledger⟩

/-- Resource allocation reuses fresh-owner existence and ledger preservation.
    The checked entry theorem supplies the actual successor source and stores. -/
theorem resource_run_progress
    (source : CheckedState operations policy contracts tables (ScopedTyping.resourceWorld issued) outside scope
      (.resource binder initializer body) stack output demand row)
    (isValue : initializer.IsValue)
    (ledger : Ledger (⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩ : RunState).erase) :
    ∃ after : RunState,
      RunStep ⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩ after ∧
      CheckedState operations policy contracts tables (ScopedTyping.resourceWorld after.issued) outside
        after.configuration.scope after.configuration.expression after.configuration.stack output demand row ∧
      Ledger after.erase := by
  obtain ⟨identity, payload, answer, unused, same, raw, checked, trace⟩ :=
    RecursiveEntries.resource_preserves source isValue
  have absent : Owner.resource identity ∉ issued := fun member => unused (ScopedTyping.mem_resource_world.mpr member)
  have fresh : (issued ++ [Owner.resource identity]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨ledger.2, by simp, ?_⟩
    intro a member b single collision
    have equal := List.mem_singleton.mp single
    exact absent ((collision.trans equal) ▸ member)
  have step := RunStep.event ⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩
    _ [.resource identity] [] raw fresh
  refine ⟨_, step, ?_, run_step_preserves_ledger step ledger⟩
  simpa [ScopedTyping.resourceWorld, List.filterMap_append] using checked

namespace Examples
open RecursiveCells.Examples (writableOperations writeCode writeBefore write_initial)
open SharedClosingSource.Examples (policy contracts tables)

theorem writable_signature : writableOperations.ports = ScopedPorts.withCellSignatures (fun _ _ => none) := by
  funext effect operation
  cases effect <;> cases operation with
  | zero => rfl
  | succ operation => cases operation <;> rfl

/-- Both the target and the payload update follow from the existing checked
    write expression; no CellUpdate or resolve premise is supplied. -/
theorem write_progress_without_selection :
    ∃ next nextRow,
      RawStep ⟨writeCode, .none, writeBefore⟩ next [] [] ∧
      CheckedState writableOperations policy contracts tables [4] [] next.scope next.expression next.stack .unit [] nextRow ∧
      nextRow.Sublist [] := by
  obtain ⟨target, resolved⟩ := current_request_resolves write_initial (by trivial)
  have same : target = .builtin 4 := (Option.some.inj resolved).symm
  subst target
  obtain ⟨next, nextRow, step, checked, included, trace⟩ := builtin_progress writable_signature write_initial (by trivial) resolved
  exact ⟨next, nextRow, step, checked, included⟩

/-- The earlier capture example now derives its physical handler selection
    from the check, including the intervening live continuation boundary. -/
theorem handler_progress_without_cut :
    ∃ next,
      RawStep ⟨.perform (Instantiation.freezeEffect RecursiveDisposalCapture.Examples.effect) 0 .unit,
        .ticket 0 19, RecursiveDisposalCapture.Examples.capture⟩ next [.ticket 23] [] := by
  have source := RecursiveDisposalCapture.Examples.request_checked
  obtain ⟨target, resolved⟩ := current_request_resolves source (by trivial)
  cases target with
  | builtin identity =>
      have impossible := ScopedTyping.builtin_resolution_instance _ resolved
      cases impossible
  | source activation =>
      obtain ⟨capture, tail, handler, cut, active⟩ := ScopedTyping.handler_selection_of_resolution _ resolved
      obtain ⟨parameter, binder, body, input, step, extension, typed⟩ :=
        ScopedPorts.capture_constructs_typed_configuration cut (state_ports source) (by trivial) (owner := 23) (by rfl)
      exact ⟨_, step⟩

end Examples

namespace ResourceExamples
open RecursiveCells.Examples (writableOperations)

def initializer : Code := .bind 3 (.integer 17) (.variable 3)
def body : Code := .perform (.cell (.bound 0)) 0 (.resourceRef (.bound 0))
def program : Code := .resource 0 initializer body

theorem source_summary : Summary writableOperations [] Environment.empty [] program .integer [] := by
  apply Summary.resource (initialRow := []) (residual := [])
    (bodyRow := fun identity => [⟨.cell identity, 0, false⟩])
  · exact .bind .integer (.variable rfl (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
  · intro identity fresh
    exact .perform rfl List.mem_cons_self (.reference List.mem_cons_self)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  · simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]
  · exact List.Subset.refl _
  · exact List.Subset.refl _
  · intro identity fresh
    simp [CallableProtection.outsideCell]

theorem initial_checked : CheckedState writableOperations policy contracts tables [] [] .none program .nil .integer [] [] :=
  RecursiveExecution.check_state (.checked (.stable source_summary) .none .nil) .nil
    (by decide) (by
      apply RecursiveRequirements.checked_complete
      exact Checked.sequence (Checked.request (row := []) rfl) (Checked.request (row := []) rfl)) (by decide)

/-- An actual source resource with a nonvalue initializer reaches its integer
    result through checked focus, substitution, entry, read, and closure. -/
theorem evaluate_resource :
    ∃ identity, RawTrace ⟨program, .none, .nil⟩ ⟨.integer 17, .none, .nil⟩ [.resource identity] [.resource identity] ∧
    CheckedState writableOperations policy contracts tables [identity] [] .none (.integer 17) .nil .integer [] [] := by
  have closed : ClosedValue (.integer 17) := ⟨trivial, rfl, by intro dependency member; cases member⟩
  obtain ⟨plain, focus, focused, contextSame, scopeSame, trace⟩ :=
    RecursiveExecution.focus_preserves (initial_checked (policy := policy) (contracts := contracts) (tables := tables))
      (Focus.resource (by intro impossible; cases impossible))
  have bound := RecursiveExecution.bind_preserves focused closed
  simp only [Code.subst, ite_true] at bound
  have plugged := RecursiveExecution.plug_preserves bound closed
  simp only [contextSame, scopeSame, ScopedExecution.Context.plug] at plugged
  obtain ⟨identity, payload, answer, unused, same, entered, opened, ownerTrace⟩ :=
    RecursiveEntries.resource_preserves plugged (by trivial)
  have payloadSame : payload = 17 := (Code.integer.inj same).symm
  subst payload
  obtain ⟨row, read, returned, included, readTrace⟩ := RecursiveCells.read_preserves (by rfl) opened .hit
  have empty : row = [] := List.sublist_nil.mp included
  subst row
  refine ⟨identity, ?_, RecursiveExecution.leave_cell returned (by trivial)⟩
  have binding : RawStep ⟨initializer, .none, .push (.plain plain) .nil⟩
      ⟨.integer 17, .none, .push (.plain plain) .nil⟩ [] [] :=
    .bind 3 (.integer 17) (.variable 3) .none _ closed (by simp [ClosedExcept, Code.dependencies])
  have plugging : RawStep ⟨.integer 17, .none, .push (.plain plain) .nil⟩
      ⟨.resource 0 (.integer 17) body, .none, .nil⟩ [] [] := by
    simpa only [contextSame, scopeSame, ScopedExecution.Context.plug] using RawStep.plug plain (.integer 17) closed .none .nil
  exact .next focus (.next binding (.next plugging (.next entered (.next read
    (.next (.leaveCell identity 17 answer .none .none (.integer 17) closed .nil) (.refl _))))))

def initialRun : RunState := ⟨⟨program, .none, .nil⟩, [], []⟩
def finalRun (identity : Nat) : RunState := ⟨⟨.integer 17, .none, .nil⟩, [.resource identity], [.resource identity]⟩

theorem resource_execution : ∃ identity, RunSteps initialRun (finalRun identity) ∧ (finalRun identity).completed.Nodup := by
  obtain ⟨identity, raw, checked⟩ :=
    evaluate_resource (policy := fun _ => ⟨true, false⟩) (contracts := fun _ => none) (tables := fun _ => [])
  have execution : RunSteps initialRun (finalRun identity) := raw_trace_enacts raw
    (issued := []) (completed := []) (by simp)
  have ledger : Ledger initialRun.erase := ⟨.refl _, by decide⟩
  exact ⟨identity, execution, ledger_no_double_completion (run_steps_preserve_ledger execution ledger)⟩

end ResourceExamples

end Ash.OneShot.RecursiveRequestProgress

#print axioms Ash.OneShot.RecursiveRequestProgress.request_evaluation
#print axioms Ash.OneShot.RecursiveRequestProgress.admitted_selection
#print axioms Ash.OneShot.RecursiveRequestProgress.current_request_admitted
#print axioms Ash.OneShot.RecursiveRequestProgress.current_request_resolves
#print axioms Ash.OneShot.RecursiveRequestProgress.request_footprint
#print axioms Ash.OneShot.RecursiveRequestProgress.protected_disposal_denied
#print axioms Ash.OneShot.RecursiveRequestProgress.state_ports
#print axioms Ash.OneShot.RecursiveRequestProgress.builtin_progress
#print axioms Ash.OneShot.RecursiveRequestProgress.request_selection
#print axioms Ash.OneShot.RecursiveRequestProgress.request_progress
#print axioms Ash.OneShot.RecursiveRequestProgress.unhandled_request_rejected
#print axioms Ash.OneShot.RecursiveRequestProgress.request_run_progress
#print axioms Ash.OneShot.RecursiveRequestProgress.resource_run_progress
#print axioms Ash.OneShot.RecursiveRequestProgress.ResourceExamples.source_summary
#print axioms Ash.OneShot.RecursiveRequestProgress.ResourceExamples.initial_checked
#print axioms Ash.OneShot.RecursiveRequestProgress.ResourceExamples.evaluate_resource
#print axioms Ash.OneShot.RecursiveRequestProgress.ResourceExamples.resource_execution
#print axioms Ash.OneShot.RecursiveRequestProgress.Examples.writable_signature
#print axioms Ash.OneShot.RecursiveRequestProgress.Examples.write_progress_without_selection
#print axioms Ash.OneShot.RecursiveRequestProgress.Examples.handler_progress_without_cut
