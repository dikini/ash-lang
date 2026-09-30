import DeclaredSharedValues

/-! Starting a callback retains its own source-selected request annotation.
The existing cleanup construction supplies the source and requirement steps;
the existing value transition supplies the connected running frame and runtime
facets. No new induction over code, plans, or execution is needed.
-/
namespace Ash.OneShot.DeclaredSourceInterfaces
open ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available)
open ScopedActionInterfaces (Connected ConfigurationConnected)

theorem start_cleanup_state
    (source : DeclaredSourceStates.CheckedState operations policy contracts tables world outside
      scope value (.push (.armed action) tail) output demand row)
    (closed : ClosedValue value)
    (connected : ConfigurationConnected operations.ports contracts.ports actions world
      ⟨.app action.action .unit, .none, .push (.running action value closed) tail⟩ output.port []) :
    State operations policy contracts tables actions world outside .none (.app action.action .unit)
      (.push (.running action value closed) tail) output demand row := by
  have caller : Connected operations.ports contracts.ports actions world
      (.push (.running action value closed) tail) action.requests [] := by
    obtain ⟨input, effects, expression, ports, caller⟩ := connected
    cases caller with
    | push frame rest bound => cases frame with
        | running scope callable saved requests => exact .push (.running scope callable saved requests) rest requests
  obtain ⟨input, requirements, records, disposals, summary, scopeTyped, pending, closing,
    unique, checked, accepted⟩ := DeclaredSourceStates.value_pending source closed.1
  cases closing with
  | push closing => cases pending with
  | push head erasedHead rest => cases head with
      | armed scopeKnown callback annotation =>
          rename_i tailDemand tailRequirements latent
          obtain ⟨callbackRow, tailRow, callbackCheck, tailCheck, same⟩ :=
            RecursiveRequirements.checked_sequence_parts checked
          have exported := RecursiveRequirements.checked_complete callbackCheck
          simp only [RecursiveRequirements.evaluate_prepend, RecursiveContexts.evaluate_request,
            List.append_nil] at exported
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
          have nextPending := Checked.sequence empty tailCheck
          rw [same] at accepted ⊢
          exact .checked (.callable invocation) .none
            (DeclaredSourceFrames.push (.running scopeKnown callback summary annotation) rest)
            (.push closing) unique
            (by simpa only [List.nil_append, ownedTickets] using Checked.sequence currentPrefixed nextPending)
            accepted rfl caller

theorem start_cleanup_progress
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨value, scope, .push (.armed action) tail⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : value.IsValue) :
    ∃ closed : ClosedValue value,
      let state : NamedState := ⟨⟨⟨value, scope, .push (.armed action) tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨.app action.action .unit, .none, .push (.running action value closed) tail⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] []) output demand row bound := by
  have closed := DeclaredSourceStates.value_closed before.current.source isValue
  have raw := RawStep.startCleanup action value closed scope tail
  obtain ⟨remaining, step, current, accounting, noCreated⟩ :=
    DeclaredExecution.value_step_preserves before.current isValue raw
  obtain ⟨actions, usage, history, shared, retained⟩ := before.actions
  have connected := ScopedActionInterfaces.raw_value_preserves_configuration raw closed (interfaces shared)
  have next := start_cleanup_state before.current.source closed connected
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  refine ⟨closed, step, ?_⟩
  apply assemble_entry before.current raw freshOwners current.names.unique step.checks usage history retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

end Ash.OneShot.DeclaredSourceInterfaces

#print axioms Ash.OneShot.DeclaredSourceInterfaces.start_cleanup_state
#print axioms Ash.OneShot.DeclaredSourceInterfaces.start_cleanup_progress
