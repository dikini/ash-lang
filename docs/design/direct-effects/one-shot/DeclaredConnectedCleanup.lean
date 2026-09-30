import DeclaredConnectedValues

/-! Cleanup installation stores the actual source/effect frame in the structural
segment. The existing entry proof still supplies the callback annotation, fresh
owner, checked requirements and completion result for the same transition.
-/
namespace Ash.OneShot.DeclaredConnectedSources
open ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements Checked evaluate)

theorem cleanup
    (state : State operations policy contracts tables actions world outside scope (.cleanup callback body) stack output demand row)
    (isValue : callback.IsValue) (identity : Nat) :
    ∃ action : ActionData,
      action.identity = identity ∧
      RawStep ⟨.cleanup callback body, scope, stack⟩ ⟨body, scope, .push (.armed action) stack⟩ [.cleanup identity] [] ∧
      State operations policy contracts tables actions world outside scope body
        (.push (.armed action) stack) output demand row := by
  cases state with
  | checked current scopeTyped pending closing unique checked accepted accounting =>
      rename_i allowed currentInput currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
      obtain ⟨requests, latent, bodyRequirements, callbackSource, bodySource, admitted, evaluation⟩ :=
        DeclaredSourceEntries.cleanup_parts current isValue
      have closed := ScopedPorts.typed_value_closed ((DeclaredSourceValues.erase callbackSource).ports .none) isValue
      let action : ActionData := ⟨identity, callback, closed, scope, ScopedPorts.embedPort currentInput.port, requests⟩
      have frame : DeclaredSourceFrames.Frame operations policy contracts tables world (.armed action) currentInput currentInput []
          (.request [] (ProtectionContracts.qualify true latent)) :=
        .armed ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩ callbackSource (by simp [action])
      have effectFrame : ScopedPorts.EffectFrame operations.ports contracts.ports world (.armed action) allowed allowed :=
        .armed ⟨_, scopeTyped⟩ ((DeclaredSourceValues.erase callbackSource).ports .none) admitted
      refine ⟨action, rfl, .enterCleanup action body stack, ?_⟩
      refine .checked bodySource scopeTyped (.push (.retained .armed frame effectFrame) pending (List.Subset.refl _)) (.push closing)
        unique ?_ accepted ?_
      · apply RecursiveRequirements.evaluate_sound
        have original := RecursiveRequirements.checked_complete checked
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
          List.append_nil] at original
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
          RecursiveContexts.evaluate_request, RecursiveEntries.armed_context, List.append_nil,
          RecursiveContexts.evaluate_plain, ownedTickets, OwnerPhaseTransitions.spendAll]
        simpa only [ProtectionResiduals.merge_assoc] using original
      · simpa only [List.nil_append] using accounting

theorem cleanup_progress
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.cleanup callback body, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : callback.IsValue) :
    ∃ action : ActionData,
      let state : NamedState := ⟨⟨⟨.cleanup callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [.cleanup action.identity] []) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [.cleanup action.identity] []) output demand row bound := by
  obtain ⟨actions, usage, history, shared, retained⟩ := before.actions
  obtain ⟨identity, freshOwners⟩ := ScopedPortProgress.fresh_owner_exists Owner.cleanup (fun _ => rfl) before.current.ledger.2
  obtain ⟨action, identitySame, raw, next⟩ := cleanup shared isValue identity
  rw [← identitySame] at raw freshOwners
  have results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results
      (ScopedTyping.resourceWorld issued) ⟨body, scope, .push (.armed action) stack⟩ bound := by
    exact DeclaredExecution.cleanup_step_results raw before.current.results
  have checks : AccessChecks ⟨.cleanup callback body, scope, stack⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations ⟨.cleanup callback body, scope, stack⟩
      ⟨body, scope, .push (.armed action) stack⟩).Nodup := by
    simpa [enteredActivations] using before.current.names.unique
  refine ⟨action, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_entry before.current raw freshOwners freshHandlers checks usage history retained
  · simpa [ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

end Ash.OneShot.DeclaredConnectedSources

#print axioms Ash.OneShot.DeclaredConnectedSources.cleanup
#print axioms Ash.OneShot.DeclaredConnectedSources.cleanup_progress
