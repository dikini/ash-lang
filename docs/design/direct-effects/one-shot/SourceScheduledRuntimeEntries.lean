import SourceScheduledRuntimeComputation

/-! Resource, handler and cleanup installation join their actual scheduled source
successors with existing freshness, completion and runtime ownership proofs. -/
namespace Ash.OneShot.SourceScheduledExecution
open ScopedExpressions ScopedExecution
open SourceScheduledSavedPlans (Saved)

theorem resource_annotations
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound)
    (isValue : initializer.IsValue) :
    ∃ forbidden : List Nat, ∃ answerPort : ScopedPorts.Port,
    ∀ identity answer, identity ∉ ScopedTyping.resourceWorld issued → identity ∉ forbidden →
      ScopedPorts.eraseType answer = answerPort →
    ∃ payload, ∃ nextForest : Saved,
      initializer = .integer payload ∧
      let state : NamedState := ⟨⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [.resource identity] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [.resource identity] []) nextForest.forest output demand row bound := by
  obtain ⟨actions, usage, history, shared, retained⟩ := before.actions
  obtain ⟨forbidden, answerPort, admitted⟩ := SourceScheduledResources.resource_annotations shared isValue
  refine ⟨forbidden, answerPort, ?_⟩
  intro identity answer fresh freshRequirements answerSame
  obtain ⟨payload, nextForest, same, raw, next⟩ := admitted identity answer fresh freshRequirements answerSame
  subst initializer
  have results := (CompletionFrames.resource_step before.current.results fresh (answer := answer)).2
  have absent : Owner.resource identity ∉ issued :=
    fun member => fresh (ScopedTyping.mem_resource_world.mpr member)
  have unique : issued.Nodup := before.current.ledger.2
  have freshOwners : (issued ++ [Owner.resource identity]).Nodup := by
    apply List.nodup_append.mpr ⟨unique, by simp, ?_⟩
    intro old present new singleton sameOwner
    simp only [List.mem_singleton] at singleton
    subst new
    subst old
    exact absent present
  have checks : AccessChecks ⟨.resource binder (.integer payload) body, scope, stack⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.resource binder (.integer payload) body, scope, stack⟩
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩).Nodup := by
    simpa [enteredActivations] using before.current.names.unique
  refine ⟨payload, nextForest, rfl, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_entry before.coherent before.current raw freshOwners freshHandlers checks usage history before.annotationHistory retained
  · simpa [ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

theorem resource_progress
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound)
    (isValue : initializer.IsValue) :
    ∃ identity payload answer, ∃ nextForest : Saved,
      initializer = .integer payload ∧
      let state : NamedState := ⟨⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [.resource identity] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [.resource identity] []) nextForest.forest output demand row bound := by
  obtain ⟨forbidden, answerPort, admitted⟩ := resource_annotations before isValue
  obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name (ScopedTyping.resourceWorld issued ++ forbidden)
  obtain ⟨payload, saved, same, step, next⟩ := admitted identity (ScopedPorts.embedPort answerPort)
    (fun member => fresh (List.mem_append_left _ member))
    (fun member => fresh (List.mem_append_right _ member)) (by simp)
  exact ⟨identity, payload, _, saved, same, step, next⟩

theorem handler_annotations
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound) :
    ∃ answerPort : ScopedPorts.Port, ∃ (table : List (Nat × ProtectionContracts.ClauseContract)),
    ∃ clauseFamilies declarationRequirements,
    ∀ activation answerType, activation ∉ activations → ScopedPorts.eraseType answerType = answerPort →
    ∃ handler : HandlerData, ∃ nextForest : Saved,
      handler.activation = activation ∧ handler.answer = answerType ∧
      let state : NamedState := ⟨⟨⟨.handle requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.handler handler) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) annotations
        (ScopedPortJoint.advanceState state after [] []) nextForest.forest output demand row bound := by
  have retainedActivations : stack.erase.activations ⊆ activations := by
    intro activation member
    exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member)
      (before.current.names.handlers activation))
  obtain ⟨actions, usage, history, shared, retained⟩ := before.actions
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, admitted⟩ :=
    SourceScheduledHandlers.handler_annotations shared retainedActivations
  refine ⟨answerPort, table, clauseFamilies, declarationRequirements, ?_⟩
  intro activation answerType freshActivation answerSame
  obtain ⟨handler, nextForest, activationSame, typeSame, raw, next⟩ := admitted activation answerType freshActivation answerSame
  have fresh : handler.activation ∉ activations := activationSame ▸ freshActivation
  have results := DeclaredExecution.handler_step_results raw before.current.results ⟨requested, body, clauses, rfl⟩
  have checks : AccessChecks ⟨.handle requested body clauses, scope, stack⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  have freshHandlers : (activations ++ enteredActivations ⟨.handle requested body clauses, scope, stack⟩
      ⟨body, scope, .push (.handler handler) stack⟩).Nodup := by
    change (activations ++ [handler.activation]).Nodup
    apply List.nodup_append.mpr ⟨before.current.names.unique, by simp, ?_⟩
    intro old present new singleton same
    simp only [List.mem_singleton] at singleton
    subst new
    subst old
    exact fresh present
  refine ⟨handler, nextForest, activationSame, typeSame, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_entry before.coherent before.current raw freshOwners freshHandlers checks usage history before.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil] using results
  · rfl
  · simp

theorem handler_progress
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound) :
    ∃ (handler : HandlerData) (table : List (Nat × ProtectionContracts.ClauseContract)), ∃ clauseFamilies declarationRequirements, ∃ nextForest : Saved,
      handler.activation ∉ activations ∧
      let state : NamedState := ⟨⟨⟨.handle requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.handler handler) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry (RecursiveHandlerTables.register tables handler.activation table)
        (SourceScheduledHandlers.register families handler.activation clauseFamilies)
        (SourceScheduledHandlers.register required handler.activation declarationRequirements) annotations
        (ScopedPortJoint.advanceState state after [] []) nextForest.forest output demand row bound := by
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, admitted⟩ := handler_annotations before
  obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name activations
  obtain ⟨handler, saved, activationSame, _, step, next⟩ := admitted activation (ScopedPorts.embedPort answerPort) fresh (by simp)
  exact ⟨handler, table, clauseFamilies, declarationRequirements, saved, activationSame ▸ fresh, step, next⟩

theorem cleanup_annotations
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup callback body, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound)
    (isValue : callback.IsValue) :
    ∃ answerPort : ScopedPorts.Port, ∃ requests,
    ∀ identity answerType, (issued ++ [Owner.cleanup identity]).Nodup → ScopedPorts.eraseType answerType = answerPort →
    ∃ action : ActionData, ∃ nextForest : Saved,
      action.identity = identity ∧ action.answer = answerType ∧ action.requests = requests ∧
      let state : NamedState := ⟨⟨⟨.cleanup callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [.cleanup action.identity] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [.cleanup action.identity] []) nextForest.forest output demand row bound := by
  obtain ⟨actions, usage, history, shared, retained⟩ := before.actions
  obtain ⟨answerPort, requests, admitted⟩ := SourceScheduledEntries.cleanup_annotations shared isValue
  refine ⟨answerPort, requests, ?_⟩
  intro identity answerType freshOwners answerSame
  obtain ⟨action, nextForest, identitySame, typeSame, requestsSame, raw, next⟩ := admitted identity answerType answerSame
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
  refine ⟨action, nextForest, identitySame, typeSame, requestsSame, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_entry before.coherent before.current raw freshOwners freshHandlers checks usage history before.annotationHistory retained
  · simpa [ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

theorem cleanup_progress
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup callback body, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound)
    (isValue : callback.IsValue) :
    ∃ action : ActionData, ∃ nextForest : Saved,
      let state : NamedState := ⟨⟨⟨.cleanup callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [.cleanup action.identity] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [.cleanup action.identity] []) nextForest.forest output demand row bound := by
  obtain ⟨answerPort, requests, admitted⟩ := cleanup_annotations before isValue
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.cleanup (fun _ => rfl) before.current.ledger.2
  obtain ⟨action, saved, _, _, _, step, next⟩ := admitted identity (ScopedPorts.embedPort answerPort) fresh (by simp)
  exact ⟨action, saved, step, next⟩


end Ash.OneShot.SourceScheduledExecution

#print axioms Ash.OneShot.SourceScheduledExecution.resource_annotations
#print axioms Ash.OneShot.SourceScheduledExecution.resource_progress
#print axioms Ash.OneShot.SourceScheduledExecution.handler_annotations
#print axioms Ash.OneShot.SourceScheduledExecution.handler_progress
#print axioms Ash.OneShot.SourceScheduledExecution.cleanup_annotations
#print axioms Ash.OneShot.SourceScheduledExecution.cleanup_progress
