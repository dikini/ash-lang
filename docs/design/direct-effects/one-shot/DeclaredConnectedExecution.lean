import DeclaredConnectedSources

/-! Runtime joins for the structural source/interpretation segment. Focus and
plugging retain the actual stored annotation in both directions. Other runtime
transitions must still preserve this stronger segment judgment.
-/
namespace Ash.OneShot.DeclaredConnectedSources
open ScopedExpressions ScopedExecution CoherentSourceTypes

structure Run (operations : Operations) (declarations : Instantiation.DeclarationRegistry)
    (policy : Syntax.TicketPolicy) (registry : Owners.Registry) (tables : CallableProtectionFrames.Tables)
    (state : NamedState) (output : Value) (demand : List Nat)
    (row : ProtectionContracts.Footprint) (bound : CallableContracts.Contract) : Prop where
  current : DeclaredExecution.Valid operations declarations policy registry tables [] [] state output demand row bound
  actions : ∃ tickets,
    ConfigurationUsage policy tickets state.execution.configuration ∧
    UsageRegistryHistory tickets state.execution.issued ∧
    State operations policy registry.contracts tables tickets (ScopedTyping.resourceWorld state.execution.issued)
      [] state.execution.configuration.scope state.execution.configuration.expression
      state.execution.configuration.stack output demand row ∧
    DeclaredClosingInvariant.Retained operations.ports (ScopedTyping.resourceWorld state.execution.issued)
      registry tickets state.execution.configuration.stack

theorem Run.shared
    (run : Run operations declarations policy registry tables state output demand row bound) :
    DeclaredSourceInterfaces.Run operations declarations policy registry tables state output demand row bound := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  exact ⟨run.current, actions, usage, history, source.shared, retained⟩

theorem initial_run
    (current : DeclaredSources.Expression operations policy (fun _ => none) [] [] .none Environment.empty
      code output demand requirements)
    (evaluated : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : ProtectionContracts.checkFootprint [] row = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code bound)
    (signature : operations.ports = DeclarationResults.signature declarations)
    (support : decide (Syntax.resourceDependencies code.dependencies = []) = true) :
    demand = [] ∧ Run operations declarations policy (fun _ => none) tables
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ output [] row bound := by
  obtain ⟨empty, existing⟩ := DeclaredSourceInterfaces.initial_run current evaluated accepted result signature support
  obtain ⟨actions, usage, history, source, retained⟩ := existing.actions
  exact ⟨empty, existing.current, actions, usage, history, empty ▸ initial current empty evaluated accepted, retained⟩

/-- Reuse runtime and action preservation, retaining the supplied finite
structural successor rather than reconstructing independent annotations. -/
theorem assemble_entry
    (current : DeclaredExecution.Valid operations declarations policy registry tables [] [] before output demand row bound)
    (raw : RawStep before.execution.configuration after created discharged)
    (freshOwners : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup)
    (checks : AccessChecks before.execution.configuration [])
    (usage : ConfigurationUsage policy actions before.execution.configuration)
    (history : UsageRegistryHistory actions before.execution.issued)
    (retained : DeclaredClosingInvariant.Retained operations.ports (ScopedTyping.resourceWorld before.execution.issued)
      registry actions before.execution.configuration.stack)
    (source : State operations policy registry.contracts nextTables (ScopedActionUsage.advance actions after created)
      (ScopedTyping.resourceWorld (before.execution.issued ++ created)) [] after.scope after.expression after.stack output nextDemand nextRow)
    (results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results
      (ScopedTyping.resourceWorld (before.execution.issued ++ created)) after bound)
    (update : registry.runtime.joint.usage = advanceUsageTickets policy registry.runtime.joint.usage after created)
    (noTickets : ∀ owner, Owner.ticket owner ∉ created) :
    Run operations declarations policy registry nextTables
      (ScopedPortJoint.advanceState before after created discharged) output nextDemand nextRow bound := by
  have existing := DeclaredSourceInterfaces.assemble_entry current raw freshOwners freshHandlers checks usage history
    retained source.shared results update noTickets
  have usageChecks := usage_checks_from_allocation_and_access history freshOwners checks
  have extension := ScopedActionUsage.advance_extends (after := after) usageChecks.allocation
  have unique : (ownedTickets after.stack).Nodup := by
    cases source with
    | checked _ _ _ _ unique _ _ _ => exact unique
  have larger : ScopedTyping.resourceWorld before.execution.issued ⊆
      ScopedTyping.resourceWorld (before.execution.issued ++ created) := by
    rw [ScopedTyping.resource_world_append]
    exact List.subset_append_left _ _
  exact ⟨existing.current, _, ScopedActionUsage.raw_step_preserves raw usageChecks usage,
    ScopedActionUsage.raw_step_preserves_history raw history, source,
    DeclaredClosingInvariant.raw_step_preserves_retained raw retained (fun _ _ known => known)
      extension larger (.none noTickets) unique⟩

theorem focus_progress
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (position : Focus code child context) :
    ∃ plain : PlainData,
      plain.context = context ∧ plain.scope = scope ∧
      let state : NamedState := ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨child, scope, .push (.plain plain) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] []) output demand row bound := by
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  obtain ⟨plain, contextSame, scopeSame, raw, next⟩ := focus source position
  have results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results
      (ScopedTyping.resourceWorld issued) ⟨child, scope, .push (.plain plain) stack⟩ bound := by
    have positioned : Focus code child plain.context := contextSame.symm ▸ position
    simpa only [scopeSame] using (CompletionFrames.focus_step positioned
      (by simpa only [scopeSame] using before.current.results)).2
  have checks := ScopedPortJoint.focus_access_checks (scope := scope) (tail := stack) (ambient := []) position
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  have freshHandlers : (activations ++ enteredActivations ⟨code, scope, stack⟩
      ⟨child, scope, .push (.plain plain) stack⟩).Nodup := by
    simpa [focus_enters_no_activation position] using before.current.names.unique
  refine ⟨plain, contextSame, scopeSame, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_entry before.current raw freshOwners freshHandlers checks usage history retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil] using results
  · rfl
  · simp

theorem plug_progress
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨value, scope, .push (.plain plain) tail⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : value.IsValue) :
    let state : NamedState := ⟨⟨⟨value, scope, .push (.plain plain) tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨plain.context.plug value, plain.scope, tail⟩
    NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
    Run operations declarations policy registry tables
      (ScopedPortJoint.advanceState state after [] []) output demand row bound := by
  have closed := DeclaredSourceStates.value_closed before.current.source isValue
  have raw := RawStep.plug plain value closed scope tail
  obtain ⟨remaining, step, current, accounting, noCreated⟩ :=
    DeclaredExecution.value_step_preserves before.current isValue raw
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  have next := plug source closed
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  refine ⟨step, ?_⟩
  apply assemble_entry before.current raw freshOwners current.names.unique step.checks usage history retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

end Ash.OneShot.DeclaredConnectedSources

#print axioms Ash.OneShot.DeclaredConnectedSources.Run.shared
#print axioms Ash.OneShot.DeclaredConnectedSources.initial_run
#print axioms Ash.OneShot.DeclaredConnectedSources.focus_progress
#print axioms Ash.OneShot.DeclaredConnectedSources.plug_progress
