import DeclaredProgressClassification

/-! A structural current-source witness shares its actual allowed effect list
with the caller interface. Entry proofs choose one source annotation and retain
both judgments for that same frame. Initial closed source supplies this witness;
preservation through all other transitions remains a separate obligation.
-/
namespace Ash.OneShot.DeclaredSourceInterfaces
open ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements Checked evaluate)
open ScopedActionInterfaces (Connected ConfigurationConnected)

/-- The allowed list belongs to the actual current source derivation. No
successor, future capture or preservation theorem occurs in this rule. -/
inductive State (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (actions : Syntax.UsageTickets) (world : List Nat)
    (outside : ProtectionContracts.Context) (scope : Execution.Scope) (code : Code) (stack : Stack)
    (output : Value) (demand : List Nat) (row : ProtectionContracts.Footprint) : Prop where
  | checked
      (current : DeclaredSources.Expression operations policy contracts world allowed scope Environment.empty
        code input currentDemand currentRequirements)
      (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
      (pending : DeclaredSourceFrames.Segment operations policy contracts tables world stack input output
        pendingDemand pendingRequirements resumes)
      (closing : DeclaredSourceClosing.Records operations policy contracts tables world stack disposals)
      (unique : (ownedTickets stack).Nodup)
      (evaluated : Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
        (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row)
      (accepted : ProtectionContracts.checkFootprint outside row = true)
      (accounting : demand = currentDemand ++ pendingDemand)
      (connected : Connected operations.ports contracts.ports actions world stack allowed []) :
      State operations policy contracts tables actions world outside scope code stack output demand row

theorem source
    (state : State operations policy contracts tables actions world outside scope code stack output demand row) :
    DeclaredSourceStates.CheckedState operations policy contracts tables world outside scope code stack output demand row := by
  cases state with
  | checked current scopeTyped pending closing unique evaluated accepted accounting connected =>
      subst demand
      exact .checked (.checked current scopeTyped pending) closing unique evaluated accepted

theorem interfaces
    (state : State operations policy contracts tables actions world outside scope code stack output demand row) :
    ConfigurationConnected operations.ports contracts.ports actions world ⟨code, scope, stack⟩ output.port [] := by
  cases state with
  | checked current scopeTyped pending closing unique evaluated accepted accounting connected =>
      exact ⟨_, _, .checked scopeTyped (SourceTemplates.expression_ports
        (DeclaredSources.expression_erase current) scopeTyped), SourceTemplates.segment_ports pending.erase, connected⟩

theorem initial
    (current : DeclaredSources.Expression operations policy contracts world [] .none Environment.empty
      code output demand requirements)
    (empty : demand = [])
    (evaluated : Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : ProtectionContracts.checkFootprint outside row = true) :
    State operations policy contracts tables actions world outside .none code .nil output demand row := by
  subst demand
  have currentCheck : Checked [] [] (OwnerPhaseTransitions.available []) (requirements.prepend []) row :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.nil_append] using evaluated)
  have pendingCheck : Checked [] [] (OwnerPhaseTransitions.available []) (Requirements.request [] []) [] := .request rfl
  simpa only [List.append_nil] using
    (State.checked (tables := tables) current .none .nil .nil (by decide)
      (Checked.sequence currentCheck pendingCheck) (by simpa only [List.append_nil] using accepted)
      rfl (Connected.nil (List.Subset.refl [])))

/-- The same initial source premises that establish Prepared also establish
the shared witness. There is no new source-admission assumption. -/
theorem initial_prepared
    (current : DeclaredSources.Expression operations policy (fun _ => none) [] [] .none Environment.empty
      code output demand requirements)
    (evaluated : Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : ProtectionContracts.checkFootprint [] row = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code bound)
    (signature : operations.ports = DeclarationResults.signature declarations)
    (support : decide (Syntax.resourceDependencies code.dependencies = []) = true) :
    demand = [] ∧
    DeclaredClosingInvariant.Prepared operations declarations policy (fun _ => none) tables
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ output [] row bound ∧
    State operations policy (fun _ => none) tables (fun _ => none) [] [] .none code .nil output demand row := by
  obtain ⟨empty, prepared⟩ := DeclaredClosingInvariant.initial_state current evaluated accepted result signature support
  exact ⟨empty, prepared, initial current empty evaluated accepted⟩

theorem focus
    (state : State operations policy contracts tables actions world outside scope whole stack output demand row)
    (position : Focus whole child context) :
    ∃ plain : PlainData,
      plain.context = context ∧ plain.scope = scope ∧
      RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] ∧
      State operations policy contracts tables actions world outside scope child
        (.push (.plain plain) stack) output demand row := by
  cases state with
  | checked current scopeTyped pending closing unique checked accepted accounting connected =>
      rename_i allowed currentInput currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
      obtain ⟨input, childDemand, restDemand, currentReq, restReq, childSource, sourceContext, sameDemand, evaluation⟩ :=
        DeclaredSourceContexts.focus_decompose current position
      obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ :=
        RecursiveContexts.prepare_plain (DeclaredSources.expression_erase current) position scopeTyped input
      have frame : DeclaredSourceFrames.Frame operations policy contracts tables world
          (.plain plain) input _ restDemand restReq :=
        .plain (by simpa only [contextSame, scopeSame] using sourceContext)
          (by simpa only [scopeSame] using scopeTyped) inputAnnotation outputAnnotation
      have effectFrame : ScopedPorts.EffectFrame operations.ports contracts.ports world
          (.plain plain) allowed allowed := by
        apply ScopedPorts.EffectFrame.plain (by simpa only [scopeSame] using scopeTyped)
        have contextTyped := SourceTemplates.context_ports (DeclaredSourceFrames.context_erase sourceContext) scopeTyped
        change ScopedPorts.ContextTyped operations.ports world ScopedPorts.TypeEnv.empty ticket allowed context
          input.port currentInput.port at contextTyped
        simpa only [contextSame, inputAnnotation, outputAnnotation] using contextTyped
      refine ⟨plain, contextSame, scopeSame, ?_, ?_⟩
      · simpa only [scopeSame] using RawStep.focus plain (by simpa only [contextSame] using position) stack
      · refine .checked childSource scopeTyped (DeclaredSourceFrames.push frame pending) (.push closing)
          unique ?_ accepted ?_ (.push effectFrame connected (List.Subset.refl _))
        · apply RecursiveRequirements.evaluate_sound
          have oldEvaluation := RecursiveRequirements.checked_complete checked
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation] at oldEvaluation
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            RecursiveContexts.plain_context, RecursiveContexts.plain_owners, List.cons_append,
            RecursiveContexts.evaluate_plain]
          simpa only [sameDemand, PhaseRechecking.spendAll_append, ProtectionResiduals.merge_assoc] using oldEvaluation
        · simpa only [sameDemand, List.append_assoc] using accounting

theorem cleanup
    (state : State operations policy contracts tables actions world outside scope (.cleanup callback body) stack output demand row)
    (isValue : callback.IsValue) (identity : Nat) :
    ∃ action : ActionData,
      action.identity = identity ∧
      RawStep ⟨.cleanup callback body, scope, stack⟩ ⟨body, scope, .push (.armed action) stack⟩ [.cleanup identity] [] ∧
      State operations policy contracts tables actions world outside scope body
        (.push (.armed action) stack) output demand row := by
  cases state with
  | checked current scopeTyped pending closing unique checked accepted accounting connected =>
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
      refine .checked bodySource scopeTyped (DeclaredSourceFrames.push frame pending) (.push closing)
        unique ?_ accepted ?_ (.push effectFrame connected (List.Subset.refl _))
      · apply RecursiveRequirements.evaluate_sound
        have original := RecursiveRequirements.checked_complete checked
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
          List.append_nil] at original
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
          RecursiveContexts.evaluate_request, RecursiveEntries.armed_context, List.append_nil,
          RecursiveContexts.evaluate_plain, ownedTickets, OwnerPhaseTransitions.spendAll]
        simpa only [ProtectionResiduals.merge_assoc] using original
      · simpa only [List.nil_append] using accounting

/-- The runtime facets and independent actions retain the shared current-source
witness on the same concrete machine. This is not yet preserved by every rule. -/
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

theorem Run.prepared (run : Run operations declarations policy registry tables state output demand row bound) :
    DeclaredClosingInvariant.Prepared operations declarations policy registry tables state output demand row bound := by
  obtain ⟨actions, usage, history, shared, retained⟩ := run.actions
  exact ⟨run.current, actions, usage, history, interfaces shared, retained⟩

theorem initial_run
    (current : DeclaredSources.Expression operations policy (fun _ => none) [] [] .none Environment.empty
      code output demand requirements)
    (evaluated : Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : ProtectionContracts.checkFootprint [] row = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code bound)
    (signature : operations.ports = DeclarationResults.signature declarations)
    (support : decide (Syntax.resourceDependencies code.dependencies = []) = true) :
    demand = [] ∧ Run operations declarations policy (fun _ => none) tables
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ output [] row bound := by
  obtain ⟨empty, prepared⟩ := DeclaredClosingInvariant.initial_state current evaluated accepted result signature support
  obtain ⟨actions, usage, history, connected, retained⟩ := prepared.actions
  exact ⟨empty, prepared.current, actions, usage, history, empty ▸ initial current empty evaluated accepted, retained⟩

/-- Assemble finite successor evidence for an already constructed entry.
Source selection and access checks are supplied by the entry theorems below. -/
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
    (shared : State operations policy registry.contracts nextTables (ScopedActionUsage.advance actions after created)
      (ScopedTyping.resourceWorld (before.execution.issued ++ created)) [] after.scope after.expression after.stack output nextDemand nextRow)
    (results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results
      (ScopedTyping.resourceWorld (before.execution.issued ++ created)) after bound)
    (update : registry.runtime.joint.usage = advanceUsageTickets policy registry.runtime.joint.usage after created)
    (noTickets : ∀ owner, Owner.ticket owner ∉ created) :
    Run operations declarations policy registry nextTables
        (ScopedPortJoint.advanceState before after created discharged) output nextDemand nextRow bound := by
  have usageChecks := usage_checks_from_allocation_and_access history freshOwners checks
  have extension := ScopedActionUsage.advance_extends (after := after) usageChecks.allocation
  have unique : (ownedTickets after.stack).Nodup := by
    cases shared with
    | checked _ _ _ _ unique _ _ _ _ => exact unique
  have larger : ScopedTyping.resourceWorld before.execution.issued ⊆
      ScopedTyping.resourceWorld (before.execution.issued ++ created) := by
    rw [ScopedTyping.resource_world_append]
    exact List.subset_append_left _ _
  exact ⟨DeclaredExecution.assemble_event current raw freshOwners freshHandlers checks (source shared) results update,
    _, ScopedActionUsage.raw_step_preserves raw usageChecks usage,
    ScopedActionUsage.raw_step_preserves_history raw history, shared,
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
  obtain ⟨actions, usage, history, shared, retained⟩ := before.actions
  obtain ⟨plain, contextSame, scopeSame, raw, next⟩ := focus shared position
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

end Ash.OneShot.DeclaredSourceInterfaces

#print axioms Ash.OneShot.DeclaredSourceInterfaces.source
#print axioms Ash.OneShot.DeclaredSourceInterfaces.interfaces
#print axioms Ash.OneShot.DeclaredSourceInterfaces.initial
#print axioms Ash.OneShot.DeclaredSourceInterfaces.initial_prepared
#print axioms Ash.OneShot.DeclaredSourceInterfaces.focus
#print axioms Ash.OneShot.DeclaredSourceInterfaces.cleanup
#print axioms Ash.OneShot.DeclaredSourceInterfaces.Run.prepared
#print axioms Ash.OneShot.DeclaredSourceInterfaces.initial_run
#print axioms Ash.OneShot.DeclaredSourceInterfaces.focus_progress
#print axioms Ash.OneShot.DeclaredSourceInterfaces.cleanup_progress
