import DeclaredCompletionAdmission
import DeclaredSourceCells
import RecursiveRequestProgress
import SavedCaptureIdentity

/-!
Execution with hereditary source/effect checking and independent runtime
ownership, support, usage and result contracts. One coherent registry supplies
both source and runtime projections. This invariant uses the checked source
requirements as its effect evidence; it does not assert equivalence to the
older coarse EffectStackTyped annotation. Capture below derives its access
checks and allocation from the current invariant. Disposing capture and
whole-source execution coverage remain separate obligations. The counterexample
in DeclaredDisposalAdmissionGap shows that this invariant alone does not imply
progress for access-checked execution; retained closing compatibility and
declared-request support need additional structural evidence.
-/
namespace Ash.OneShot.DeclaredExecution
open Instantiation ScopedExpressions ScopedExecution CoherentSourceTypes
open ScopedTyping (resourceWorld resource_world_append)
open DeclaredSourceStates (CheckedState)
open CompletionFrames (ConfigurationReturns)
open ScopedPortJoint (advanceState)

structure Valid (operations : Operations) (declarations : DeclarationRegistry)
    (policy : Syntax.TicketPolicy) (registry : Owners.Registry)
    (tables : CallableProtectionFrames.Tables) (outside : ProtectionContracts.Context)
    (ambient : List Nat) (state : NamedState) (output : Value)
    (demand : List Nat) (row : ProtectionContracts.Footprint) (bound : CallableContracts.Contract) : Prop where
  signature : operations.ports = DeclarationResults.signature declarations
  source : CheckedState operations policy registry.contracts tables (resourceWorld state.execution.issued)
    outside state.execution.configuration.scope state.execution.configuration.expression
    state.execution.configuration.stack output demand row
  results : ConfigurationReturns declarations registry.runtime.results (resourceWorld state.execution.issued)
    state.execution.configuration bound
  ledger : Ledger state.execution.erase
  names : NameHistory state.execution state.activations
  support : AccessValid state.execution.configuration ambient
  usage : ConfigurationUsage policy registry.runtime.joint.usage state.execution.configuration
  registry : ScopedPortJoint.RegistryHistory registry.runtime.joint state.execution.issued
  closed : state.execution.configuration.ResourceClosed

/-- Initial structural premises establish this invariant without assuming any
future state, capture certificate or successful execution. -/
theorem initial_state
    (source : DeclaredSources.Expression operations policy (fun _ => none) [] outgoing .none Environment.empty
      code output demand requirements)
    (checked : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : ProtectionContracts.checkFootprint outside row = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code bound)
    (signature : operations.ports = DeclarationResults.signature declarations)
    (support : decide (Syntax.resourceDependencies code.dependencies = []) = true) :
    demand = [] ∧ Valid operations declarations policy (fun _ => none) tables outside []
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ output [] row bound := by
  obtain ⟨empty, source, runtime⟩ :=
    DeclaredCompletionAdmission.initial_state (tables := tables) source checked accepted result signature support
  exact ⟨empty, signature, source, runtime.results, runtime.joint.ledger, runtime.joint.names,
    runtime.joint.support, runtime.joint.usage, runtime.joint.registry, runtime.joint.closed⟩

/-- Reuse the generic runtime preservation proofs after a local source/result
proof has constructed the actual successor. This helper is not a source rule. -/
theorem assemble_event
    (valid : Valid operations declarations policy registry tables outside ambient before output demand row bound)
    (raw : RawStep before.execution.configuration after created discharged)
    (freshOwners : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup)
    (checks : AccessChecks before.execution.configuration ambient)
    (source : CheckedState operations policy nextRegistry.contracts nextTables
      (resourceWorld (before.execution.issued ++ created)) outside after.scope after.expression after.stack
      output nextDemand nextRow)
    (results : ConfigurationReturns declarations nextRegistry.runtime.results
      (resourceWorld (before.execution.issued ++ created)) after bound)
    (update : nextRegistry.runtime.joint.usage = advanceUsageTickets policy registry.runtime.joint.usage after created) :
    Valid operations declarations policy nextRegistry nextTables outside ambient
      (advanceState before after created discharged) output nextDemand nextRow bound := by
  have step : NamedAccessStep ambient before (advanceState before after created discharged) :=
    ⟨.event before after created discharged raw freshOwners freshHandlers, checks⟩
  obtain ⟨ledger, names, support⟩ := named_access_step_preserves step valid.ledger valid.names valid.support
  have history := ScopedPortJoint.usage_history_iff.mpr valid.registry
  have usage := raw_step_preserves_configuration_usage raw
    (usage_checks_from_allocation_and_access history freshOwners checks) valid.usage
  have nextHistory := raw_step_preserves_usage_registry_history (policy := policy) raw history
  rw [← update] at usage nextHistory
  exact ⟨valid.signature, source, results, ledger, names, support, usage,
    ScopedPortJoint.usage_history_iff.mp nextHistory, raw_step_preserves_resource_closure raw valid.closed⟩

/-- The existing finite payload-bound proof applies directly to hereditary
source ports and retained completion contracts; no effect-stack erasure is used. -/
theorem request_access_checks
    (valid : Valid operations declarations policy registry tables outside ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ output demand row bound) :
    AccessChecks ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ ambient := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    have impossible := congrArg Configuration.expression same
    dsimp only at impossible
    rw [← impossible] at closed
    cases closed.1
  · intro requested' operation' operand' scope' whole' cap tail handler same cut closed
    have typed := DeclaredReturnAdmission.ports valid.source
    rw [valid.signature] at typed
    have returns := valid.results
    have support := valid.support
    rw [same] at typed returns support
    exact CompletionJoint.payload_access_from_ports typed returns support.control cut closed.1
  · intro binder ticket scope caller input answer front cap tail plan same resolved built
    cases congrArg Configuration.expression same

/-- Every non-disposing selected request with a value operand can allocate a
fresh owner and preserve the complete invariant. Access, history and usage
successors are derived, not additional admission premises. -/
theorem resume_only_capture
    (valid : Valid operations declarations policy registry tables outside ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ output demand row bound)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue)
    (noDispose : (ProtectionContracts.lookup operation (tables handler)).map ProtectionContracts.ClauseContract.dispose = some false) :
    ∃ (owner : Nat) (record : Owners.Record) (after : Configuration)
      (nextDemand : List Nat) (nextRow : ProtectionContracts.Footprint),
      record.annotation.closeRow = none ∧
      NamedAccessStep ambient
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
        (advanceState ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
          issued, completed⟩, activations⟩ after [.ticket owner] []) ∧
      Valid operations declarations policy (registry.insert owner record) tables outside ambient
        (advanceState ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
          issued, completed⟩, activations⟩ after [.ticket owner] []) output nextDemand nextRow bound ∧
      registry.contracts.Extends (registry.insert owner record).contracts ∧
      CallableJoint.RegistryExtends registry.runtime (registry.insert owner record).runtime ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) valid.ledger.2
  have empty : registry owner = none := by
    have absent := ScopedPortJoint.registry_fresh valid.registry fresh
    cases found : registry owner <;>
      simp_all [Owners.Registry.runtime, CallableJoint.Registry.joint]
  obtain ⟨record, after, binder, nextDemand, nextRow, noClose, actualScope, permissions,
    raw, source, results, sourceExtension, runtimeExtension, demandPerm, rowBound, owners⟩ :=
    DeclaredCompletionAdmission.coherent_resume_only_capture valid.source valid.results
      valid.signature cut isValue empty noDispose
  have freshHandlers : (activations ++ enteredActivations
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  have checks := request_access_checks valid
  refine ⟨owner, record, after, nextDemand, nextRow, noClose,
    ⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩, ?_, sourceExtension, runtimeExtension,
    demandPerm, rowBound, owners⟩
  apply assemble_event valid raw fresh freshHandlers checks
  · simpa [resource_world_append, resourceWorld] using source
  · simpa [resource_world_append, resourceWorld] using results
  · rw [Owners.registry_insert_runtime, CallableJoint.joint_insert, ScopedPortJoint.usage_insert]
    simp only [advanceUsageTickets, actualScope, permissions]

/-- Resumption recomposes the saved continuation and the waiting caller,
consumes exactly one demand, and preserves all independent runtime facets. -/
theorem resume_preserves {front capture tail : Stack}
    (valid : Valid operations declarations policy registry tables outside ambient
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ output demand row bound)
    (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) :
    ∃ remaining,
      let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
      let before : NamedState := ⟨⟨⟨.resume binder value, scope,
        front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
      NamedAccessStep ambient before (advanceState before after [] [.ticket owner]) ∧
      Valid operations declarations policy registry tables outside ambient
        (advanceState before after [] [.ticket owner]) output remaining row bound ∧
      demand = owner :: remaining := by
  obtain ⟨remaining, raw, source, results, demandSame, trace⟩ :=
    DeclaredCompletionAdmission.resume_preserves valid.source valid.results resolved isValue
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      ⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩
      ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  have checks := CompletionJoint.resume_access_checks (ambient := ambient) (front := front)
    (owner := owner) (input := inputType) (answer := answerType) (capture := capture) (tail := tail)
    (caller := caller) (scope := scope) (binder := binder) (value := value)
  refine ⟨remaining, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_, demandSame⟩
  apply assemble_event valid raw freshOwners freshHandlers checks
  · simpa only [List.append_nil] using source
  · simpa only [List.append_nil] using results
  · rfl

/-- All returned-value transitions reuse the existing structural result proofs,
including cleanup execution, resource release and scheduled owner retirement. -/
theorem value_step_results
    (returns : ConfigurationReturns declarations registry world ⟨value, scope, stack⟩ bound)
    (isValue : value.IsValue) (step : RawStep ⟨value, scope, stack⟩ after created discharged) :
    ConfigurationReturns declarations registry world after bound := by
  cases step <;> try cases isValue
  case focus => exact False.elim (ScopedPorts.focus_is_not_value (by assumption) isValue)
  case plug => exact (CompletionFrames.plug_step returns (by assumption)).2
  case leaveHandler => exact (CompletionFrames.handler_return_step returns (by assumption)).2
  case leaveCell => exact (CompletionFrames.cell_return_step returns (by assumption)).2.2
  case startCleanup => exact (CompletionFrames.cleanup_start_step returns (by assumption)).2
  case finishCleanup => exact (CompletionFrames.cleanup_finish_step returns).2
  case leaveClause => exact (CompletionFrames.clause_return_step returns (by assumption)).2
  case finishClose => exact (CompletionFrames.closing_finish_step returns).2
  case retire => exact (CompletionFrames.retiring_step returns).2

/-- A returned value's structural result contract excludes the resource being
released. The other local access checks are impossible for value syntax. -/
theorem value_access_checks
    (returns : ConfigurationReturns declarations registry world ⟨value, scope, stack⟩ bound)
    (isValue : value.IsValue) : AccessChecks ⟨value, scope, stack⟩ ambient := by
  constructor
  · intro identity payload answer savedScope scope' value' tail same closed
    rw [same] at returns
    exact (CompletionFrames.cell_return_step returns closed).2.1
  · intro requested operation operand scope' whole cap tail handler same cut closed
    have expressionEq := congrArg Configuration.expression same
    dsimp only at expressionEq
    rw [expressionEq] at isValue
    cases isValue
  · intro binder ticket scope' caller input answer front cap tail plan same resolved built
    have expressionEq := congrArg Configuration.expression same
    dsimp only at expressionEq
    rw [expressionEq] at isValue
    cases isValue

/-- Every actual returned-value step preserves the combined invariant. The
source proof accounts for precisely the tickets retired by that step. -/
theorem value_step_preserves
    (valid : Valid operations declarations policy registry tables outside ambient before output demand row bound)
    (isValue : before.execution.configuration.expression.IsValue)
    (raw : RawStep before.execution.configuration after created discharged) :
    ∃ remaining,
      NamedAccessStep ambient before (advanceState before after created discharged) ∧
      Valid operations declarations policy registry tables outside ambient
        (advanceState before after created discharged) output remaining row bound ∧
      demand = RecursiveCompletion.retiredTickets discharged ++ remaining ∧ created = [] := by
  obtain ⟨remaining, source, demandSame, empty, trace⟩ :=
    DeclaredSourceStates.value_step_preserves valid.source isValue raw
  subst created
  have results := value_step_results valid.results isValue raw
  have checks := value_access_checks (ambient := ambient) valid.results isValue
  have freshOwners : (before.execution.issued ++ []).Nodup := by
    simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup := by
    simpa [value_enters_no_activation (DeclaredSourceStates.value_closed valid.source isValue)] using valid.names.unique
  refine ⟨remaining, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_, demandSame, rfl⟩
  apply assemble_event valid raw freshOwners freshHandlers checks
  · simpa only [List.append_nil] using source
  · simpa only [List.append_nil] using results
  · rfl

/-- A current value either has no pending stack or takes a step preserving all
source and runtime facets. This includes cleanup start and completion. -/
theorem value_progress
    (valid : Valid operations declarations policy registry tables outside ambient before output demand row bound)
    (isValue : before.execution.configuration.expression.IsValue) :
    before.execution.configuration.stack = .nil ∨
    ∃ after discharged remaining,
      NamedAccessStep ambient before (advanceState before after [] discharged) ∧
      Valid operations declarations policy registry tables outside ambient
        (advanceState before after [] discharged) output remaining row bound ∧
      demand = RecursiveCompletion.retiredTickets discharged ++ remaining := by
  rcases DeclaredSourceStates.value_progress valid.source isValue with terminal | ⟨after, discharged, raw⟩
  · exact Or.inl terminal
  · obtain ⟨remaining, step, next, demandSame, empty⟩ := value_step_preserves valid isValue raw
    exact Or.inr ⟨after, discharged, remaining, step, next, demandSame⟩

/-- Reuse substitution for bind/application and select the already checked
branch. No independent result analysis or substitution proof is introduced. -/
theorem ready_step_results
    (returns : ConfigurationReturns declarations registry world ⟨code, scope, stack⟩ bound)
    (ready : RecursiveExpressions.Ready code)
    (step : RawStep ⟨code, scope, stack⟩ after created discharged) :
    ConfigurationReturns declarations registry world after bound := by
  cases step with
  | focus plain focus tail => exact False.elim (RecursiveExpressions.ready_not_focus ready focus)
  | plug plain value closed scope tail => exact False.elim (RecursiveExpressions.ready_not_value ready closed.1)
  | leaveHandler handler value closed scope tail => exact False.elim (RecursiveExpressions.ready_not_value ready closed.1)
  | leaveCell identity payload answer savedScope scope value closed tail => exact False.elim (RecursiveExpressions.ready_not_value ready closed.1)
  | startCleanup action saved closed scope tail => exact False.elim (RecursiveExpressions.ready_not_value ready closed.1)
  | leaveClause owner answer value closed scope caller tail => exact False.elim (RecursiveExpressions.ready_not_value ready closed.1)
  | bind parameter value body scope tail closed environment => exact (CompletionFrames.bind_step returns closed environment).2
  | beta parameter body value scope tail closed closure => exact (CompletionFrames.beta_step returns closed closure).2
  | ifTrue =>
      obtain ⟨environment, ticket, input, scopeChecked, current, pending⟩ := returns
      cases current with
      | leaf isValue => cases isValue
      | branch condition yes no => exact ⟨environment, ticket, input, scopeChecked, yes, pending⟩
  | ifFalse =>
      obtain ⟨environment, ticket, input, scopeChecked, current, pending⟩ := returns
      cases current with
      | leaf isValue => cases isValue
      | branch condition yes no => exact ⟨environment, ticket, input, scopeChecked, no, pending⟩
  | enterHandler | enterCell | enterCleanup | finishCleanup | capture | resume | discard | finishClose | retire | readCell | writeCell => cases ready

/-- Ready bind, application and branch expressions make progress while retaining
source demand up to permutation and reducing the checked effect row. -/
theorem ready_progress
    (valid : Valid operations declarations policy registry tables outside ambient before output demand row bound)
    (ready : RecursiveExpressions.Ready before.execution.configuration.expression) :
    ∃ after remaining nextRow,
      NamedAccessStep ambient before (advanceState before after [] []) ∧
      Valid operations declarations policy registry tables outside ambient
        (advanceState before after [] []) output remaining nextRow bound ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨after, remaining, nextRow, raw, source, sameDemand, included, sameStack, trace⟩ :=
    DeclaredSourceStates.ready_preserves valid.source ready
  have results := ready_step_results valid.results ready raw
  have syntaxChecks (code : Code) (checked : RecursiveExpressions.Ready code) :
      AccessChecks ⟨code, before.execution.configuration.scope, before.execution.configuration.stack⟩ ambient ∧
      enteredActivations ⟨code, before.execution.configuration.scope, before.execution.configuration.stack⟩ after = [] := by
    constructor
    · apply ScopedPortJoint.ordinary_access_checks (RecursiveExpressions.ready_not_value checked)
      · cases checked <;> intro requested operation operand impossible <;> cases impossible
      · cases checked <;> intro binder impossible <;> cases impossible
    · cases checked <;> rfl
  obtain ⟨checks, noEntry⟩ := syntaxChecks _ ready
  have freshOwners : (before.execution.issued ++ []).Nodup := by
    simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup := by
    simpa only [noEntry, List.append_nil] using valid.names.unique
  refine ⟨after, remaining, nextRow, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
    ?_, sameDemand, included⟩
  apply assemble_event valid raw freshOwners freshHandlers checks
  · simpa only [List.append_nil] using source
  · simpa only [List.append_nil] using results
  · rfl

/-- Source-directed resource allocation supplies an identity outside the issued
resource world, so the lifetime history also remains fresh. -/
theorem resource_entry
    (valid : Valid operations declarations policy registry tables outside ambient
      ⟨⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : initializer.IsValue) :
    ∃ identity payload answer,
      initializer = .integer payload ∧
      let before : NamedState := ⟨⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep ambient before (advanceState before after [.resource identity] []) ∧
      Valid operations declarations policy registry tables outside ambient
        (advanceState before after [.resource identity] []) output demand row bound := by
  obtain ⟨identity, payload, answer, fresh, same, raw, source, results⟩ :=
    DeclaredCompletionAdmission.resource_entry valid.source valid.results isValue
  have absent : Owner.resource identity ∉ issued := fun member => fresh (ScopedTyping.mem_resource_world.mpr member)
  have unique : issued.Nodup := valid.ledger.2
  have freshOwners : (issued ++ [Owner.resource identity]).Nodup := by
    apply List.nodup_append.mpr ⟨unique, by simp, ?_⟩
    intro old present new singleton sameOwner
    simp only [List.mem_singleton] at singleton
    subst new
    subst old
    exact absent present
  have checks : AccessChecks ⟨.resource binder initializer body, scope, stack⟩ ambient :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.resource binder initializer body, scope, stack⟩
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  refine ⟨identity, payload, answer, same, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_event valid raw freshOwners freshHandlers checks
  · simpa [resource_world_append, resourceWorld] using source
  · simpa [resource_world_append, resourceWorld] using results
  · rfl

/-- Focus uses the source-chosen frame for both judgments. Lexical frame
annotations, result contracts and runtime support describe the same transition. -/
theorem focus_progress
    (valid : Valid operations declarations policy registry tables outside ambient
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (focus : Focus code child position) :
    ∃ plain : PlainData,
      plain.context = position ∧ plain.scope = scope ∧
      let before : NamedState := ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨child, scope, .push (.plain plain) stack⟩
      NamedAccessStep ambient before (advanceState before after [] []) ∧
      Valid operations declarations policy registry tables outside ambient
        (advanceState before after [] []) output demand row bound := by
  obtain ⟨plain, raw, source, contextSame, scopeSame, trace⟩ :=
    DeclaredSourceStates.focus_preserves valid.source focus
  have results : ConfigurationReturns declarations registry.runtime.results (resourceWorld issued)
      ⟨child, scope, .push (.plain plain) stack⟩ bound := by
    have positioned : Focus code child plain.context := contextSame.symm ▸ focus
    simpa only [scopeSame] using (CompletionFrames.focus_step positioned
      (by simpa only [scopeSame] using valid.results)).2
  have checks := ScopedPortJoint.focus_access_checks (scope := scope) (tail := stack) (ambient := ambient) focus
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (activations ++ enteredActivations ⟨code, scope, stack⟩
      ⟨child, scope, .push (.plain plain) stack⟩).Nodup := by
    simpa [focus_enters_no_activation focus] using valid.names.unique
  refine ⟨plain, contextSame, scopeSame, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_event valid raw freshOwners freshHandlers checks
  · simpa only [List.append_nil] using source
  · simpa only [List.append_nil] using results
  · rfl

theorem cleanup_step_results
    (raw : RawStep before after [.cleanup identity] [])
    (returns : ConfigurationReturns declarations registry world before bound) :
    ConfigurationReturns declarations registry world after bound := by
  cases raw
  exact (CompletionFrames.cleanup_entry_step returns).2

theorem handler_step_results
    (raw : RawStep before after created discharged)
    (returns : ConfigurationReturns declarations registry world before bound)
    (form : ∃ requested body clauses, before.expression = .handle requested body clauses) :
    ConfigurationReturns declarations registry world after bound := by
  obtain ⟨requested, body, clauses, same⟩ := form
  cases raw <;> try cases same
  all_goals try
    have impossible : ClosedValue (.handle requested body clauses) := by assumption
    cases impossible.1
  case focus plain tail focused => cases focused
  case enterHandler => exact (CompletionFrames.handler_entry_step returns).2

/-- Installing a checked cleanup callback allocates a fresh cleanup owner and
retains its full source and result contracts on the same armed frame. -/
theorem cleanup_entry
    (valid : Valid operations declarations policy registry tables outside ambient
      ⟨⟨⟨.cleanup callback body, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : callback.IsValue) :
    ∃ action : ActionData,
      let before : NamedState := ⟨⟨⟨.cleanup callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep ambient before (advanceState before after [.cleanup action.identity] []) ∧
      Valid operations declarations policy registry tables outside ambient
        (advanceState before after [.cleanup action.identity] []) output demand row bound := by
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.cleanup (fun _ => rfl) valid.ledger.2
  obtain ⟨action, identitySame, raw, source, trace⟩ :=
    DeclaredSourceEntries.cleanup_preserves valid.source isValue identity
  rw [← identitySame] at raw fresh
  have results : ConfigurationReturns declarations registry.runtime.results (resourceWorld issued)
      ⟨body, scope, .push (.armed action) stack⟩ bound := by
    exact cleanup_step_results raw valid.results
  have checks : AccessChecks ⟨.cleanup callback body, scope, stack⟩ ambient :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations ⟨.cleanup callback body, scope, stack⟩
      ⟨body, scope, .push (.armed action) stack⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  refine ⟨action, ⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩, ?_⟩
  apply assemble_event valid raw fresh freshHandlers checks
  · simpa [resource_world_append, resourceWorld] using source
  · simpa [resource_world_append, resourceWorld] using results
  · rfl

/-- Handler installation registers its checked declarations at the actual fresh
activation. Runtime histories and the structural source use that same frame. -/
theorem handler_entry
    (valid : Valid operations declarations policy registry tables outside ambient
      ⟨⟨⟨.handle requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound) :
    ∃ (handler : HandlerData) (table : List (Nat × ProtectionContracts.ClauseContract)),
      handler.activation ∉ activations ∧
      let before : NamedState := ⟨⟨⟨.handle requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.handler handler) stack⟩
      NamedAccessStep ambient before (advanceState before after [] []) ∧
      Valid operations declarations policy registry (RecursiveHandlerTables.register tables handler.activation table)
        outside ambient (advanceState before after [] []) output demand row bound := by
  have retained : stack.erase.activations ⊆ activations := by
    intro activation member
    exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member) (valid.names.handlers activation))
  obtain ⟨handler, table, fresh, installed, raw, source, owners⟩ :=
    DeclaredSourceEntries.handler_preserves valid.source retained
  have results : ConfigurationReturns declarations registry.runtime.results (resourceWorld issued)
      ⟨body, scope, .push (.handler handler) stack⟩ bound := by
    exact handler_step_results raw valid.results ⟨requested, body, clauses, rfl⟩
  have checks : AccessChecks ⟨.handle requested body clauses, scope, stack⟩ ambient :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (activations ++ enteredActivations ⟨.handle requested body clauses, scope, stack⟩
      ⟨body, scope, .push (.handler handler) stack⟩).Nodup := by
    change (activations ++ [handler.activation]).Nodup
    apply List.nodup_append.mpr ⟨valid.names.unique, by simp, ?_⟩
    intro old present new singleton same
    simp only [List.mem_singleton] at singleton
    subst new
    subst old
    exact fresh present
  refine ⟨handler, table, fresh, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_event valid raw freshOwners freshHandlers checks
  · simpa only [List.append_nil] using source
  · simpa only [List.append_nil] using results
  · rfl

/-- The existing callable cell-transport argument extends to completion frames.
Only the selected cell payload changes; saved captures are not searched. -/
theorem cell_update_preserves_results
    (update : CellUpdate identity old new before after)
    (checked : CompletionFrames.StackReturns declarations registry world before input output) :
    CompletionFrames.StackReturns declarations registry world after input output := by
  induction update generalizing input output with
  | hit => cases checked with
      | cell scope absent rest => exact .cell scope absent rest
  | push miss next ih => cases checked with
      | plain scope context rest => exact .plain scope context (ih rest)
      | cell scope absent rest => exact .cell scope absent (ih rest)
      | handler scope clauses rest => exact .handler scope clauses (ih rest)
      | armed scope callback rest => exact .armed scope callback (ih rest)
      | running scope callback saved rest => exact .running scope callback saved (ih rest)
      | closing scope rest => exact .closing scope (ih rest)
      | retiring rest => exact .retiring (ih rest)
  | live next ih => cases checked with
      | live known scope saved rest => exact .live known scope saved (ih rest)
  | spent next ih => cases checked with
      | spent known scope rest => exact .spent known scope (ih rest)

private theorem request_storage_contract
    (checked : CompletionContracts.Derives declarations environment world ticket
      (.perform effect operation operand) contract) :
    ∃ resources, contract = .storage resources := by
  cases checked with
  | leaf isValue => cases isValue
  | perform => exact ⟨_, rfl⟩

/-- Existing nonallocating-request classification leaves only builtin read and
write. Their scalar replies satisfy the retained storage contract. -/
theorem builtin_step_results
    (raw : RawStep before after [] [])
    (same : before.expression = .perform effect operation operand) (isValue : operand.IsValue)
    (returns : ConfigurationReturns declarations registry world before bound) :
    ConfigurationReturns declarations registry world after bound := by
  have ordinary := ScopedPortProgress.nonallocating_request_is_ordinary raw same isValue
  cases ordinary with
  | bind | beta | ifTrue | ifFalse => cases same
  | read selected =>
      obtain ⟨environment, ticket, contract, scope, code, stack⟩ := returns
      obtain ⟨resources, rfl⟩ := request_storage_contract code
      exact ⟨environment, ticket, .storage resources, scope, .leaf trivial rfl .nil,
        cell_update_preserves_results selected stack⟩
  | write selected =>
      obtain ⟨environment, ticket, contract, scope, code, stack⟩ := returns
      obtain ⟨resources, rfl⟩ := request_storage_contract code
      exact ⟨environment, ticket, .storage resources, scope, .leaf trivial rfl .nil,
        cell_update_preserves_results selected stack⟩

/-- The existing hereditary read/write proofs retain source evidence at the
actual update selected by the machine, including under completion frames. -/
theorem builtin_step_source
    (signature : operations.ports = ScopedPorts.withCellSignatures users)
    (source : CheckedState operations policy contracts tables world outside
      before.scope before.expression before.stack output demand row)
    (raw : RawStep before after [] [])
    (same : before.expression = .perform effect operation operand) (isValue : operand.IsValue) :
    ∃ nextRow, CheckedState operations policy contracts tables world outside
      after.scope after.expression after.stack output demand nextRow ∧ nextRow.Sublist row := by
  have ordinary := ScopedPortProgress.nonallocating_request_is_ordinary raw same isValue
  cases ordinary with
  | bind | beta | ifTrue | ifFalse => cases same
  | read selected =>
      obtain ⟨nextRow, step, next, included, trace⟩ :=
        DeclaredSourceCells.read_preserves (by rw [signature]; rfl) source selected
      exact ⟨nextRow, next, included⟩
  | write selected =>
      obtain ⟨nextRow, step, next, included, trace⟩ :=
        DeclaredSourceCells.write_preserves (by rw [signature]; rfl) source selected
      exact ⟨nextRow, next, included⟩

/-- Builtin requests preserve all independent source and runtime facets. The
operation signature comes from the same declarations as result checking. -/
theorem builtin_step_preserves
    (valid : Valid operations declarations policy registry tables outside ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : operand.IsValue)
    (raw : RawStep ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ after [] []) :
    ∃ nextRow,
      let before : NamedState := ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep ambient before (advanceState before after [] []) ∧
      Valid operations declarations policy registry tables outside ambient
        (advanceState before after [] []) output demand nextRow bound ∧ nextRow.Sublist row := by
  obtain ⟨nextRow, source, included⟩ := builtin_step_source valid.signature valid.source raw rfl isValue
  have results := builtin_step_results raw rfl isValue valid.results
  have checks := request_access_checks valid
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ after).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  refine ⟨nextRow, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_, included⟩
  apply assemble_event valid raw freshOwners freshHandlers checks
  · simpa only [List.append_nil] using source
  · simpa only [List.append_nil] using results
  · rfl

/-- Closed requests derive physical selection from structural requirements.
The builtin branch already has full preservation; the other branch identifies
the actual nearest source-handler cut for capability-specific admission. -/
theorem request_selection
    (valid : Valid operations declarations policy registry tables [] ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : operand.IsValue) :
    (∃ after nextRow,
      let before : NamedState := ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep ambient before (advanceState before after [] []) ∧
      Valid operations declarations policy registry tables [] ambient
        (advanceState before after [] []) output demand nextRow bound ∧ nextRow.Sublist row) ∨
    (∃ capture tail handler, HandlerCut requested stack capture tail handler) := by
  rcases RecursiveRequestProgress.request_selection valid.signature
      (DeclaredSourceStates.checked_state_erase valid.source) isValue with
    ⟨after, nextRow, raw, source, included⟩ | selected
  · obtain ⟨nextRow, step, next, included⟩ := builtin_step_preserves valid isValue raw
    exact Or.inl ⟨after, nextRow, step, next, included⟩
  · exact Or.inr selected

/-- Current support supplies all resources retained outside a saved capture.
The active caller prefix can add resources but is not needed to supply them. -/
theorem saved_resources_supported {front capture tail : Stack}
    (support : Supported (front.append (.live owner input answer capture caller tail)).erase []) :
    Admission.outsideResources capture.erase ⊆
      (front.erase.append (.spent owner answer tail.erase)).visible := by
  rw [erase_append] at support
  obtain ⟨inside, boundary⟩ := supported_decompose front.erase support
  cases boundary with
  | live owner input answer saved rest ambient captured outside =>
      have external := Admission.outside_resources_supported captured
      intro resource member
      have supplied := external member
      simpa only [visible_append, Control.visible, List.append_nil] using
        List.mem_append_right front.erase.visible supplied

/-- A checked caller execution cannot replace the saved code of an existing
owner. Its original structural closing certificate therefore applies at any
later live occurrence, with resource support derived from the current state. -/
theorem retained_discard_access
    (earlierValid : Valid operations declarations policy earlierRegistry earlierTables [] []
      earlier output earlierDemand earlierRow bound)
    (valid : Valid operations declarations policy registry tables [] []
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (steps : NamedAccessSteps [] earlier
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩)
    (located : SourceTemplates.CapturedIn owner original earlier.execution.configuration.stack)
    (built : makePlan original = some originalPlan)
    (closing : Admission.OpenCloses original.erase .nil .nil
      (Admission.outsideResources original.erase) outward (originalPlan.map CloseEntry.erase))
    (internal : InternalUses original.erase.liveTickets original.erase.pending)
    (resolved : scope.resolve binder = some owner)
    (requests : RequestsResolved stack.erase outward) :
    AccessChecks ⟨.discard binder, scope, stack⟩ [] := by
  constructor
  · intro identity payload answer savedScope current value tail same closed
    have expressionSame := congrArg Configuration.expression same
    dsimp only at expressionSame
    rw [← expressionSame] at closed
    cases closed.1
  · intro requested operation operand current whole capture tail handler same cut closed
    cases congrArg Configuration.expression same
  · intro other actualOwner current caller input answer front capture tail plan same actualResolved actualBuilt
    have binderSame := Code.discard.inj (congrArg Configuration.expression same)
    have scopeSame := congrArg Configuration.scope same
    have stackSame := congrArg Configuration.stack same
    dsimp only at scopeSame stackSame
    subst other
    subst current
    subst stack
    have ownerSame := Option.some.inj (resolved.symm.trans actualResolved)
    subst actualOwner
    have currentLocation : SourceTemplates.CapturedIn owner capture
        (front.append (.live owner input answer capture caller tail)) :=
      RecursiveRecords.located_below front .here
    have sameCapture := SavedCaptureIdentity.checked_same_capture steps earlierValid.usage
      (ScopedPortJoint.usage_history_iff.mpr earlierValid.registry) located currentLocation
    rw [sameCapture] at built closing internal
    have samePlan := Option.some.inj (built.symm.trans actualBuilt)
    subst originalPlan
    have resources := saved_resources_supported valid.support.control
    have provided : RequestsResolved (front.erase.append (.spent owner answer tail.erase)) outward := by
      simpa only [RequestsResolved, erase_append, Stack.erase, resolve_append, Control.resolve] using requests
    exact .checked (Admission.open_closes_materialize (original := .nil) (surviving := .nil)
      (outer := front.erase.append (.spent owner answer tail.erase)) closing resources provided) internal

private theorem discard_step_results
    (raw : RawStep before after [.close identity] [.ticket owner])
    (returns : ConfigurationReturns declarations registry world before bound) :
    ConfigurationReturns declarations registry world after bound := by
  cases raw
  exact (CompletionFrames.discard_step (by assumption) (by assumption) returns).2

private theorem discard_step_resolves
    (raw : RawStep before after [.close identity] [.ticket owner])
    (same : before.expression = .discard binder) : before.scope.resolve binder = some owner := by
  cases raw
  cases same
  assumption

/-- The existing structural footprint checker supplies physical resolution of
all advertised effects, using the established selection correspondence. -/
theorem checked_closing_requests
    (checked : ProtectionContracts.checkFootprint (CallableProtectionFrames.contextOf tables stack) row = true) :
    RequestsResolved stack.erase (row.map ProtectionContracts.Demand.effect) := by
  intro effect member
  obtain ⟨request, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨target, mode, selected⟩ := RecursiveRequestProgress.admitted_selection
    (ProtectionContracts.check_footprint_iff.mp checked request present)
  rw [CallableProtectionFrames.context_realizes] at selected
  have resolved := ProtectionContexts.select_target (requested := request.effect)
    (incoming := request.held) stack.erase
  rw [selected] at resolved
  exact ⟨target, resolved.symm⟩

/-- Source checking and runtime name history derive the actual cleanup
footprint's successful check in the surviving caller. Retirement separation
and template evaluation reuse the existing plan proofs. -/
theorem current_disposal_footprint {front capture tail : Stack}
    (valid : Valid operations declarations policy registry tables outside ambient
      ⟨⟨⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ output demand row bound)
    (resolved : scope.resolve binder = some owner) :
    ∃ (plan : List CloseEntry) (raw : ProtectionContracts.Footprint)
      (requirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan))
      (closingRow : ProtectionContracts.Footprint),
      makePlan capture = some plan ∧
      DeclaredSourceClosing.PlanTemplate operations policy registry.contracts tables (resourceWorld issued)
        .none plan raw requirements ∧
      ProtectionResiduals.residualize
        (CallableProtectionFrames.contextOf tables (front.append (.spent owner answer caller tail))) raw = some closingRow ∧
      closingRow ⊆ row ∧ ProtectionContracts.checkFootprint outside closingRow = true ∧
      ProtectionContracts.checkFootprint
        (CallableProtectionFrames.contextOf tables (front.append (.spent owner answer caller tail)) ++ outside) raw = true := by
  obtain ⟨plan, raw, requirements, store, closingRow, built, template, checked, included, accepted⟩ :=
    DeclaredSourceDisposal.current_disposal_plan valid.source resolved
  have distinct := (history_gives_distinct_names valid.names valid.ledger).1
  have separate : ∀ nested ∈ OwnerClosingSource.retirements plan,
      nested ∉ OwnerPhases.names (OwnerPhases.ofStack tables (front.append (.spent owner answer caller tail))) := by
    simpa only [OwnerPhases.ofStack, OwnerPhases.frameEntry, OwnerPhases.names] using
      (OwnerClosingSource.retirements_separate (tables := tables) (closeId := 0) (scope := scope) distinct built)
  have evaluated := RecursiveRequirements.checked_complete checked
  rw [RecursiveClosing.template_evaluation (DeclaredSourceClosing.template_erase template) separate] at evaluated
  have exported : OwnerSource.exportAt
      (OwnerPhases.ofStack tables (front.append (.spent owner answer caller tail)))
      (OwnerPhaseTransitions.spend
        (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner input answer capture caller tail)))) owner)
      raw = some closingRow := by
    cases ready : PhaseRechecking.checkOwners
        (OwnerPhaseTransitions.spend
          (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner input answer capture caller tail)))) owner)
        (OwnerClosingSource.retirements plan) with
    | false =>
        simp only [ready, Bool.cond_false] at evaluated
        cases evaluated
    | true => simpa only [ready, Bool.cond_true] using evaluated
  have unique : (ownedTickets (front.append (.live owner input answer capture caller tail))).Nodup := by
    cases valid.source with
    | checked _ _ unique _ _ => exact unique
  have phases := OwnerPhaseTransitions.trace_result (OwnerPhaseTransitions.resume_phase_trace unique)
  change OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answer caller tail)))) =
    OwnerPhaseTransitions.spend
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner input answer capture caller tail)))) owner at phases
  have callerReady : ∀ other ∈ activeTickets (front.append (.spent owner answer caller tail)),
      OwnerPhaseTransitions.spend
        (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner input answer capture caller tail)))) owner other = .available := by
    intro other member
    rw [← phases]
    apply if_pos
    rw [owned_tickets_append]
    exact List.mem_append_right _ (active_tickets_owned _ member)
  rw [RecursivePlanAdmission.caller_export callerReady] at exported
  exact ⟨plan, raw, requirements, closingRow, built, template, exported, included, accepted,
    ProtectionResiduals.residual_admitted_iff.mpr ⟨closingRow, exported, accepted⟩⟩

/-- With no external interpretation assumptions, the actual source cleanup
footprint has physical request targets at the current discard. Live-to-spent
replacement changes capabilities but leaves these physical targets unchanged. -/
theorem current_disposal_requests {front capture tail : Stack}
    (valid : Valid operations declarations policy registry tables [] ambient
      ⟨⟨⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ output demand row bound)
    (resolved : scope.resolve binder = some owner) :
    ∃ (plan : List CloseEntry) (raw : ProtectionContracts.Footprint)
      (requirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan)),
      makePlan capture = some plan ∧
      DeclaredSourceClosing.PlanTemplate operations policy registry.contracts tables (resourceWorld issued)
        .none plan raw requirements ∧
      RequestsResolved (front.append (.live owner input answer capture caller tail)).erase
        (raw.map ProtectionContracts.Demand.effect) := by
  obtain ⟨plan, raw, requirements, closingRow, built, template, exported, included, accepted, checked⟩ :=
    current_disposal_footprint valid resolved
  have requests := checked_closing_requests (by simpa only [List.append_nil] using checked)
  refine ⟨plan, raw, requirements, built, template, ?_⟩
  simpa only [RequestsResolved, erase_append, Stack.erase, resolve_append, Control.resolve] using requests

/-- Historical closing evidence and its currently provided request interface
construct disposal with full runtime preservation. The source footprint and
declared-request judgments can supply that interface independently. -/
theorem discard_from_retained_requests
    (earlierValid : Valid operations declarations policy earlierRegistry earlierTables [] []
      earlier output earlierDemand earlierRow bound)
    (valid : Valid operations declarations policy registry tables [] []
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (steps : NamedAccessSteps [] earlier
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩)
    (located : SourceTemplates.CapturedIn owner original earlier.execution.configuration.stack)
    (built : makePlan original = some originalPlan)
    (closing : Admission.OpenCloses original.erase .nil .nil
      (Admission.outsideResources original.erase) outward
      (originalPlan.map CloseEntry.erase))
    (internal : InternalUses original.erase.liveTickets original.erase.pending)
    (resolved : scope.resolve binder = some owner)
    (requests : RequestsResolved stack.erase outward) :
    ∃ identity after remaining,
      let before : NamedState := ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before (advanceState before after [.close identity] [.ticket owner]) ∧
      Valid operations declarations policy registry tables [] []
        (advanceState before after [.close identity] [.ticket owner]) output remaining row bound ∧
      demand = owner :: remaining := by
  have checks := retained_discard_access earlierValid valid steps located built closing internal resolved requests
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.close (fun _ => rfl) valid.ledger.2
  obtain ⟨after, actualOwner, remaining, raw, source, demandSame, trace⟩ :=
    DeclaredSourceDisposal.discard_preserves valid.source identity
  have ownerSame := Option.some.inj (resolved.symm.trans (discard_step_resolves raw rfl))
  subst actualOwner
  have results := discard_step_results raw valid.results
  have freshHandlers : (activations ++ enteredActivations ⟨.discard binder, scope, stack⟩ after).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  refine ⟨identity, after, remaining, ⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩, ?_, demandSame⟩
  apply assemble_event valid raw fresh freshHandlers checks
  · simpa [resource_world_append, resourceWorld] using source
  · simpa [resource_world_append, resourceWorld] using results
  · rfl

/-- Preserve the finite-footprint interface by reusing the common disposal
construction. Source admission must still establish its historical certificate. -/
theorem discard_from_retained_certificate
    (earlierValid : Valid operations declarations policy earlierRegistry earlierTables [] []
      earlier output earlierDemand earlierRow bound)
    (valid : Valid operations declarations policy registry tables [] []
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (steps : NamedAccessSteps [] earlier
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩)
    (located : SourceTemplates.CapturedIn owner original earlier.execution.configuration.stack)
    (built : makePlan original = some originalPlan)
    (closing : Admission.OpenCloses original.erase .nil .nil
      (Admission.outsideResources original.erase) (closingRow.map ProtectionContracts.Demand.effect)
      (originalPlan.map CloseEntry.erase))
    (internal : InternalUses original.erase.liveTickets original.erase.pending)
    (resolved : scope.resolve binder = some owner)
    (requests : ProtectionContracts.checkFootprint (CallableProtectionFrames.contextOf tables stack) closingRow = true) :
    ∃ identity after remaining,
      let before : NamedState := ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before (advanceState before after [.close identity] [.ticket owner]) ∧
      Valid operations declarations policy registry tables [] []
        (advanceState before after [.close identity] [.ticket owner]) output remaining row bound ∧
      demand = owner :: remaining :=
  discard_from_retained_requests earlierValid valid steps located built closing internal resolved (checked_closing_requests requests)

/-- The existing scoped effect-stack rules provide the declared closing
interface at its live boundary. This judgment is independent of source rows. -/
theorem declared_closing_requests {registry : Owners.Registry} {front capture tail : Stack}
    (typed : ScopedPorts.EffectStack signature registry.contracts.ports world
      (front.append (.live owner input answer capture caller tail)) incoming [])
    (known : registry.contracts owner = some contract) :
    RequestsResolved (front.append (.live owner input answer capture caller tail)).erase contract.closeEffects := by
  obtain ⟨middle, inside, boundary⟩ := ScopedPorts.effect_stack_decompose front typed
  cases boundary with
  | live actual scope saved rest resume close bound =>
      have same := Option.some.inj ((Owners.ports_lookup known).symm.trans actual)
      cases same
      have provided : RequestsResolved tail.erase contract.closeEffects := by
        intro request member
        rcases ScopedPorts.effect_stack_provides_or_exports rest (close member) with found | impossible
        · exact found
        · cases impossible
      simpa only [RequestsResolved, erase_append, Stack.erase, resolve_append, Control.resolve] using
        (Admission.requests_resolved_under_prefix provided front.erase)

/-- Retained structural closing compatibility and the independent declared
effect-stack interface suffice for the complete current disposal step. No
equality between conservative request annotations and source footprints is used.
Establishing and preserving these premises from source admission remains open. -/
theorem discard_with_declared_interface {front capture tail : Stack}
    (earlierValid : Valid operations declarations policy earlierRegistry earlierTables [] []
      earlier output earlierDemand earlierRow bound)
    (valid : Valid operations declarations policy registry tables [] []
      ⟨⟨⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ output demand row bound)
    (steps : NamedAccessSteps [] earlier
      ⟨⟨⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩)
    (located : SourceTemplates.CapturedIn owner original earlier.execution.configuration.stack)
    (built : makePlan original = some originalPlan)
    (known : registry.contracts owner = some contract)
    (closing : Admission.OpenCloses original.erase .nil .nil
      (Admission.outsideResources original.erase) contract.closeEffects (originalPlan.map CloseEntry.erase))
    (internal : InternalUses original.erase.liveTickets original.erase.pending)
    (resolved : scope.resolve binder = some owner)
    (typed : ScopedPorts.EffectStack operations.ports registry.contracts.ports (resourceWorld issued)
      (front.append (.live owner input answer capture caller tail)) incoming []) :
    ∃ identity after remaining,
      let before : NamedState := ⟨⟨⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep [] before (advanceState before after [.close identity] [.ticket owner]) ∧
      Valid operations declarations policy registry tables [] []
        (advanceState before after [.close identity] [.ticket owner]) output remaining row bound ∧
      demand = owner :: remaining :=
  discard_from_retained_requests earlierValid valid steps located built closing internal resolved
    (declared_closing_requests typed known)

namespace DisposalInterfaceExample
open ResumeOnlyCapture.Examples
open SourceCallableExamples (operations policy)
open ClosingBudgetGap (contracts)

/-- Reuse the existing pure-callback example to distinguish the source
footprint check from structural preservation of declared callback requests.
This is not a counterexample to the combined execution invariant. -/
theorem source_footprint_does_not_supply_closing_certificate :
    ∃ requirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan),
      DeclaredSourceClosing.PlanTemplate operations policy contracts tables [] .none plan [] requirements ∧
      ProtectionContracts.checkFootprint [] ([] : ProtectionContracts.Footprint) = true ∧
      ¬ Admission.OpenCloses whole.erase .nil .nil (Admission.outsideResources whole.erase) []
        (plan.map CloseEntry.erase) := by
  refine ⟨_, DeclaredSourceClosing.PlanTemplate.invoke (action := action) (latent := [])
    (DeclaredSourceValues.from_legacy callback_source) .nil, rfl, ?_⟩
  intro certificate
  have resources : Admission.outsideResources whole.erase ⊆ Control.nil.visible := by decide
  have requests : RequestsResolved .nil [] := by simp [RequestsResolved]
  have closing := Admission.open_closes_materialize (original := .nil) (surviving := .nil)
    (outer := .nil) certificate resources requests
  have internal : InternalUses whole.erase.liveTickets whole.erase.pending := .nil
  have accepted := ClosingAdmission.checked_disposal_iff.mpr (Discardable.checked closing internal)
  change ClosingAdmission.checkedDisposal whole.erase Stack.nil.erase = some (plan.map CloseEntry.erase) at accepted
  rw [closing_rejected.2] at accepted
  cases accepted

end DisposalInterfaceExample
end Ash.OneShot.DeclaredExecution

#print axioms Ash.OneShot.DeclaredExecution.initial_state
#print axioms Ash.OneShot.DeclaredExecution.request_access_checks
#print axioms Ash.OneShot.DeclaredExecution.resume_only_capture
#print axioms Ash.OneShot.DeclaredExecution.resume_preserves

#print axioms Ash.OneShot.DeclaredExecution.value_step_results
#print axioms Ash.OneShot.DeclaredExecution.value_access_checks
#print axioms Ash.OneShot.DeclaredExecution.value_step_preserves
#print axioms Ash.OneShot.DeclaredExecution.value_progress
#print axioms Ash.OneShot.DeclaredExecution.ready_step_results
#print axioms Ash.OneShot.DeclaredExecution.ready_progress
#print axioms Ash.OneShot.DeclaredExecution.resource_entry

#print axioms Ash.OneShot.DeclaredExecution.focus_progress

#print axioms Ash.OneShot.DeclaredExecution.cleanup_entry
#print axioms Ash.OneShot.DeclaredExecution.handler_entry

#print axioms Ash.OneShot.DeclaredExecution.cell_update_preserves_results
#print axioms Ash.OneShot.DeclaredExecution.builtin_step_results
#print axioms Ash.OneShot.DeclaredExecution.builtin_step_source
#print axioms Ash.OneShot.DeclaredExecution.builtin_step_preserves
#print axioms Ash.OneShot.DeclaredExecution.request_selection

#print axioms Ash.OneShot.DeclaredExecution.saved_resources_supported
#print axioms Ash.OneShot.DeclaredExecution.retained_discard_access
#print axioms Ash.OneShot.DeclaredExecution.discard_from_retained_certificate

#print axioms Ash.OneShot.DeclaredExecution.checked_closing_requests
#print axioms Ash.OneShot.DeclaredExecution.current_disposal_footprint
#print axioms Ash.OneShot.DeclaredExecution.current_disposal_requests
#print axioms Ash.OneShot.DeclaredExecution.DisposalInterfaceExample.source_footprint_does_not_supply_closing_certificate
#print axioms Ash.OneShot.DeclaredExecution.discard_from_retained_requests
#print axioms Ash.OneShot.DeclaredExecution.declared_closing_requests
#print axioms Ash.OneShot.DeclaredExecution.discard_with_declared_interface
