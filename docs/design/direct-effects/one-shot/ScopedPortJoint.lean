import ScopedPortCompletion

/-!
One historical record with independent port/effect and one-shot usage projections.
Joint preservation uses actual scoped transitions, ownership and name history,
and explicit local access checks. Current-state value progress is conditional;
source-derived return-support and closing conditions remain separate work.
-/

namespace Ash.OneShot.ScopedPortJoint
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ScopedTyping (World resourceWorld resource_world_append)

variable {front cap tail : Stack} {issued completed : List Owner}

structure TicketRecord where
  contract : ContinuationContract
  permissions : OneShotRights

abbrev Registry := Nat → Option TicketRecord

def Registry.effects (registry : Registry) : EffectTickets :=
  fun owner => (registry owner).map TicketRecord.contract

def Registry.usage (registry : Registry) : UsageTickets :=
  fun owner => (registry owner).map TicketRecord.permissions

def Registry.insert (registry : Registry) (owner : Nat) (record : TicketRecord) : Registry :=
  fun other => if other = owner then some record else registry other

@[simp] theorem effects_insert (registry : Registry) :
    (registry.insert owner record).effects = registry.effects.insert owner record.contract := by
  funext other
  by_cases same : other = owner <;> simp [Registry.effects, Registry.insert, EffectTickets.insert, same]

@[simp] theorem usage_insert (registry : Registry) :
    (registry.insert owner record).usage = registry.usage.insert owner record.permissions := by
  funext other
  by_cases same : other = owner <;> simp [Registry.usage, Registry.insert, UsageTickets.insert, same]

/-- Both projections describe exactly the same historically issued owners. -/
def RegistryHistory (registry : Registry) (issued : List Owner) : Prop :=
  ∀ owner, (∃ record, registry owner = some record) ↔ Owner.ticket owner ∈ issued

theorem usage_history_iff : ScopedExecution.UsageRegistryHistory registry.usage issued ↔ RegistryHistory registry issued := by
  constructor <;> intro history owner <;> cases found : registry owner <;>
    simpa [Registry.usage, found] using history owner

theorem registry_fresh (history : RegistryHistory registry issued)
    (fresh : (issued ++ [Owner.ticket owner]).Nodup) : registry owner = none := by
  cases found : registry owner with
  | none => rfl
  | some record =>
      have used := (history owner).mp ⟨record, found⟩
      exact False.elim ((List.nodup_append.mp fresh).2.2 (.ticket owner) used (.ticket owner) (by simp) rfl)

def advanceState (before : NamedState) (after : Configuration) (created discharged : List Owner) : NamedState :=
  ⟨⟨after, before.execution.issued ++ created, discharged ++ before.execution.completed⟩,
    before.activations ++ enteredActivations before.execution.configuration after⟩

structure Valid (signature : Signature) (policy : TicketPolicy) (registry : Registry)
    (ambient : List Nat) (state : NamedState) (result : Port) (outgoing : List Instance) : Prop where
  ledger : Ledger state.execution.erase
  names : NameHistory state.execution state.activations
  support : AccessValid state.execution.configuration ambient
  effects : EffectConfigurationTyped signature registry.effects (resourceWorld state.execution.issued)
    state.execution.configuration result outgoing
  usage : ConfigurationUsage policy registry.usage state.execution.configuration
  registry : RegistryHistory registry state.execution.issued
  closed : state.execution.configuration.ResourceClosed

/-- Initial checks establish the facets separately. They do not establish
    compatibility or closing readiness of every future captured continuation. -/
theorem initial_configuration_valid
    (typed : Typed signature [] TypeEnv.empty .none outgoing expression result)
    (used : ScopedExpressions.Uses policy .none .available expression .available)
    (support : resourceDependencies expression.dependencies = []) :
    Valid signature policy (fun _ => none) []
      ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ result outgoing := by
  constructor
  · exact ⟨.refl [], by simp [RunState.erase]⟩
  · exact ⟨by simp [Stack.erase, Control.ticketNames], by simp [Stack.erase, Control.activations], by simp⟩
  · exact ⟨.nil _, by simp [support]⟩
  · exact ⟨result, outgoing, .checked .none typed, .nil, .nil (List.Subset.refl _)⟩
  · exact ⟨[], [], .idle .none used, .nil, List.nil_subset _, .refl _, by simp [ScopedExecution.ownedTickets]⟩
  · intro owner; simp
  · exact ⟨typed_resource_closed typed, trivial⟩

/-- Private proof assembly. Public results below independently derive the
    effect result; this is not an execution-admission rule. -/
private theorem assemble_event
    (raw : RawStep before.execution.configuration after created discharged)
    (freshOwners : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup)
    (checks : AccessChecks before.execution.configuration ambient)
    (valid : Valid signature policy registry ambient before result outgoing)
    (effects : EffectConfigurationTyped signature nextRegistry.effects (resourceWorld (before.execution.issued ++ created))
      after result outgoing)
    (update : nextRegistry.usage = advanceUsageTickets policy registry.usage after created) :
    Valid signature policy nextRegistry ambient (advanceState before after created discharged) result outgoing := by
  have step : NamedAccessStep ambient before (advanceState before after created discharged) :=
    ⟨.event before after created discharged raw freshOwners freshHandlers, checks⟩
  obtain ⟨ledger, names, support⟩ := named_access_step_preserves step valid.ledger valid.names valid.support
  have history := usage_history_iff.mpr valid.registry
  have usage := raw_step_preserves_configuration_usage raw
    (usage_checks_from_allocation_and_access history freshOwners checks) valid.usage
  have nextHistory := raw_step_preserves_usage_registry_history (policy := policy) raw history
  rw [← update] at usage nextHistory
  exact ⟨ledger, names, support, effects, usage, usage_history_iff.mp nextHistory,
    raw_step_preserves_resource_closure raw valid.closed⟩

private theorem assemble_old_world_event
    (raw : RawStep before.execution.configuration after created discharged)
    (freshOwners : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup)
    (checks : AccessChecks before.execution.configuration ambient)
    (valid : Valid signature policy registry ambient before result outgoing)
    (effects : EffectConfigurationTyped signature nextRegistry.effects (resourceWorld before.execution.issued) after result outgoing)
    (update : nextRegistry.usage = advanceUsageTickets policy registry.usage after created) :
    Valid signature policy nextRegistry ambient (advanceState before after created discharged) result outgoing :=
  assemble_event raw freshOwners freshHandlers checks valid
    (effect_configuration_world_weaken effects (by rw [resource_world_append]; exact List.subset_append_left _ _)) update

/-- Type-directed capture and independent usage checking allocate the same
    ticket owner, with one record containing the chosen contract and rights. -/
theorem capture_constructs_joint_configuration
    (cut : HandlerCut requested whole cap tail handler)
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : operand.IsValue)
    (fresh : (issued ++ [Owner.ticket owner]).Nodup)
    (checks : AccessChecks ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ ambient) :
    ∃ (parameter binder : Nat) (body : Code) (output : Port) (residual : List Instance),
      let initial : NamedState := ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer cap handler.scope tail⟩
      let record : TicketRecord := ⟨⟨output, eraseType handler.answer, residual, residual⟩, policy binder⟩
      NamedAccessStep ambient initial (advanceState initial after [.ticket owner] []) ∧
      Valid signature policy (registry.insert owner record) ambient
        (advanceState initial after [.ticket owner] []) result outgoing := by
  have empty := registry_fresh valid.registry fresh
  have effectEmpty : registry.effects owner = none := by simp [Registry.effects, empty]
  obtain ⟨parameter, binder, body, output, residual, raw, extension, effects⟩ :=
    capture_constructs_effect_configuration cut valid.effects isValue effectEmpty
  have freshHandlers : (activations ++ enteredActivations
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩
      ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer cap handler.scope tail⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  refine ⟨parameter, binder, body, output, residual,
    ⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩, ?_⟩
  apply assemble_old_world_event raw fresh freshHandlers checks valid
  · simpa only [effects_insert] using effects
  · simp [ScopedExecution.advanceUsageTickets]

/-- Effect and port projections use the same historical record. The actual
    raw annotations need only erase to its declared ports. -/
theorem active_live_contract
    (typed : EffectConfigurationTyped signature tickets world
      ⟨expression, scope, front.append (.live owner input answer cap caller tail)⟩ result outgoing) :
    ∃ contract, tickets owner = some contract ∧
      contract.input = eraseType input ∧ contract.answer = eraseType answer := by
  obtain ⟨type, effects, expression, ports, control⟩ := typed
  obtain ⟨middle, inside, outside⟩ := effect_stack_decompose front control
  cases outside with
  | live known scope saved rest resume close bound =>
      obtain ⟨middlePort, frontPorts, outsidePorts⟩ := stack_typed_decompose front ports
      cases outsidePorts with
      | live recorded caller captured tail =>
          simp only [EffectTickets.types, known, Option.map_some] at recorded
          obtain ⟨inputEq, answerEq⟩ := Prod.mk.inj (Option.some.inj recorded)
          exact ⟨_, known, inputEq, answerEq⟩

theorem resume_preserves_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing)
    (resolved : scope.resolve binder = some owner) (closed : ScopedExpressions.ClosedValue value)
    (checks : AccessChecks ⟨.resume binder value, scope,
      front.append (.live owner input answer cap caller tail)⟩ ambient) :
    let initial : NamedState := ⟨⟨⟨.resume binder value, scope,
      front.append (.live owner input answer cap caller tail)⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, scope, cap.append (front.append (.spent owner answer caller tail))⟩
    NamedAccessStep ambient initial (advanceState initial after [] [.ticket owner]) ∧
    Valid signature policy registry ambient (advanceState initial after [] [.ticket owner]) result outgoing := by
  have raw := RawStep.resume binder owner scope caller input answer front cap tail value closed resolved
  have fresh : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      ⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩
      ⟨value, scope, cap.append (front.append (.spent owner answer caller tail))⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  exact ⟨⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩,
    assemble_old_world_event raw fresh freshHandlers checks valid
      (resume_preserves_effect_configuration resolved valid.effects closed.1) rfl⟩

theorem discard_preserves_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.discard binder, scope, front.append (.live owner input answer cap caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing)
    (known : registry.effects owner = some contract)
    (resolved : scope.resolve binder = some owner) (built : makePlan cap = some plan)
    (planTyped : ScopedPorts.PlanTyped signature (resourceWorld issued) contract.closeEffects plan)
    (fresh : (issued ++ [Owner.close closeId]).Nodup)
    (checks : AccessChecks ⟨.discard binder, scope,
      front.append (.live owner input answer cap caller tail)⟩ ambient) :
    let initial : NamedState := ⟨⟨⟨.discard binder, scope,
      front.append (.live owner input answer cap caller tail)⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨.unit, scope, (closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))⟩
    NamedAccessStep ambient initial (advanceState initial after [.close closeId] [.ticket owner]) ∧
    Valid signature policy registry ambient (advanceState initial after [.close closeId] [.ticket owner]) result outgoing := by
  have raw := RawStep.discard binder owner closeId scope caller input answer front cap tail plan resolved built
  have freshHandlers : (activations ++ enteredActivations
      ⟨.discard binder, scope, front.append (.live owner input answer cap caller tail)⟩
      ⟨.unit, scope, (closeControl scope plan).append
        (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  exact ⟨⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩,
    assemble_old_world_event raw fresh freshHandlers checks valid
      (discard_preserves_effect_configuration known resolved valid.effects built planTyped) rfl⟩

private theorem closed_value_creates_no_owners
    (raw : RawStep before after created discharged) (closed : ScopedExpressions.ClosedValue before.expression) : created = [] := by
  cases raw <;> first | rfl | cases closed.1

/-- Includes actual callback invocation, outward resumed completion, scope
    return, and owner retirement whenever their pre-expression is a value. -/
theorem closed_value_preserves_joint_configuration
    (step : NamedAccessStep ambient before after) (closed : ScopedExpressions.ClosedValue before.execution.configuration.expression)
    (valid : Valid signature policy registry ambient before result outgoing) :
    Valid signature policy registry ambient after result outgoing := by
  cases step with
  | mk execution checks => cases execution with
      | event next created discharged raw freshOwners freshHandlers =>
          exact assemble_old_world_event raw freshOwners freshHandlers checks valid
            (raw_value_step_preserves_effect_configuration raw closed valid.effects)
            (by rw [closed_value_creates_no_owners raw closed]; rfl)

/-- Existing-annotation ordinary transitions. The builtin cases carry the
    actual nearest-cell selection proof and cannot stand for source capture. -/
inductive OrdinaryStep : Configuration → Configuration → Prop where
  | bind {tail : Stack} (closed : ScopedExpressions.ClosedValue value) (environment : ScopedExpressions.ClosedExcept parameter body)
      :
      OrdinaryStep ⟨.bind parameter value body, scope, tail⟩ ⟨body.subst parameter value, scope, tail⟩
  | beta {tail : Stack} (closed : ScopedExpressions.ClosedValue value) (closure : ScopedExpressions.ClosedValue (.lambda parameter body))
      :
      OrdinaryStep ⟨.app (.lambda parameter body) value, scope, tail⟩ ⟨body.subst parameter value, .none, tail⟩
  | ifTrue {tail : Stack} : OrdinaryStep ⟨.branch (.boolean true) yes no, scope, tail⟩ ⟨yes, scope, tail⟩
  | ifFalse {tail : Stack} : OrdinaryStep ⟨.branch (.boolean false) yes no, scope, tail⟩ ⟨no, scope, tail⟩
  | read (cell : CellUpdate identity payload payload before after) :
      OrdinaryStep ⟨.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before⟩
        ⟨.integer payload, scope, after⟩
  | write (cell : CellUpdate identity old new before after) :
      OrdinaryStep ⟨.perform (freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before⟩
        ⟨.unit, scope, after⟩

theorem ordinary_step_executes (step : OrdinaryStep before after) : RawStep before after [] [] := by
  cases step with
  | bind closed environment => exact .bind _ _ _ _ _ closed environment
  | beta closed closure => exact .beta _ _ _ _ _ closed closure
  | ifTrue => exact .ifTrue _ _ _ _
  | ifFalse => exact .ifFalse _ _ _ _
  | read cell => exact .readCell _ _ _ _ _ cell
  | write cell => exact .writeCell _ _ _ _ _ _ cell

theorem ordinary_step_preserves_effects (step : OrdinaryStep before after)
    (typed : EffectConfigurationTyped (withCellSignatures users) tickets world before result outgoing) :
    EffectConfigurationTyped (withCellSignatures users) tickets world after result outgoing := by
  cases step with
  | bind closed environment => exact bind_preserves_effect_configuration typed closed.1
  | beta closed closure => exact beta_preserves_effect_configuration typed closed.1
  | ifTrue => exact branch_preserves_effect_configuration (condition := true) typed
  | ifFalse => exact branch_preserves_effect_configuration (condition := false) typed
  | read cell => exact cell_read_preserves_effect_configuration typed cell
  | write cell => exact cell_write_preserves_effect_configuration typed cell

theorem ordinary_step_has_no_activation (step : OrdinaryStep before after) :
    enteredActivations before after = [] := by cases step <;> rfl

theorem ordinary_access_checks {expression : Code}
    (notValue : ¬ expression.IsValue)
    (notRequest : ∀ requested operation operand, expression ≠ .perform (freezeEffect requested) operation operand)
    (notDiscard : ∀ binder, expression ≠ .discard binder) :
    AccessChecks ⟨expression, scope, tail⟩ ambient := by
  constructor
  · intro identity payload answer savedScope current value rest same closed
    have sameExpression : expression = value := congrArg Configuration.expression same
    exact False.elim (notValue (sameExpression.symm ▸ closed.1))
  · intro requested operation operand current whole cap outside handler same cut closed
    exact False.elim (notRequest requested operation operand (congrArg Configuration.expression same))
  · intro binder owner current caller input answer front cap outside plan same resolve built
    exact False.elim (notDiscard binder (congrArg Configuration.expression same))

theorem ordinary_step_access_checks (step : OrdinaryStep before after) : AccessChecks before ambient := by
  cases step with
  | read selected | write selected => exact builtin_request_access_checks selected
  | bind | beta | ifTrue | ifFalse =>
      exact ordinary_access_checks (by simp [Code.IsValue])
        (by intro requested operation operand same; cases same) (by intro binder same; cases same)

theorem ordinary_step_preserves_joint_configuration
    (step : OrdinaryStep before.execution.configuration after)
    (valid : Valid (withCellSignatures users) policy registry ambient before result outgoing) :
    NamedAccessStep ambient before (advanceState before after [] []) ∧
    Valid (withCellSignatures users) policy registry ambient (advanceState before after [] []) result outgoing := by
  have checks := ordinary_step_access_checks step (ambient := ambient)
  have raw := ordinary_step_executes step
  have freshOwners : (before.execution.issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have noEntry : enteredActivations before.execution.configuration after = [] := ordinary_step_has_no_activation step
  have freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup := by
    simpa [noEntry] using valid.names.unique
  exact ⟨⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
    assemble_old_world_event raw freshOwners freshHandlers checks valid (ordinary_step_preserves_effects step valid.effects) rfl⟩


theorem focus_access_checks (focus : ScopedExecution.Focus whole child context) :
    AccessChecks ⟨whole, scope, tail⟩ ambient := by
  constructor
  · intro identity payload answer savedScope current value rest same closed
    have sameExpression : whole = value := congrArg Configuration.expression same
    exact False.elim (ScopedTyping.focus_is_not_value focus (sameExpression.symm ▸ closed.1))
  · intro requested operation operand current stack cap outside handler same cut closed
    cases focus <;> cases same
    exact False.elim ((by assumption : ¬ child.IsValue) closed.1)
  · intro binder owner current caller input answer front cap outside plan same resolve built
    cases focus <;> cases same

/-- Value typing supplies closure; independent access checks supply release
    exclusion. This conditional theorem does not claim source-derived safety. -/
theorem checked_value_event_constructs_joint_step
    (raw : RawStep before.execution.configuration after created discharged)
    (isValue : before.execution.configuration.expression.IsValue)
    (valid : Valid signature policy registry ambient before result outgoing)
    (checks : AccessChecks before.execution.configuration ambient) :
    NamedAccessStep ambient before (advanceState before after created discharged) ∧
    Valid signature policy registry ambient (advanceState before after created discharged) result outgoing := by
  obtain ⟨input, expression, stack⟩ := effect_configuration_has_types valid.effects
  have closed := at_type_value_closed expression isValue
  have noOwners := closed_value_creates_no_owners raw closed
  subst created
  have freshOwners : (before.execution.issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup := by
    simpa [value_enters_no_activation closed] using valid.names.unique
  have step : NamedAccessStep ambient before (advanceState before after [] discharged) :=
    ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩
  exact ⟨step, closed_value_preserves_joint_configuration step closed valid⟩

theorem focus_constructs_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨whole, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (focus : ScopedExecution.Focus whole child context) :
    ∃ plain : PlainData,
      let initial : NamedState := ⟨⟨⟨whole, scope, tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨child, scope, .push (.plain plain) tail⟩
      NamedAccessStep ambient initial (advanceState initial after [] []) ∧
      Valid signature policy registry ambient (advanceState initial after [] []) result outgoing := by
  obtain ⟨plain, raw, effects⟩ := focus_constructs_effect_configuration valid.effects focus
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩).Nodup := by
    simpa [focus_enters_no_activation focus] using valid.names.unique
  have checks := focus_access_checks focus (scope := scope) (tail := tail) (ambient := ambient)
  exact ⟨plain, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
    assemble_old_world_event raw freshOwners freshHandlers checks valid effects rfl⟩

theorem handler_entry_constructs_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.handle effectInst body clauses, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (fresh : (activations ++ [activation]).Nodup) :
    ∃ handler : HandlerData, handler.activation = activation ∧
      let initial : NamedState := ⟨⟨⟨.handle effectInst body clauses, scope, tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.handler handler) tail⟩
      NamedAccessStep ambient initial (advanceState initial after [] []) ∧
      Valid signature policy registry ambient (advanceState initial after [] []) result outgoing := by
  obtain ⟨handler, sameActivation, raw, effects⟩ := handler_entry_constructs_effect_configuration valid.effects activation
  have checks : AccessChecks ⟨.handle effectInst body clauses, scope, tail⟩ ambient :=
    ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand same; cases same) (by intro binder same; cases same)
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      ⟨.handle effectInst body clauses, scope, tail⟩ ⟨body, scope, .push (.handler handler) tail⟩).Nodup := by
    simpa [enteredActivations, sameActivation] using fresh
  exact ⟨handler, sameActivation, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
    assemble_old_world_event raw freshOwners freshHandlers checks valid effects rfl⟩

theorem cleanup_entry_constructs_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.cleanup callback body, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : callback.IsValue) (fresh : (issued ++ [Owner.cleanup identity]).Nodup) :
    ∃ action : ActionData,
      let initial : NamedState := ⟨⟨⟨.cleanup callback body, scope, tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.armed action) tail⟩
      NamedAccessStep ambient initial (advanceState initial after [.cleanup identity] []) ∧
      Valid signature policy registry ambient (advanceState initial after [.cleanup identity] []) result outgoing := by
  obtain ⟨action, identityEq, raw, effects⟩ := cleanup_entry_constructs_effect_configuration valid.effects isValue identity
  have checks : AccessChecks ⟨.cleanup callback body, scope, tail⟩ ambient :=
    ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand same; cases same) (by intro binder same; cases same)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.cleanup callback body, scope, tail⟩ ⟨body, scope, .push (.armed action) tail⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  exact ⟨action, ⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩,
    assemble_old_world_event raw fresh freshHandlers checks valid effects rfl⟩

theorem non_request_preserves_usage_registry
    (raw : RawStep before after created discharged)
    (notRequest : ∀ requested operation operand, before.expression ≠ .perform (freezeEffect requested) operation operand) :
    tickets = ScopedExecution.advanceUsageTickets policy tickets after created := by
  cases raw with
  | capture requested operation parameter binder owner operand body scope whole cap tail handler output cut selected closed ready =>
      exact False.elim (notRequest requested operation operand rfl)
  | focus | plug | bind | beta | ifTrue | ifFalse | enterHandler | leaveHandler | enterCell | leaveCell
  | enterCleanup | startCleanup | finishCleanup | resume | discard | leaveClause | finishClose | retire | readCell | writeCell => rfl

/-- Fresh acquisition is derived from finite issued history, then the same
    event joins generative typing with access, names, ownership and usage. -/
theorem resource_entry_constructs_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.resource binder initializer body, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : initializer.IsValue) :
    ∃ after,
      NamedAccessStep ambient ⟨⟨⟨.resource binder initializer body, scope, tail⟩, issued, completed⟩, activations⟩ after ∧
      Valid signature policy registry ambient after result outgoing := by
  obtain ⟨afterExecution, event, effects, afterLedger⟩ := resource_entry_effect_progress valid.effects isValue valid.ledger
  cases event with
  | event after created discharged raw freshOwners =>
      have freshHandlers : (activations ++ enteredActivations
          ⟨.resource binder initializer body, scope, tail⟩ after).Nodup := by
        simpa [enteredActivations] using valid.names.unique
      have checks : AccessChecks ⟨.resource binder initializer body, scope, tail⟩ ambient :=
        ordinary_access_checks (by simp [Code.IsValue])
          (by intro requested operation operand same; cases same) (by intro binder same; cases same)
      exact ⟨_, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
        assemble_event raw freshOwners freshHandlers checks valid effects
          (non_request_preserves_usage_registry raw (by intro requested operation operand same; cases same))⟩

/-- Structural effect readiness supplies the plan and the ledger supplies a
    fresh close owner. The independent structural access/interpretation check
    is still explicit; readiness of later captures is not asserted. -/
theorem ready_disposal_constructs_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.discard binder, scope, front.append (.live owner input answer cap caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing)
    (known : registry.effects owner = some contract) (resolved : scope.resolve binder = some owner)
    (ready : CloseReady signature (resourceWorld issued) contract.closeEffects cap)
    (checks : AccessChecks ⟨.discard binder, scope,
      front.append (.live owner input answer cap caller tail)⟩ ambient) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨.discard binder, scope, front.append (.live owner input answer cap caller tail)⟩,
        issued, completed⟩, activations⟩ after ∧
      Valid signature policy registry ambient after result outgoing := by
  obtain ⟨plan, built, planTyped⟩ := close_ready_constructs_plan ready
  obtain ⟨closeId, fresh⟩ := Progress.fresh_close_exists valid.ledger.2
  exact ⟨_, discard_preserves_joint_configuration valid known resolved built planTyped fresh checks⟩

/-- Canonical forms for the unit input of completion frames. -/
theorem scoped_unit_value
    (typed : Typed signature world environment ticket allowed value .unit)
    (isValue : value.IsValue) : value = .unit := by
  cases typed <;> simp_all [Code.IsValue]

theorem value_raw_progress
    (typed : ConfigurationTyped signature effectTickets world before result)
    (usage : ConfigurationUsage policy usageTickets before)
    (isValue : before.expression.IsValue) :
    before.stack = .nil ∨ ∃ after discharged, RawStep before after [] discharged := by
  obtain ⟨value, scope, stack⟩ := before
  obtain ⟨input, expression, control⟩ := typed
  have closed := at_type_value_closed expression isValue
  cases stack with
  | nil => exact Or.inl rfl
  | live owner input answer capture caller tail =>
      exact False.elim (live_clause_cannot_return_unconsumed isValue usage)
  | spent owner answer caller tail =>
      exact Or.inr ⟨_, [], .leaveClause owner answer value closed scope caller tail⟩
  | push frame tail =>
      right
      cases control with
      | push frameTyped rest =>
          cases frame with
          | plain plain => exact ⟨_, [], .plug plain value closed scope tail⟩
          | handler handler => exact ⟨_, [], .leaveHandler handler value closed scope tail⟩
          | cell identity payload savedScope answer =>
              exact ⟨_, [.resource identity], .leaveCell identity payload answer savedScope scope value closed tail⟩
          | armed action => exact ⟨_, [], .startCleanup action value closed scope tail⟩
          | running action saved savedClosed =>
              have unit : value = .unit := scoped_unit_value (at_type_closed_value expression closed) isValue
              subst value
              exact ⟨_, [.cleanup action.identity], .finishCleanup action saved savedClosed scope tail⟩
          | unwinding action => cases frameTyped
          | closing identity savedScope =>
              have unit : value = .unit := scoped_unit_value (at_type_closed_value expression closed) isValue
              subst value
              exact ⟨_, [.close identity], .finishClose identity scope savedScope tail⟩
          | retiring owner =>
              have unit : value = .unit := scoped_unit_value (at_type_closed_value expression closed) isValue
              subst value
              exact ⟨_, [.ticket owner], .retire owner scope tail⟩

/-- Conditional completion progress preserves all seven fields. Freshness
    follows from history, but actual release access remains an explicit premise. -/
theorem checked_value_progress
    (valid : Valid signature policy registry ambient before result outgoing)
    (isValue : before.execution.configuration.expression.IsValue)
    (checks : AccessChecks before.execution.configuration ambient) :
    before.execution.configuration.stack = .nil ∨
    ∃ after, NamedAccessStep ambient before after ∧
      Valid signature policy registry ambient after result outgoing := by
  have typed := effect_configuration_has_types valid.effects
  rcases value_raw_progress typed valid.usage isValue with terminal | step
  · exact Or.inl terminal
  · obtain ⟨after, discharged, raw⟩ := step
    obtain ⟨input, expression, control⟩ := typed
    exact Or.inr ⟨_, checked_value_event_constructs_joint_step raw isValue valid checks⟩

/-- Empty control has discharged every issued owner exactly once, by the
    conserved ledger. This does not assert termination of arbitrary execution. -/
theorem terminal_ledger_settled
    (valid : Valid signature policy registry ambient before result outgoing)
    (terminal : before.execution.configuration.stack = .nil) :
    before.execution.issued.Perm before.execution.completed ∧ before.execution.completed.Nodup := by
  have balance := valid.ledger.1
  have unique := valid.ledger.2
  simp only [RunState.erase, terminal, Stack.erase, Control.owners, List.nil_append] at balance
  exact ⟨balance, balance.nodup unique⟩

/-- Active accessibility produces an actual live boundary on the active spine;
    dormant captures are never searched. -/
theorem active_ticket_has_boundary {stack : Stack} (present : owner ∈ ScopedExecution.activeTickets stack) :
    ∃ (front : Stack), ∃ input answer capture caller tail,
      stack = front.append (.live owner input answer capture caller tail) := by
  induction stack with
  | nil => cases present
  | push frame rest ih =>
      obtain ⟨front, input, answer, capture, caller, tail, same⟩ := ih present
      exact ⟨.push frame front, input, answer, capture, caller, tail, by simp [Stack.append, same]⟩
  | live name input answer capture caller rest ihCapture ihRest =>
      rcases List.mem_cons.mp present with same | later
      · subst name
        exact ⟨.nil, input, answer, capture, caller, rest, rfl⟩
      · obtain ⟨front, q, a, saved, savedCaller, tail, same⟩ := ihRest later
        exact ⟨.live name input answer capture caller front, q, a, saved, savedCaller, tail,
          by simp [Stack.append, same]⟩
  | spent name answer caller rest ih =>
      obtain ⟨front, input, a, capture, savedCaller, tail, same⟩ := ih present
      exact ⟨.spent name answer caller front, input, a, capture, savedCaller, tail,
        by simp [Stack.append, same]⟩

theorem resume_demand_supplies_owner
    (checked : ScopedExecution.CodeDemand policy tickets scope (.resume binder value) demand) :
    ∃ owner, scope.resolve binder = some owner ∧ demand = [owner] := by
  cases checked with
  | idle scope used => cases used
  | consume known used => cases used with
      | resume permitted operand => exact ⟨_, by simp [Execution.Scope.resolve], rfl⟩

/-- A fully evaluated resume operand can always resume. Both lexical resolution
    and the active boundary are derived from usage, rather than supplied as
    premises. Full clause-prefix restoration preserves the same registry. -/
theorem resume_value_progress
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : value.IsValue) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Valid signature policy registry ambient after result outgoing := by
  obtain ⟨current, demand, code, control, accessible, balance, unique⟩ := valid.usage
  obtain ⟨owner, resolved, same⟩ := resume_demand_supplies_owner code
  have present : owner ∈ ScopedExecution.activeTickets stack := accessible (same ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := active_ticket_has_boundary present
  subst stack
  have typed := effect_configuration_has_types valid.effects
  obtain ⟨type, expression, ports⟩ := typed
  have closed : ClosedValue value := by
    cases expression with
    | checked scope typed => cases typed with
        | resume operand effects formed => exact typed_value_closed operand isValue
  refine ⟨_, resume_preserves_joint_configuration valid resolved closed ?_⟩
  exact ordinary_access_checks (by intro h; cases h)
    (by intros; intro h; cases h) (by intro other h; cases h)



namespace Examples
open ScopedSignatureGap.Examples (program program_uses_one_shot program_has_no_initial_resource_atoms)

def policy : TicketPolicy := fun _ => ActionRequirements.resumeOnly
def emptyRegistry : Registry := fun _ => none
def source : NamedState := ⟨⟨⟨program, .none, .nil⟩, [], []⟩, []⟩

theorem safe_source_valid : Valid ScopedPorts.Examples.signature policy emptyRegistry [] source .unit [] :=
  initial_configuration_valid ScopedPorts.Examples.generative_source_port_typed
    program_uses_one_shot program_has_no_initial_resource_atoms

theorem safe_entry_constructed :
    ∃ after, NamedAccessStep [] source after ∧
      Valid ScopedPorts.Examples.signature policy emptyRegistry [] after .unit [] :=
  resource_entry_constructs_joint_configuration safe_source_valid trivial

def escaping : NamedState := ⟨⟨ScopedPorts.RetainedExamples.escapingReturn, [.resource 0], []⟩, []⟩

/-- All seven current-state facets hold, but none supplies future release
    exclusion. This state is not claimed reachable from admitted source. -/
theorem escaping_current_valid :
    Valid ScopedPorts.Examples.signature policy emptyRegistry [] escaping ScopedPorts.Examples.callbackPort [] := by
  constructor
  · exact ⟨.refl _, by decide⟩
  · constructor
    · intro owner
      simp [escaping, ScopedPorts.RetainedExamples.escapingReturn, Stack.erase, ExecFrame.erase, Control.ticketNames]
    · intro activation
      simp [escaping, ScopedPorts.RetainedExamples.escapingReturn, Stack.erase, ExecFrame.erase, Control.activations, Frame.activation]
    · decide
  · exact ScopedPorts.CompletionExamples.live_support_does_not_supply_release.2.1
  · exact ScopedPorts.EffectExamples.connected_typing_does_not_imply_release.1
  · exact ⟨[], [], .idle .none (.lambda (.bind .resourceRef .integer)),
      .push (.cell ⟨_, .none⟩) (List.nil_subset _) .nil, List.nil_subset _, .refl _, by decide⟩
  · intro owner
    simp [emptyRegistry, escaping]
  · exact ⟨ScopedSignatureGap.Examples.payload_closed.2.1, trivial, trivial⟩

theorem joint_validity_does_not_supply_release :
    Valid ScopedPorts.Examples.signature policy emptyRegistry [] escaping ScopedPorts.Examples.callbackPort [] ∧
      ¬ AccessChecks escaping.execution.configuration [] :=
  ⟨escaping_current_valid, ScopedPorts.RetainedExamples.escaping_return_access_rejected⟩

/-- Dropping the access premise would make current value progress false for
    this invariant: the counterexample has no admitted named successor. -/
theorem joint_valid_value_can_lack_admitted_step :
    Valid ScopedPorts.Examples.signature policy emptyRegistry [] escaping ScopedPorts.Examples.callbackPort [] ∧
    escaping.execution.configuration.expression.IsValue ∧
    ¬ ∃ after, NamedAccessStep [] escaping after := by
  refine ⟨escaping_current_valid, trivial, ?_⟩
  rintro ⟨after, event, checks⟩
  exact joint_validity_does_not_supply_release.2 checks

end Examples

end Ash.OneShot.ScopedPortJoint

#print axioms Ash.OneShot.ScopedPortJoint.effects_insert
#print axioms Ash.OneShot.ScopedPortJoint.usage_insert
#print axioms Ash.OneShot.ScopedPortJoint.usage_history_iff
#print axioms Ash.OneShot.ScopedPortJoint.registry_fresh
#print axioms Ash.OneShot.ScopedPortJoint.initial_configuration_valid
#print axioms Ash.OneShot.ScopedPortJoint.capture_constructs_joint_configuration
#print axioms Ash.OneShot.ScopedPortJoint.active_live_contract
#print axioms Ash.OneShot.ScopedPortJoint.resume_preserves_joint_configuration
#print axioms Ash.OneShot.ScopedPortJoint.discard_preserves_joint_configuration
#print axioms Ash.OneShot.ScopedPortJoint.closed_value_preserves_joint_configuration
#print axioms Ash.OneShot.ScopedPortJoint.ordinary_step_executes
#print axioms Ash.OneShot.ScopedPortJoint.ordinary_step_preserves_effects
#print axioms Ash.OneShot.ScopedPortJoint.ordinary_step_has_no_activation
#print axioms Ash.OneShot.ScopedPortJoint.ordinary_access_checks
#print axioms Ash.OneShot.ScopedPortJoint.ordinary_step_access_checks
#print axioms Ash.OneShot.ScopedPortJoint.ordinary_step_preserves_joint_configuration
#print axioms Ash.OneShot.ScopedPortJoint.focus_access_checks
#print axioms Ash.OneShot.ScopedPortJoint.checked_value_event_constructs_joint_step
#print axioms Ash.OneShot.ScopedPortJoint.focus_constructs_joint_configuration
#print axioms Ash.OneShot.ScopedPortJoint.handler_entry_constructs_joint_configuration
#print axioms Ash.OneShot.ScopedPortJoint.cleanup_entry_constructs_joint_configuration
#print axioms Ash.OneShot.ScopedPortJoint.non_request_preserves_usage_registry
#print axioms Ash.OneShot.ScopedPortJoint.resource_entry_constructs_joint_configuration
#print axioms Ash.OneShot.ScopedPortJoint.ready_disposal_constructs_joint_configuration
#print axioms Ash.OneShot.ScopedPortJoint.scoped_unit_value
#print axioms Ash.OneShot.ScopedPortJoint.value_raw_progress
#print axioms Ash.OneShot.ScopedPortJoint.checked_value_progress
#print axioms Ash.OneShot.ScopedPortJoint.terminal_ledger_settled
#print axioms Ash.OneShot.ScopedPortJoint.active_ticket_has_boundary
#print axioms Ash.OneShot.ScopedPortJoint.resume_demand_supplies_owner
#print axioms Ash.OneShot.ScopedPortJoint.resume_value_progress
#print axioms Ash.OneShot.ScopedPortJoint.Examples.safe_source_valid
#print axioms Ash.OneShot.ScopedPortJoint.Examples.safe_entry_constructed
#print axioms Ash.OneShot.ScopedPortJoint.Examples.escaping_current_valid
#print axioms Ash.OneShot.ScopedPortJoint.Examples.joint_validity_does_not_supply_release

#print axioms Ash.OneShot.ScopedPortJoint.Examples.joint_valid_value_can_lack_admitted_step
