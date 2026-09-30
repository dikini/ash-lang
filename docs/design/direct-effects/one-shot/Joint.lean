import UsageExecution

/-!
One runtime ticket registry with independently checked type/effect and usage
projections. Joint transition proofs use the same raw transition, allocation
history, and structural access checks. They do not define source admission or
assume that those checks hold for future execution.
-/

namespace Ash.OneShot.Joint
open Syntax Execution Typing

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

theorem usage_history_iff : UsageRegistryHistory registry.usage issued ↔ RegistryHistory registry issued := by
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

/-- One configuration, one registry, and independent derivations of each facet. -/
structure Valid (signature : Signature) (policy : TicketPolicy) (registry : Registry)
    (ambient : List Nat) (state : NamedState) (result : Ty) (outgoing : List Instance) : Prop where
  ledger : Ledger state.execution.erase
  names : NameHistory state.execution state.activations
  support : AccessValid state.execution.configuration ambient
  effects : EffectConfigurationTyped signature registry.effects state.execution.configuration result outgoing
  usage : ConfigurationUsage policy registry.usage state.execution.configuration
  registry : RegistryHistory registry state.execution.issued

/-- Closed annotated expressions initialize every facet from their independent
    checks. This does not establish compatibility of all future captured cuts. -/
theorem initial_configuration_valid
    (typed : Typed signature TypeEnv.empty .none outgoing expression result)
    (used : Uses policy .none .available expression .available)
    (support : resourceDependencies expression.dependencies = []) :
    Valid signature policy (fun _ => none) []
      ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ result outgoing := by
  constructor
  · exact ⟨.refl [], by simp [RunState.erase]⟩
  · exact ⟨by simp [Stack.erase, Control.ticketNames], by simp [Stack.erase, Control.activations], by simp⟩
  · exact ⟨.nil _, by simp [support]⟩
  · exact ⟨result, outgoing, .checked .none typed, .nil, .nil (fun _ used => used)⟩
  · exact ⟨[], [], .idle .none used, .nil, List.nil_subset _, .refl _, by simp [ownedTickets]⟩
  · intro owner
    simp

/-- Proof assembly only: the public transition theorems below derive the
    effect result independently. This is not an execution-admission rule. -/
private theorem assemble_event
    (raw : RawStep before.execution.configuration after created discharged)
    (freshOwners : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup)
    (checks : AccessChecks before.execution.configuration ambient)
    (valid : Valid signature policy registry ambient before result outgoing)
    (effects : EffectConfigurationTyped signature nextRegistry.effects after result outgoing)
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
  exact ⟨ledger, names, support, effects, usage, usage_history_iff.mp nextHistory⟩

/-- Type-directed capture and independent usage checking allocate the same
    ticket owner, with one record containing the chosen contract and rights. -/
theorem capture_constructs_joint_configuration
    (cut : HandlerCut requested whole cap tail handler)
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.perform requested operation operand, scope, whole⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : operand.IsValue)
    (hygiene : ∀ parameter binder body, ClauseAt operation handler.clauses parameter binder body → ResourceFresh operand body)
    (fresh : (issued ++ [Owner.ticket owner]).Nodup)
    (checks : AccessChecks ⟨.perform requested operation operand, scope, whole⟩ ambient) :
    ∃ (parameter binder : Nat) (body : Expr) (output : Ty) (residual : List Instance),
      let initial : NamedState := ⟨⟨⟨.perform requested operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner output handler.answer cap handler.scope tail⟩
      let record : TicketRecord := ⟨⟨output, handler.answer, residual, residual⟩, policy binder⟩
      NamedAccessStep ambient initial (advanceState initial after [.ticket owner] []) ∧
      Valid signature policy (registry.insert owner record) ambient
        (advanceState initial after [.ticket owner] []) result outgoing := by
  have empty := registry_fresh valid.registry fresh
  have effectEmpty : registry.effects owner = none := by simp [Registry.effects, empty]
  obtain ⟨parameter, binder, body, output, residual, raw, extension, effects⟩ :=
    capture_constructs_effect_configuration cut valid.effects isValue hygiene effectEmpty
  have freshHandlers : (activations ++ enteredActivations
      ⟨.perform requested operation operand, scope, whole⟩
      ⟨body.subst parameter operand, .ticket binder owner,
        .live owner output handler.answer cap handler.scope tail⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  refine ⟨parameter, binder, body, output, residual,
    ⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩, ?_⟩
  apply assemble_event raw fresh freshHandlers checks valid
  · simpa only [effects_insert] using effects
  · simp [advanceUsageTickets]

/-- The actual active live boundary determines the registered effect contract. -/
theorem active_live_contract
    (typed : EffectConfigurationTyped signature tickets
      ⟨expression, scope, front.append (.live owner input answer cap caller tail)⟩ result outgoing) :
    ∃ contract, tickets owner = some contract ∧ contract.input = input ∧ contract.answer = answer := by
  obtain ⟨type, effects, expression, ports, control⟩ := typed
  obtain ⟨middle, inside, outside⟩ := effect_stack_decompose front control
  cases outside with
  | live known scope saved rest resume close bound => exact ⟨_, known, rfl, rfl⟩

theorem resume_preserves_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value)
    (checks : AccessChecks ⟨.resume binder value, scope,
      front.append (.live owner input answer cap caller tail)⟩ ambient) :
    let initial : NamedState := ⟨⟨⟨.resume binder value, scope,
      front.append (.live owner input answer cap caller tail)⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, scope, cap.append (front.append (.spent owner answer caller tail))⟩
    NamedAccessStep ambient initial (advanceState initial after [] [.ticket owner]) ∧
    Valid signature policy registry ambient (advanceState initial after [] [.ticket owner]) result outgoing := by
  obtain ⟨contract, known, rfl, rfl⟩ := active_live_contract valid.effects
  have raw := RawStep.resume binder owner scope caller contract.input contract.answer front cap tail value closed resolved
  have fresh : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      ⟨.resume binder value, scope, front.append (.live owner contract.input contract.answer cap caller tail)⟩
      ⟨value, scope, cap.append (front.append (.spent owner contract.answer caller tail))⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  exact ⟨⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩,
    assemble_event raw fresh freshHandlers checks valid
      (resume_preserves_effect_configuration known resolved valid.effects closed.1) rfl⟩

theorem discard_preserves_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.discard binder, scope, front.append (.live owner contract.input contract.answer cap caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing)
    (known : registry.effects owner = some contract)
    (resolved : scope.resolve binder = some owner) (built : makePlan cap = some plan)
    (planTyped : PlanTyped signature contract.closeEffects plan)
    (fresh : (issued ++ [Owner.close closeId]).Nodup)
    (checks : AccessChecks ⟨.discard binder, scope,
      front.append (.live owner contract.input contract.answer cap caller tail)⟩ ambient) :
    let initial : NamedState := ⟨⟨⟨.discard binder, scope,
      front.append (.live owner contract.input contract.answer cap caller tail)⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨.unit, scope, (closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner contract.answer caller tail)))⟩
    NamedAccessStep ambient initial (advanceState initial after [.close closeId] [.ticket owner]) ∧
    Valid signature policy registry ambient (advanceState initial after [.close closeId] [.ticket owner]) result outgoing := by
  have raw := RawStep.discard binder owner closeId scope caller contract.input contract.answer front cap tail plan resolved built
  have freshHandlers : (activations ++ enteredActivations
      ⟨.discard binder, scope, front.append (.live owner contract.input contract.answer cap caller tail)⟩
      ⟨.unit, scope, (closeControl scope plan).append
        (.push (.closing closeId scope) (front.append (.spent owner contract.answer caller tail)))⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  exact ⟨⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩,
    assemble_event raw fresh freshHandlers checks valid
      (discard_preserves_effect_configuration known resolved valid.effects built planTyped) rfl⟩

private theorem closed_value_creates_no_owners
    (raw : RawStep before after created discharged) (closed : ClosedValue before.expression) : created = [] := by
  cases raw <;> first | rfl | cases closed.1

/-- Includes actual callback invocation, outward resumed completion, scope
    return, and owner retirement whenever their pre-expression is a value. -/
theorem closed_value_preserves_joint_configuration
    (step : NamedAccessStep ambient before after) (closed : ClosedValue before.execution.configuration.expression)
    (valid : Valid signature policy registry ambient before result outgoing) :
    Valid signature policy registry ambient after result outgoing := by
  cases step with
  | mk execution checks => cases execution with
      | event next created discharged raw freshOwners freshHandlers =>
          exact assemble_event raw freshOwners freshHandlers checks valid
            (raw_value_step_preserves_effect_configuration raw closed valid.effects)
            (by rw [closed_value_creates_no_owners raw closed]; rfl)

/-- Existing-annotation ordinary transitions. The builtin cases carry the
    actual nearest-cell selection proof and cannot stand for source capture. -/
inductive OrdinaryStep : Configuration → Configuration → Prop where
  | bind {tail : Stack} (closed : ClosedValue value) (environment : ClosedExcept parameter body)
      (fresh : ResourceFresh value body) :
      OrdinaryStep ⟨.bind parameter value body, scope, tail⟩ ⟨body.subst parameter value, scope, tail⟩
  | beta {tail : Stack} (closed : ClosedValue value) (closure : ClosedValue (.lambda parameter body))
      (fresh : ResourceFresh value body) :
      OrdinaryStep ⟨.app (.lambda parameter body) value, scope, tail⟩ ⟨body.subst parameter value, .none, tail⟩
  | ifTrue {tail : Stack} : OrdinaryStep ⟨.branch (.boolean true) yes no, scope, tail⟩ ⟨yes, scope, tail⟩
  | ifFalse {tail : Stack} : OrdinaryStep ⟨.branch (.boolean false) yes no, scope, tail⟩ ⟨no, scope, tail⟩
  | read (cell : CellUpdate identity payload payload before after) :
      OrdinaryStep ⟨.perform (.cell identity) 0 (.resourceRef identity), scope, before⟩
        ⟨.integer payload, scope, after⟩
  | write (cell : CellUpdate identity old new before after) :
      OrdinaryStep ⟨.perform (.cell identity) 1 (.pair (.resourceRef identity) (.integer new)), scope, before⟩
        ⟨.unit, scope, after⟩

theorem ordinary_step_executes (step : OrdinaryStep before after) : RawStep before after [] [] := by
  cases step with
  | bind closed environment fresh => exact .bind _ _ _ _ _ closed environment fresh
  | beta closed closure fresh => exact .beta _ _ _ _ _ closed closure fresh
  | ifTrue => exact .ifTrue _ _ _ _
  | ifFalse => exact .ifFalse _ _ _ _
  | read cell => exact .readCell _ _ _ _ _ cell
  | write cell => exact .writeCell _ _ _ _ _ _ cell

theorem ordinary_step_preserves_effects (step : OrdinaryStep before after)
    (typed : EffectConfigurationTyped (withCellSignatures users) tickets before result outgoing) :
    EffectConfigurationTyped (withCellSignatures users) tickets after result outgoing := by
  cases step with
  | bind closed environment fresh => exact bind_preserves_effect_configuration typed closed.1
  | beta closed closure fresh => exact beta_preserves_effect_configuration typed closed.1
  | ifTrue => exact branch_preserves_effect_configuration (condition := true) typed
  | ifFalse => exact branch_preserves_effect_configuration (condition := false) typed
  | read cell => exact cell_read_preserves_effect_configuration typed cell
  | write cell => exact cell_write_preserves_effect_configuration typed cell

theorem ordinary_step_has_no_activation (step : OrdinaryStep before after) :
    enteredActivations before after = [] := by cases step <;> rfl

theorem ordinary_step_preserves_joint_configuration
    (step : OrdinaryStep before.execution.configuration after)
    (valid : Valid (withCellSignatures users) policy registry ambient before result outgoing)
    (checks : AccessChecks before.execution.configuration ambient) :
    NamedAccessStep ambient before (advanceState before after [] []) ∧
    Valid (withCellSignatures users) policy registry ambient (advanceState before after [] []) result outgoing := by
  have raw := ordinary_step_executes step
  have freshOwners : (before.execution.issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have noEntry : enteredActivations before.execution.configuration after = [] := ordinary_step_has_no_activation step
  have freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup := by
    simpa [noEntry] using valid.names.unique
  exact ⟨⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
    assemble_event raw freshOwners freshHandlers checks valid (ordinary_step_preserves_effects step valid.effects) rfl⟩

theorem focus_constructs_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨whole, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (focus : Focus whole child context)
    (checks : AccessChecks ⟨whole, scope, tail⟩ ambient) :
    ∃ plain : PlainData, plain.context = context ∧ plain.scope = scope ∧
      let initial : NamedState := ⟨⟨⟨whole, scope, tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨child, scope, .push (.plain plain) tail⟩
      NamedAccessStep ambient initial (advanceState initial after [] []) ∧
      Valid signature policy registry ambient (advanceState initial after [] []) result outgoing := by
  obtain ⟨plain, contextEq, scopeEq, raw, effects⟩ := focus_constructs_effect_configuration valid.effects focus
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have noEntry : enteredActivations ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩ = [] := by
    cases whole <;> rfl
  have freshHandlers : (activations ++ enteredActivations
      ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩).Nodup := by
    simpa [noEntry] using valid.names.unique
  exact ⟨plain, contextEq, scopeEq, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
    assemble_event raw freshOwners freshHandlers checks valid effects rfl⟩

private theorem value_has_no_activation (closed : ClosedValue before.expression) :
    enteredActivations before after = [] := by
  cases before with
  | mk expression scope stack => cases expression <;> first | rfl | cases closed.1

theorem value_event_preserves_joint_configuration
    (raw : RawStep before.execution.configuration after [] discharged)
    (closed : ClosedValue before.execution.configuration.expression)
    (valid : Valid signature policy registry ambient before result outgoing)
    (checks : AccessChecks before.execution.configuration ambient) :
    NamedAccessStep ambient before (advanceState before after [] discharged) ∧
    Valid signature policy registry ambient (advanceState before after [] discharged) result outgoing := by
  have freshOwners : (before.execution.issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup := by
    simpa [value_has_no_activation closed] using valid.names.unique
  have step : NamedAccessStep ambient before (advanceState before after [] discharged) :=
    ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩
  exact ⟨step, closed_value_preserves_joint_configuration step closed valid⟩

/-- Entry annotations are derived from the checked pre-expression. -/
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
    Syntax.UsageExecutionExamples.ordinary_access_checks (by simp [Expr.IsValue])
      (by intro requested operation operand same; cases same) (by intro binder same; cases same)
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      ⟨.handle effectInst body clauses, scope, tail⟩ ⟨body, scope, .push (.handler handler) tail⟩).Nodup := by
    simpa [enteredActivations, sameActivation] using fresh
  exact ⟨handler, sameActivation, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩,
    assemble_event raw freshOwners freshHandlers checks valid effects rfl⟩

theorem cell_entry_constructs_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.resource identity (.integer payload) body, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (fresh : (issued ++ [Owner.resource identity]).Nodup) :
    ∃ answer : Ty,
      let initial : NamedState := ⟨⟨⟨.resource identity (.integer payload) body, scope, tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.cell identity payload scope answer) tail⟩
      NamedAccessStep ambient initial (advanceState initial after [.resource identity] []) ∧
      Valid signature policy registry ambient (advanceState initial after [.resource identity] []) result outgoing := by
  obtain ⟨answer, raw, effects⟩ := cell_entry_constructs_effect_configuration valid.effects
  have checks : AccessChecks ⟨.resource identity (.integer payload) body, scope, tail⟩ ambient :=
    Syntax.UsageExecutionExamples.ordinary_access_checks (by simp [Expr.IsValue])
      (by intro requested operation operand same; cases same) (by intro binder same; cases same)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.resource identity (.integer payload) body, scope, tail⟩
      ⟨body, scope, .push (.cell identity payload scope answer) tail⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  exact ⟨answer, ⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩,
    assemble_event raw fresh freshHandlers checks valid effects rfl⟩

theorem cleanup_entry_constructs_joint_configuration
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.cleanup callback body, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : callback.IsValue) (fresh : (issued ++ [Owner.cleanup identity]).Nodup) :
    ∃ action : ActionData,
      let initial : NamedState := ⟨⟨⟨.cleanup callback body, scope, tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.armed action) tail⟩
      NamedAccessStep ambient initial (advanceState initial after [.cleanup identity] []) ∧
      Valid signature policy registry ambient (advanceState initial after [.cleanup identity] []) result outgoing := by
  obtain ⟨action, raw, effects⟩ := cleanup_entry_constructs_effect_configuration valid.effects isValue identity
  have checks : AccessChecks ⟨.cleanup callback body, scope, tail⟩ ambient :=
    Syntax.UsageExecutionExamples.ordinary_access_checks (by simp [Expr.IsValue])
      (by intro requested operation operand same; cases same) (by intro binder same; cases same)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.cleanup callback body, scope, tail⟩ ⟨body, scope, .push (.armed action) tail⟩).Nodup := by
    simpa [enteredActivations] using valid.names.unique
  exact ⟨action, ⟨.event _ _ _ _ raw fresh freshHandlers, checks⟩,
    assemble_event raw fresh freshHandlers checks valid effects rfl⟩

namespace Examples
open Execution.Examples
open ControlUsageExamples (policy rights)
open Syntax.UsageExecutionExamples (ordinary_access_checks builtin_read_access_checks)

def disposalRecord : TicketRecord := ⟨⟨.unit, .unit, [], []⟩, rights⟩
def disposalRegistry : Registry := Registry.insert (fun _ => none) 3 disposalRecord

def disposalInitial : NamedState :=
  ⟨⟨⟨.discard 9, closeScope, .live 3 .unit .unit abandoned .none .nil⟩,
    [.resource 4, .cleanup 7, .ticket 3], []⟩, [10]⟩

theorem discard_handler_effects : EffectFrame RetainedExamples.userAndCells tickets
    (.handler discardHandler) [.user 1 []] [] := by
  apply EffectFrame.handler ⟨_, .none⟩
  · exact .cons rfl (.discard (fun _ used => used)) .nil
  · intro operation input output known
    simp only [RetainedExamples.userAndCells, withCellSignatures, discardHandler,
      Typing.Examples.unitRequestSignature] at known
    split at known
    · rename_i equal
      simp [discardHandler, clauseKeys, equal.2]
    · cases known
  · decide

theorem abandoned_cell_effects : EffectStack RetainedExamples.userAndCells tickets
    abandoned [.cell 4, .user 1 []] [] := by
  refine .push (.armed ⟨_, .none⟩ RetainedExamples.read_callback_retained_type ?_)
    (.push (.cell ⟨_, .none⟩ (by simp [Ty.resources]))
      (.push discard_handler_effects (.nil (fun _ used => used)) (fun _ used => used))
      (fun _ used => used)) (fun _ used => used)
  simp [readAction]

theorem disposal_initial_effects : EffectConfigurationTyped RetainedExamples.userAndCells
    disposalRegistry.effects disposalInitial.execution.configuration .unit [] := by
  refine ⟨.unit, [], .checked (.bound (binder := 9) (contract := disposalRecord.contract) rfl)
    (.discard (fun _ used => used)), ?_, ?_⟩
  · exact .live rfl ⟨_, .none⟩ RetainedExamples.abandoned_cell_stack_has_typed_code .nil
  · exact .live (contract := disposalRecord.contract) rfl ⟨_, .none⟩ abandoned_cell_effects (.nil (fun _ used => used))
      (fun _ used => used) (fun _ used => used) (fun _ used => used)

/-- All facets hold together for this resource-bearing administrative state. -/
theorem disposal_initial_valid :
    Valid RetainedExamples.userAndCells policy disposalRegistry [] disposalInitial .unit [] := by
  constructor
  · exact ⟨(List.reverse_perm [Owner.resource 4, .cleanup 7, .ticket 3]).symm, by decide⟩
  · constructor
    · intro ticket
      simp [disposalInitial, abandoned, readAction, discardHandler, Stack.erase, ExecFrame.erase,
        ActionData.erase, HandlerData.erase, Control.ticketNames, List.count_cons]
    · intro activation
      simp [disposalInitial, abandoned, readAction, discardHandler, Stack.erase, ExecFrame.erase,
        ActionData.erase, HandlerData.erase, Control.activations, Frame.activation]
    · decide
  · constructor
    · refine .live _ _ _ _ _ _ ?_ (.nil _)
      refine .push _ _ _ (.push _ _ _ (.push _ _ _ (.nil _) ?_) ?_) ?_
      · simp [discardHandler, ExecFrame.erase, HandlerData.erase, Clauses.dependencies,
          Expr.dependencies, Instance.resources, resourceDependencies, without]
      · simp [ExecFrame.erase]
      · simp [readAction, ActionData.erase, readCallback, readBody, Expr.dependencies,
          resourceDependencies, instanceDependencies, Instance.resources, without,
          Stack.erase, ExecFrame.erase, Control.visible, Frame.visible]
    · simp [disposalInitial, Expr.dependencies, resourceDependencies]
  · exact disposal_initial_effects
  · have same : disposalRegistry.usage = Syntax.UsageExecutionExamples.disposalTickets := by
      funext owner
      by_cases equal : owner = 3 <;>
        simp [disposalRegistry, Registry.usage, Registry.insert, disposalRecord,
          Syntax.UsageExecutionExamples.disposalTickets, UsageTickets.insert, equal]
    rw [same]
    exact Syntax.UsageExecutionExamples.cell_disposal_initial_usage
  · intro owner
    by_cases same : owner = 3 <;> simp [disposalInitial, disposalRegistry, Registry.insert, same]

def disposalFinal : NamedState :=
  ⟨⟨⟨.unit, .none, .nil⟩, [.resource 4, .cleanup 7, .ticket 3, .close 8],
    [.close 8, .resource 4, .cleanup 7, .ticket 3]⟩, [10]⟩

/-- One actual execution and one registry carry the complete joint invariant
    through disposal, callback application, focus, cell read, and release. -/
theorem resource_disposal_joint_execution :
    NamedAccessSteps [] disposalInitial disposalFinal ∧
    Valid RetainedExamples.userAndCells policy disposalRegistry [] disposalFinal .unit [] := by
  obtain ⟨s0, v0⟩ := discard_preserves_joint_configuration (front := .nil)
    (contract := disposalRecord.contract) disposal_initial_valid rfl rfl
    (plan := closePlan) rfl
    (.invoke RetainedExamples.read_callback_retained_type
      (by simp [readAction, planProvides]) (.release .nil))
    (closeId := 8) (by decide) Syntax.UsageExecutionExamples.cell_disposal_access_checks
  obtain ⟨s1, v1⟩ := value_event_preserves_joint_configuration
    (RawStep.startCleanup closingAction .unit closed_unit closeScope closeCellTail) closed_unit v0
    (resource_free_access_checks rfl (by intro binder same; cases same))
  have beta : OrdinaryStep ⟨.app readCallback .unit, .none, runningClose⟩
      ⟨readBody.subst 2 .unit, .none, runningClose⟩ :=
    .beta closed_unit read_callback_closed (by simp [ResourceFresh, Expr.dependencies])
  obtain ⟨s2, v2⟩ := ordinary_step_preserves_joint_configuration beta v1
    (ordinary_access_checks (by simp [Expr.IsValue])
      (by intro requested operation operand same; cases same) (by intro binder same; cases same))
  obtain ⟨plain, contextEq, scopeEq, s3, v3⟩ := focus_constructs_joint_configuration v2
    (Focus.bind (initializer := .perform (.cell 4) 0 (.resourceRef 4)) (by simp [Expr.IsValue]))
    (ordinary_access_checks (by simp [Expr.IsValue, readBody, Expr.subst])
      (by intro requested operation operand same; cases same) (by intro binder same; cases same))
  have cell : CellUpdate 4 17 17 (.push (.plain plain) runningClose) (.push (.plain plain) runningClose) :=
    .push (by simp [ExecFrame.erase, PlainData.erase, Frame.target])
      (.push (by simp [ExecFrame.erase, Frame.target]) .hit)
  obtain ⟨s4, v4⟩ := ordinary_step_preserves_joint_configuration (.read cell) v3 (builtin_read_access_checks cell)
  obtain ⟨s5, v5⟩ := value_event_preserves_joint_configuration
    (RawStep.plug plain (.integer 17) (closed_integer 17) .none runningClose) (closed_integer 17) v4
    (resource_free_access_checks rfl (by intro binder same; cases same))
  simp only [advanceState, contextEq, scopeEq, Context.plug, enteredActivations, List.append_nil] at s5 v5
  have binding : OrdinaryStep ⟨.bind 0 (.integer 17) .unit, .none, runningClose⟩ ⟨.unit, .none, runningClose⟩ :=
    .bind (closed_integer 17) (by simp [ClosedExcept, Expr.dependencies]) (by simp [ResourceFresh, Expr.dependencies])
  obtain ⟨s6, v6⟩ := ordinary_step_preserves_joint_configuration binding v5
    (resource_free_access_checks rfl (by intro binder same; cases same))
  obtain ⟨s7, v7⟩ := value_event_preserves_joint_configuration
    (RawStep.finishCleanup closingAction .unit closed_unit .none closeCellTail) closed_unit v6
    (resource_free_access_checks rfl (by intro binder same; cases same))
  obtain ⟨s8, v8⟩ := value_event_preserves_joint_configuration
    (RawStep.leaveCell 4 17 .unit closeScope closeScope .unit closed_unit closeTail) closed_unit v7
    (resource_free_access_checks rfl (by intro binder same; cases same))
  obtain ⟨s9, v9⟩ := value_event_preserves_joint_configuration
    (RawStep.finishClose 8 closeScope closeScope (.spent 3 .unit .none .nil)) closed_unit v8
    (resource_free_access_checks rfl (by intro binder same; cases same))
  obtain ⟨s10, v10⟩ := value_event_preserves_joint_configuration
    (RawStep.leaveClause 3 .unit .unit closed_unit closeScope .none .nil) closed_unit v9
    (resource_free_access_checks rfl (by intro binder same; cases same))
  exact ⟨.next s0 (.next s1 (.next s2 (.next s3 (.next s4 (.next s5 (.next s6
    (.next s7 (.next s8 (.next s9 (.next s10 (.refl _))))))))))), v10⟩

def resumeOnlyRegistry : Registry := Registry.insert (fun _ => none) 3
  ⟨disposalRecord.contract, ⟨true, false⟩⟩

theorem resume_only_keeps_effect_contract : resumeOnlyRegistry.effects = disposalRegistry.effects := by
  funext owner
  by_cases same : owner = 3 <;>
    simp [resumeOnlyRegistry, disposalRegistry, Registry.effects, Registry.insert, same]

theorem disposal_effects_do_not_confer_permission :
    EffectConfigurationTyped RetainedExamples.userAndCells resumeOnlyRegistry.effects
      disposalInitial.execution.configuration .unit [] ∧
    ¬ Valid RetainedExamples.userAndCells policy resumeOnlyRegistry [] disposalInitial .unit [] := by
  constructor
  · rw [resume_only_keeps_effect_contract]
    exact disposal_initial_effects
  · intro valid
    obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := valid.usage
    change CodeDemand policy resumeOnlyRegistry.usage (.ticket 9 3) (.discard 9) currentDemand at code
    cases code with
    | idle scope checked => cases checked
    | consume known checked =>
        simp [resumeOnlyRegistry, Registry.usage, Registry.insert] at known
        cases known
        cases checked with
        | discard allowed => cases allowed

/-- A complete resource execution starts from expression checking and empty
    histories, rather than assuming a pre-existing administrative capture. -/
theorem source_cell_scope_joint_execution :
    let initial : NamedState := ⟨⟨⟨.resource 4 (.integer 0) .unit, .none, .nil⟩, [], []⟩, []⟩
    let final : NamedState := ⟨⟨⟨.unit, .none, .nil⟩, [.resource 4], [.resource 4]⟩, []⟩
    NamedAccessSteps [] initial final ∧
      Valid RetainedExamples.userAndCells policy (fun _ => none) [] final .unit [] := by
  have initial := initial_configuration_valid (signature := RetainedExamples.userAndCells) (policy := policy)
    (expression := .resource 4 (.integer 0) .unit)
    (Typed.resource (identity := 4) (allowed := []) .integer .unit
      (by simp [Ty.resources]) (by simp) (fun _ used => used))
    (Uses.resource .integer .unit) (by simp [Expr.dependencies, resourceDependencies, without])
  obtain ⟨answer, enter, inside⟩ := cell_entry_constructs_joint_configuration initial (by decide)
  obtain ⟨leave, final⟩ := value_event_preserves_joint_configuration
    (RawStep.leaveCell 4 0 answer .none .none .unit closed_unit .nil) closed_unit inside
    (resource_free_access_checks rfl (by intro binder same; cases same))
  exact ⟨.next enter (.next leave (.refl _)), final⟩

end Examples

end Ash.OneShot.Joint

#print axioms Ash.OneShot.Joint.capture_constructs_joint_configuration
#print axioms Ash.OneShot.Joint.resume_preserves_joint_configuration
#print axioms Ash.OneShot.Joint.discard_preserves_joint_configuration
#print axioms Ash.OneShot.Joint.closed_value_preserves_joint_configuration

#print axioms Ash.OneShot.Joint.ordinary_step_preserves_joint_configuration
#print axioms Ash.OneShot.Joint.focus_constructs_joint_configuration

#print axioms Ash.OneShot.Joint.Examples.disposal_initial_valid

#print axioms Ash.OneShot.Joint.Examples.resource_disposal_joint_execution

#print axioms Ash.OneShot.Joint.Examples.disposal_effects_do_not_confer_permission
#print axioms Ash.OneShot.Joint.handler_entry_constructs_joint_configuration
#print axioms Ash.OneShot.Joint.cell_entry_constructs_joint_configuration
#print axioms Ash.OneShot.Joint.cleanup_entry_constructs_joint_configuration

#print axioms Ash.OneShot.Joint.initial_configuration_valid
#print axioms Ash.OneShot.Joint.Examples.source_cell_scope_joint_execution
