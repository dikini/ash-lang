import ClauseFrames

/-!
One historical owner record with independent type/effect, usage and result
projections. Capture and resume preserve these components on the same named
execution. General payload admission and cleanup remain separate obligations.
-/

namespace Ash.OneShot.ClauseJoint
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ScopedTyping (resourceWorld resource_world_append)
open DeclarationResults (signature)

structure TicketRecord where
  joint : ScopedPortJoint.TicketRecord
  results : ClauseFrames.ResultRecord
  inputBound : ClauseResults.PortBound joint.contract.input results.input

abbrev Registry := Nat → Option TicketRecord

def Registry.joint (registry : Registry) : ScopedPortJoint.Registry :=
  fun owner => (registry owner).map TicketRecord.joint

def Registry.results (registry : Registry) : ClauseFrames.Registry :=
  fun owner => (registry owner).map TicketRecord.results

def Registry.insert (registry : Registry) (owner : Nat) (record : TicketRecord) : Registry :=
  fun candidate => if candidate = owner then some record else registry candidate

@[simp] theorem joint_insert (registry : Registry) :
    (registry.insert owner record).joint = registry.joint.insert owner record.joint := by
  funext candidate
  by_cases same : candidate = owner <;> simp [Registry.joint, Registry.insert, ScopedPortJoint.Registry.insert, same]

@[simp] theorem results_insert (registry : Registry) :
    (registry.insert owner record).results = ClauseFrames.insert registry.results owner record.results := by
  funext candidate
  by_cases same : candidate = owner <;> simp [Registry.results, Registry.insert, ClauseFrames.insert, same]

def RegistryExtends (before after : Registry) : Prop :=
  ∀ owner record, before owner = some record → after owner = some record

theorem registry_extends_refl (registry : Registry) : RegistryExtends registry registry := by
  intro owner record known
  exact known

theorem registry_extends_trans (first : RegistryExtends a b) (second : RegistryExtends b c) :
    RegistryExtends a c := by
  intro owner record known
  exact second owner record (first owner record known)

theorem registry_insert_extends (fresh : registry owner = none) :
    RegistryExtends registry (registry.insert owner record) := by
  intro candidate previous known
  by_cases same : candidate = owner
  · subst candidate
    rw [fresh] at known
    contradiction
  · simp [Registry.insert, same, known]

structure Valid (declarations : DeclarationRegistry) (policy : TicketPolicy) (registry : Registry)
    (ambient : List Nat) (state : NamedState) (result : Port) (outgoing : List Instance) (bound : List Nat) : Prop where
  joint : ScopedPortJoint.Valid (signature declarations) policy registry.joint ambient state result outgoing
  results : ClauseFrames.ConfigurationReturns declarations registry.results (resourceWorld state.execution.issued)
    state.execution.configuration bound

variable {front capture tail : Stack} {issued completed : List Owner}

theorem recorded_history (valid : Valid declarations policy registry ambient state result outgoing bound) :
    (∀ owner, (∃ record, registry owner = some record) ↔ .ticket owner ∈ state.execution.issued) ∧
    (∀ owner, (∃ record, registry.results owner = some record) ↔ .ticket owner ∈ state.execution.issued) := by
  constructor <;> intro owner <;> cases found : registry owner <;>
    simpa [Registry.joint, Registry.results, found] using valid.joint.registry owner

theorem registry_fresh (valid : Valid declarations policy registry ambient state result outgoing bound)
    (fresh : (state.execution.issued ++ [Owner.ticket owner]).Nodup) : registry owner = none := by
  have absent := ScopedPortJoint.registry_fresh valid.joint.registry fresh
  cases found : registry owner <;> simp_all [Registry.joint]

theorem result_registry_fresh (valid : Valid declarations policy registry ambient state result outgoing bound)
    (fresh : (state.execution.issued ++ [Owner.ticket owner]).Nodup) : registry.results owner = none := by
  have absent := ScopedPortJoint.registry_fresh valid.joint.registry fresh
  cases found : registry owner <;> simp_all [Registry.joint, Registry.results]

theorem initial_configuration_valid
    (typed : Typed (signature declarations) [] TypeEnv.empty .none outgoing expression result)
    (used : Uses policy .none .available expression .available)
    (support : resourceDependencies expression.dependencies = [])
    (checked : ClauseResults.Derives declarations environment [] .none expression bound) :
    Valid declarations policy (fun _ => none) []
      ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ result outgoing bound :=
  ⟨ScopedPortJoint.initial_configuration_valid typed used support,
    environment, .none, bound, .none, checked, .nil (List.Subset.refl _)⟩

/-- The live frame's actual input annotation and finite result input refer to
    the same owner record. Answer support is not inferred from its value type. -/
theorem active_input_bound
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨expression, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound) :
    ∃ record, registry owner = some record ∧
      record.joint.contract.input = eraseType input ∧
      ClauseResults.PortBound (eraseType input) record.results.input := by
  obtain ⟨contract, known, inputEq, answerEq⟩ := ScopedPortJoint.active_live_contract valid.joint.effects
  cases found : registry owner with
  | none => simp [ScopedPortJoint.Registry.effects, Registry.joint, found] at known
  | some record =>
      simp only [ScopedPortJoint.Registry.effects, Registry.joint, found, Option.map_some] at known
      cases Option.some.inj known
      exact ⟨record, rfl, inputEq, inputEq ▸ record.inputBound⟩

theorem resume_access_checks : AccessChecks
    ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩ ambient := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    have impossible := congrArg Configuration.expression same
    dsimp only at impossible
    rw [← impossible] at closed
    cases closed.1
  · intro requested operation operand scope whole cap tail handler same cut closed
    cases congrArg Configuration.expression same
  · intro binder ticket scope caller input answer front cap tail plan same resolved built
    cases congrArg Configuration.expression same

theorem resume_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨.resume binder value, scope,
      front.append (.live owner input answer capture caller tail)⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.ticket owner]) ∧
    Valid declarations policy registry ambient
      (ScopedPortJoint.advanceState before after [] [.ticket owner]) result outgoing bound := by
  obtain ⟨closed, support⟩ := ContinuationBounds.resume_operand_bound
    (environment := fun _ => ResultSummaries.Summary.unknown) resolved
    (effect_configuration_has_types valid.joint.effects) isValue
  obtain ⟨step, joint⟩ := ScopedPortJoint.resume_preserves_joint_configuration
    valid.joint resolved closed resume_access_checks
  have results := (ClauseFrames.resume_step resolved valid.results closed).2
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩

/-- Capture uses one operation lookup, selected clause, owner and successor
    for all projections. General outward payload access is still required. -/
theorem capture_preserves
    (cut : HandlerCut requested whole capture tail handler)
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (isValue : operand.IsValue)
    (fresh : (issued ++ [Owner.ticket owner]).Nodup)
    (checks : AccessChecks ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ ambient) :
    ∃ (parameter binder : Nat) (body : Code) (output : Port) (residual : List Instance)
      (record : TicketRecord),
      record.joint = ⟨⟨output, eraseType handler.answer, residual, residual⟩, policy binder⟩ ∧
      ClauseAt operation handler.clauses parameter binder body ∧
      (∃ input, signature declarations requested operation = some (input, output)) ∧
      RegistryExtends registry (registry.insert owner record) ∧
      let before : NamedState := ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer capture handler.scope tail⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) ∧
      Valid declarations policy (registry.insert owner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket owner] []) result outgoing bound := by
  have resultFresh := result_registry_fresh valid fresh
  have jointFresh := ScopedPortJoint.registry_fresh valid.joint.registry fresh
  have effectFresh : registry.joint.effects owner = none := by
    simp [ScopedPortJoint.Registry.effects, jointFresh]
  have beforeTyped := effect_configuration_has_types valid.joint.effects
  obtain ⟨output, effects, expression, stack, effectStack⟩ := valid.joint.effects
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, operationType, available, operandTyped⟩ := typed_perform_inversion expression
      obtain ⟨residual, capturedEffects, outsideEffects, handlerEffects⟩ := handler_cut_effect_decomposition cut effectStack
      obtain ⟨capturedTypes, outsideTypes, handlerTypes⟩ := handler_cut_retains_typing cut stack
      cases handlerEffects with
      | handler caller clauses coverage unique =>
          have operationAtHandler := operationType
          rw [← ScopedTyping.handler_cut_instance cut] at operationAtHandler
          obtain ⟨parameter, binder, body, selected⟩ := ScopedTyping.clause_at_of_key (coverage _ _ _ operationAtHandler)
          obtain ⟨raw, resultRecord, outputFinite, resultExtended, resultAfter⟩ :=
            ClauseFrames.capture_step cut selected beforeTyped operationType isValue valid.results resultFresh
          let contract : ContinuationContract := ⟨output, eraseType handler.answer, residual, residual⟩
          let record : TicketRecord := ⟨⟨contract, policy binder⟩, resultRecord, outputFinite⟩
          let extended := registry.insert owner record
          let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
            .live owner (embedPort output) handler.answer capture handler.scope tail⟩
          let before : NamedState := ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩
          have extension : EffectExtension registry.joint.effects extended.joint.effects := by
            simpa [extended, record] using effect_ticket_insertion_extends (contract := contract) effectFresh
          have newTicket : extended.joint.effects owner = some contract := by
            simp [extended, record, Registry.insert, Registry.joint, ScopedPortJoint.Registry.effects]
          have typeExtension := effect_extension_has_type_extension extension
          have newTypes : extended.joint.effects.types owner = some (output, eraseType handler.answer) := by
            simp [EffectTickets.types, newTicket, contract]
          have closed := typed_value_closed operandTyped isValue
          have afterEffects : EffectConfigurationTyped (signature declarations) extended.joint.effects
              (resourceWorld issued) after result outgoing := by
            refine ⟨eraseType handler.answer, residual, ?_, ?_, ?_⟩
            · exact .checked (.bound newTicket)
                (selected_clause_substitution_typed selected clauses operationAtHandler operandTyped closed)
            · exact .live (by simpa using newTypes) (effect_scope_known_has_types (effect_scope_known_extension caller extension))
                (by simpa using stack_typed_extension capturedTypes typeExtension) (stack_typed_extension outsideTypes typeExtension)
            · exact .live newTicket (effect_scope_known_extension caller extension)
                (effect_stack_extension capturedEffects extension) (effect_stack_extension outsideEffects extension)
                (fun _ used => used) (fun _ used => used) (fun _ used => used)
          have freshHandlers : (activations ++ enteredActivations before.execution.configuration after).Nodup := by
            simpa [before, after, enteredActivations] using valid.joint.names.unique
          have step : NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) :=
            ⟨.event before after [.ticket owner] [] raw fresh freshHandlers, checks⟩
          obtain ⟨ledger, names, support⟩ := named_access_step_preserves step
            valid.joint.ledger valid.joint.names valid.joint.support
          have history := ScopedPortJoint.usage_history_iff.mpr valid.joint.registry
          have usage := raw_step_preserves_configuration_usage raw
            (usage_checks_from_allocation_and_access history fresh checks) valid.joint.usage
          have nextHistory := raw_step_preserves_usage_registry_history (policy := policy) raw history
          have usageUpdate : extended.joint.usage = ScopedExecution.advanceUsageTickets policy registry.joint.usage after [.ticket owner] := by
            simp [extended, record, after, ScopedExecution.advanceUsageTickets]
          rw [← usageUpdate] at usage nextHistory
          refine ⟨parameter, binder, body, output, residual, record, rfl, selected, ⟨input, operationType⟩, registry_insert_extends (registry_fresh valid fresh), step, ?_⟩
          constructor
          · exact ⟨ledger, names, support, by
                simpa [ScopedPortJoint.advanceState, before, after, extended, resource_world_append, resourceWorld] using afterEffects,
              usage, ScopedPortJoint.usage_history_iff.mp nextHistory,
              raw_step_preserves_resource_closure raw valid.joint.closed⟩
          · simpa [ScopedPortJoint.advanceState, before, extended, record, resource_world_append, resourceWorld] using resultAfter

theorem empty_payload_access_checks
    (typed : ConfigurationTyped (signature declarations) tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result)
    (known : signature declarations requested operation = some (input, output))
    (emptyInput : ClauseResults.PortBound input []) (isValue : operand.IsValue) :
    AccessChecks ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ ambient := by
  obtain ⟨resultPort, current, stack⟩ := typed
  cases current with
  | checked scopeTyped current =>
      obtain ⟨actualInput, declared, available, operandTyped⟩ := typed_perform_inversion current
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans declared))
      have closed := typed_value_closed operandTyped isValue
      obtain ⟨retained, actual, included⟩ := OperationResults.typed_value_below_port
        (environment := fun _ => ResultSummaries.Summary.unknown) operandTyped isValue [] emptyInput
      rw [OperationResults.closed_value_storage_sound closed] at actual
      cases Option.some.inj actual
      constructor
      · intro identity payload answer savedScope current value tail same closed
        have impossible := congrArg Configuration.expression same
        dsimp only at impossible
        rw [← impossible] at closed
        cases closed.1
      · intro requested' operation' operand' scope' whole' cap tail handler same cut closed
        have sameOperand := (Code.perform.inj (congrArg Configuration.expression same)).2.2
        rw [← sameOperand]
        exact included.trans (List.nil_subset _)
      · intro binder ticket scope caller input answer front cap tail plan same resolved built
        cases congrArg Configuration.expression same

theorem named_raw_step (step : NamedAccessStep ambient before after) :
    ∃ created discharged, RawStep before.execution.configuration after.execution.configuration created discharged := by
  cases step.execution with
  | event after created discharged raw fresh freshHandlers => exact ⟨created, discharged, raw⟩

theorem handler_entry_results
    (raw : RawStep ⟨.handle effect body clauses, scope, tail⟩ after created discharged)
    (checked : ClauseFrames.ConfigurationReturns declarations registry world
      ⟨.handle effect body clauses, scope, tail⟩ bound) :
    ClauseFrames.ConfigurationReturns declarations registry world after bound := by
  cases raw with
  | focus plain focus => cases focus
  | enterHandler => exact (ClauseFrames.handler_entry_step checked).2
  | plug _ _ closed _ _ => cases closed.1
  | leaveHandler _ _ closed _ _ => cases closed.1
  | leaveCell _ _ _ _ _ _ closed _ => cases closed.1
  | startCleanup _ _ closed _ _ => cases closed.1
  | leaveClause _ _ _ closed _ _ _ => cases closed.1

theorem handler_entry_shape
    (raw : RawStep ⟨.handle effect body clauses, scope, tail⟩ after created discharged) :
    ∃ handler, after = ⟨body, scope, .push (.handler handler) tail⟩ ∧
      freezeEffect handler.effectInst = effect ∧ handler.clauses = clauses ∧ handler.scope = scope := by
  cases raw with
  | focus plain focus => cases focus
  | enterHandler handler => exact ⟨handler, rfl, rfl, rfl, rfl⟩
  | plug _ _ closed _ _ => cases closed.1
  | leaveHandler _ _ closed _ _ => cases closed.1
  | leaveCell _ _ _ _ _ _ closed _ => cases closed.1
  | startCleanup _ _ closed _ _ => cases closed.1
  | leaveClause _ _ _ closed _ _ _ => cases closed.1

theorem handler_entry_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.handle effect body clauses, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (fresh : (activations ++ [activation]).Nodup) :
    ∃ handler : HandlerData, handler.activation = activation ∧
      freezeEffect handler.effectInst = effect ∧ handler.clauses = clauses ∧ handler.scope = scope ∧
      let before : NamedState := ⟨⟨⟨.handle effect body clauses, scope, tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.handler handler) tail⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] []) ∧
      Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [] []) result outgoing bound := by
  obtain ⟨handler, same, step, joint⟩ := ScopedPortJoint.handler_entry_constructs_joint_configuration valid.joint fresh
  obtain ⟨created, discharged, raw⟩ := named_raw_step step
  obtain ⟨actualHandler, afterEq, effectEq, clausesEq, scopeEq⟩ := handler_entry_shape raw
  have sameHandler := ExecFrame.handler.inj (Stack.push.inj (congrArg Configuration.stack afterEq)).1
  cases sameHandler
  refine ⟨handler, same, effectEq, clausesEq, scopeEq, step, joint, ?_⟩
  simpa [ScopedPortJoint.advanceState] using handler_entry_results raw valid.results

theorem current_closed_value (valid : Valid declarations policy registry ambient state result outgoing bound)
    (isValue : state.execution.configuration.expression.IsValue) :
    ScopedExpressions.ClosedValue state.execution.configuration.expression := by
  obtain ⟨input, expression, stack⟩ := effect_configuration_has_types valid.joint.effects
  exact at_type_value_closed expression isValue

theorem value_access_checks
    (isValue : value.IsValue)
    (noCell : ∀ identity payload caller answer tail, stack ≠ .push (.cell identity payload caller answer) tail) :
    AccessChecks ⟨value, scope, stack⟩ ambient := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    exact False.elim (noCell _ _ _ _ _ (congrArg Configuration.stack same))
  · intro requested operation operand scope whole cap tail handler same cut closed
    have expressionEq := congrArg Configuration.expression same
    dsimp only at expressionEq
    rw [expressionEq] at isValue
    cases isValue
  · intro binder ticket scope caller input answer front cap tail plan same resolved built
    have expressionEq := congrArg Configuration.expression same
    dsimp only at expressionEq
    rw [expressionEq] at isValue
    cases isValue

theorem handler_return_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, .push (.handler handler) tail⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨value, scope, .push (.handler handler) tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, handler.scope, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] []) ∧
    Valid declarations policy registry ambient (ScopedPortJoint.advanceState before after [] []) result outgoing bound := by
  obtain ⟨raw, results⟩ := ClauseFrames.handler_return_step valid.results (current_closed_value valid isValue)
  have checks := value_access_checks (stack := .push (.handler handler) tail) (scope := scope) (ambient := ambient)
    isValue (by intro identity payload caller answer rest same; cases same)
  obtain ⟨step, joint⟩ := ScopedPortJoint.checked_value_event_constructs_joint_step raw isValue valid.joint checks
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩

theorem clause_return_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, .spent owner answer caller tail⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨value, scope, .spent owner answer caller tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, caller, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] []) ∧
    Valid declarations policy registry ambient (ScopedPortJoint.advanceState before after [] []) result outgoing bound := by
  obtain ⟨raw, results⟩ := ClauseFrames.clause_return_step valid.results (current_closed_value valid isValue)
  have checks := value_access_checks (stack := .spent owner answer caller tail) (scope := scope) (ambient := ambient)
    isValue (by intro identity payload caller answer rest same; cases same)
  obtain ⟨step, joint⟩ := ScopedPortJoint.checked_value_event_constructs_joint_step raw isValue valid.joint checks
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩

theorem cell_return_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, .push (.cell identity payload caller answer) tail⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨value, scope, .push (.cell identity payload caller answer) tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, caller, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.resource identity]) ∧
    Valid declarations policy registry ambient
      (ScopedPortJoint.advanceState before after [] [.resource identity]) result outgoing bound := by
  obtain ⟨raw, checks, results⟩ := ClauseFrames.cell_return_step (ambient := ambient) valid.results (current_closed_value valid isValue)
  obtain ⟨step, joint⟩ := ScopedPortJoint.checked_value_event_constructs_joint_step raw isValue valid.joint checks
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩

/-- A certificate over existing named access steps, with all three projected
    judgments at every state. This adds no execution transition. -/
inductive CertifiedSteps (declarations : DeclarationRegistry) (policy : TicketPolicy)
    (ambient : List Nat) (result : Port) (outgoing : List Instance) (bound : List Nat) :
    Registry → NamedState → Registry → NamedState → Prop where
  | refl (valid : Valid declarations policy registry ambient state result outgoing bound) :
      CertifiedSteps declarations policy ambient result outgoing bound registry state registry state
  | next (valid : Valid declarations policy registry ambient before result outgoing bound)
      (step : NamedAccessStep ambient before middle)
      (extended : RegistryExtends registry nextRegistry)
      (rest : CertifiedSteps declarations policy ambient result outgoing bound nextRegistry middle finalRegistry after) :
      CertifiedSteps declarations policy ambient result outgoing bound registry before finalRegistry after

theorem certified_execution
    (checked : CertifiedSteps declarations policy ambient result outgoing bound registry before finalRegistry after) :
    NamedAccessSteps ambient before after := by
  induction checked with
  | refl => exact .refl _
  | next valid step extended rest ih => exact .next step ih

theorem certified_final
    (checked : CertifiedSteps declarations policy ambient result outgoing bound registry before finalRegistry after) :
    Valid declarations policy finalRegistry ambient after result outgoing bound := by
  induction checked with
  | refl valid => exact valid
  | next valid step extended rest ih => exact ih

theorem certified_registry_extension
    (checked : CertifiedSteps declarations policy ambient result outgoing bound registry before finalRegistry after) :
    RegistryExtends registry finalRegistry := by
  induction checked with
  | refl => exact registry_extends_refl _
  | next valid step extended rest ih => exact registry_extends_trans extended ih

namespace Examples
open ClauseResults.Examples (innerHandler innerClauses inner_handler_checked inner_handler_typed single_coverage policy)
open GenerativeFrames.Examples (declarations environment)
open ContinuationBounds.Examples (family)

def initial : NamedState := ⟨⟨⟨innerHandler, .none, .nil⟩, [], []⟩, []⟩
def final : NamedState := ⟨⟨⟨.integer 17, .none, .nil⟩, [.ticket 5], [.ticket 5]⟩, [12]⟩
def emptyRegistry : Registry := fun _ => none

theorem initial_valid : Valid declarations policy emptyRegistry [] initial .integer [] [] :=
  initial_configuration_valid (environment := environment) (inner_handler_typed _ _ _ _)
    (.handle (.perform .unit) (.cons (.resume rfl .integer) .nil)) rfl (inner_handler_checked _ _ _)

/-- The five-step execution preserves the combined invariant at every state,
    including after the ticket is consumed and while its history remains. -/
theorem single_handler_execution : ∃ record,
    CertifiedSteps declarations policy [] .integer [] [] emptyRegistry initial (emptyRegistry.insert 5 record) final := by
  have v0 := initial_valid
  obtain ⟨handler, activationEq, effectEq, clausesEq, scopeEq, e0, v1⟩ :=
    handler_entry_preserves (activation := 12) v0 (by decide)
  have instanceEq := freeze_effect_injective effectEq
  let state1 : NamedState := ⟨⟨⟨.perform (freezeEffect family) 0 .unit, .none,
    .push (.handler handler) .nil⟩, [], []⟩, [12]⟩
  have v1 : Valid declarations policy emptyRegistry [] state1 .integer [] [] := by
    simpa [initial, innerHandler, ScopedPortJoint.advanceState, enteredActivations, activationEq] using v1
  have e0 : NamedAccessStep [] initial state1 := by
    simpa [initial, innerHandler, ScopedPortJoint.advanceState, enteredActivations, activationEq] using e0
  have checks : AccessChecks state1.execution.configuration [] :=
    empty_payload_access_checks (effect_configuration_has_types v1.joint.effects)
      (input := .unit) (output := .integer) rfl rfl trivial
  obtain ⟨parameter, binder, body, output, residual, record, recordEq, selected, ⟨input, known⟩, captureExtension, e1, v2⟩ :=
    capture_preserves (owner := 5) (.hit handler .nil instanceEq) v1 trivial (by decide) checks
  have declared : signature declarations family 0 = some (.unit, .integer) := rfl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans declared))
  rw [clausesEq] at selected
  cases selected with
  | pass different selected => exact False.elim (different rfl)
  | hit =>
      let state2 : NamedState := ⟨⟨⟨.resume 10 (.integer 17), .ticket 10 5,
        .live 5 .integer handler.answer (.push (.handler handler) .nil) handler.scope .nil⟩,
        [.ticket 5], []⟩, [12]⟩
      have v2 : Valid declarations policy (emptyRegistry.insert 5 record) [] state2 .integer [] [] := by
        simpa [state1, state2, ScopedPortJoint.advanceState, enteredActivations, innerClauses, Code.subst, embedPort] using v2
      have e1 : NamedAccessStep [] state1 state2 := by
        simpa [state1, state2, ScopedPortJoint.advanceState, enteredActivations, innerClauses, Code.subst, embedPort] using e1
      obtain ⟨e2, v3⟩ := resume_preserves (front := .nil) v2 rfl trivial
      obtain ⟨e3, v4⟩ := handler_return_preserves v3 trivial
      obtain ⟨e4, v5⟩ := clause_return_preserves v4 trivial
      have last : Valid declarations policy (emptyRegistry.insert 5 record) [] final .integer [] [] := by
        simpa [state2, final, ScopedPortJoint.advanceState, enteredActivations, Stack.append, scopeEq] using v5
      let state4 : NamedState := ⟨⟨⟨.integer 17, handler.scope, .spent 5 handler.answer handler.scope .nil⟩,
        [.ticket 5], [.ticket 5]⟩, [12]⟩
      have e4 : NamedAccessStep [] state4 final := by
        simpa [state2, state4, final, ScopedPortJoint.advanceState, enteredActivations, Stack.append, scopeEq] using e4
      exact ⟨record, .next v0 e0 (registry_extends_refl _) (.next v1 e1 captureExtension
        (.next v2 e2 (registry_extends_refl _) (.next v3 e3 (registry_extends_refl _)
          (.next v4 e4 (registry_extends_refl _) (.refl last)))))⟩

theorem single_handler_ledger : Ledger final.execution.erase := by
  obtain ⟨record, checked⟩ := single_handler_execution
  exact (certified_final checked).joint.ledger

theorem completed_record_remains : ∃ record,
    Valid declarations policy (emptyRegistry.insert 5 record) [] final .integer [] [] ∧
    (emptyRegistry.insert 5 record).results 5 = some record.results ∧
    ClauseResults.PortBound record.joint.contract.input record.results.input := by
  obtain ⟨record, checked⟩ := single_handler_execution
  exact ⟨record, certified_final checked, by simp [Registry.results, Registry.insert], record.inputBound⟩

theorem consumed_ticket_cannot_resume (record : TicketRecord) :
    ¬ Valid declarations policy (emptyRegistry.insert 5 record) []
      ⟨⟨⟨.resume 10 (.integer 17), .ticket 10 5, .nil⟩, [.ticket 5], [.ticket 5]⟩, [12]⟩ .integer [] [] := by
  intro valid
  obtain ⟨current, control, code, stack, available, balance, unique⟩ := valid.joint.usage
  have demand := ScopedExecution.resume_code_demand code (by rfl)
  rw [demand] at available
  exact List.not_mem_nil (available List.mem_cons_self)

theorem callable_input_is_not_silently_empty :
    ¬ ∃ record : TicketRecord, record.joint.contract.input = .function .unit .integer [] := by
  rintro ⟨record, same⟩
  have impossible := record.inputBound
  rw [same] at impossible
  cases impossible

end Examples

end Ash.OneShot.ClauseJoint

#print axioms Ash.OneShot.ClauseJoint.joint_insert
#print axioms Ash.OneShot.ClauseJoint.results_insert
#print axioms Ash.OneShot.ClauseJoint.recorded_history
#print axioms Ash.OneShot.ClauseJoint.result_registry_fresh
#print axioms Ash.OneShot.ClauseJoint.initial_configuration_valid
#print axioms Ash.OneShot.ClauseJoint.active_input_bound
#print axioms Ash.OneShot.ClauseJoint.resume_access_checks
#print axioms Ash.OneShot.ClauseJoint.resume_preserves
#print axioms Ash.OneShot.ClauseJoint.capture_preserves
#print axioms Ash.OneShot.ClauseJoint.empty_payload_access_checks
#print axioms Ash.OneShot.ClauseJoint.named_raw_step
#print axioms Ash.OneShot.ClauseJoint.handler_entry_results
#print axioms Ash.OneShot.ClauseJoint.handler_entry_shape
#print axioms Ash.OneShot.ClauseJoint.handler_entry_preserves
#print axioms Ash.OneShot.ClauseJoint.current_closed_value
#print axioms Ash.OneShot.ClauseJoint.value_access_checks
#print axioms Ash.OneShot.ClauseJoint.handler_return_preserves
#print axioms Ash.OneShot.ClauseJoint.clause_return_preserves
#print axioms Ash.OneShot.ClauseJoint.cell_return_preserves
#print axioms Ash.OneShot.ClauseJoint.certified_execution
#print axioms Ash.OneShot.ClauseJoint.certified_final
#print axioms Ash.OneShot.ClauseJoint.Examples.initial_valid
#print axioms Ash.OneShot.ClauseJoint.Examples.single_handler_execution
#print axioms Ash.OneShot.ClauseJoint.Examples.single_handler_ledger
#print axioms Ash.OneShot.ClauseJoint.Examples.completed_record_remains
#print axioms Ash.OneShot.ClauseJoint.Examples.consumed_ticket_cannot_resume
#print axioms Ash.OneShot.ClauseJoint.Examples.callable_input_is_not_silently_empty

#print axioms Ash.OneShot.ClauseJoint.registry_extends_refl
#print axioms Ash.OneShot.ClauseJoint.registry_extends_trans
#print axioms Ash.OneShot.ClauseJoint.registry_insert_extends
#print axioms Ash.OneShot.ClauseJoint.registry_fresh
#print axioms Ash.OneShot.ClauseJoint.certified_registry_extension
