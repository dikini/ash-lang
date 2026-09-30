import CallableFrames

/-!
One historical record joins full callable contracts to the independent
port/effect, usage, ownership and name-history invariant on the same machine.
Local preservation is not yet full initial-term execution coverage.
-/

namespace Ash.OneShot.CallableJoint
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ScopedTyping (resourceWorld resource_world_append)
open DeclarationResults (signature)

structure TicketRecord where
  joint : ScopedPortJoint.TicketRecord
  results : CallableFrames.ResultRecord
  inputBound : ∃ bound, results.input = .storage bound ∧ ClauseResults.PortBound joint.contract.input bound

abbrev Registry := Nat → Option TicketRecord

def Registry.joint (registry : Registry) : ScopedPortJoint.Registry :=
  fun owner => (registry owner).map TicketRecord.joint

def Registry.results (registry : Registry) : CallableFrames.Registry :=
  fun owner => (registry owner).map TicketRecord.results

def Registry.insert (registry : Registry) (owner : Nat) (record : TicketRecord) : Registry :=
  fun candidate => if candidate = owner then some record else registry candidate

@[simp] theorem joint_insert (registry : Registry) :
    (registry.insert owner record).joint = registry.joint.insert owner record.joint := by
  funext candidate
  by_cases same : candidate = owner <;> simp [Registry.joint, Registry.insert, ScopedPortJoint.Registry.insert, same]

@[simp] theorem results_insert (registry : Registry) :
    (registry.insert owner record).results = CallableFrames.insert registry.results owner record.results := by
  funext candidate
  by_cases same : candidate = owner <;> simp [Registry.results, Registry.insert, CallableFrames.insert, same]

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
    (ambient : List Nat) (state : NamedState) (result : Port) (outgoing : List Instance) (bound : CallableContracts.Contract) : Prop where
  joint : ScopedPortJoint.Valid (signature declarations) policy registry.joint ambient state result outgoing
  results : CallableFrames.ConfigurationReturns declarations registry.results (resourceWorld state.execution.issued)
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
    (checked : CallableContracts.Derives declarations environment [] .none expression bound) :
    Valid declarations policy (fun _ => none) []
      ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ result outgoing bound :=
  ⟨ScopedPortJoint.initial_configuration_valid typed used support,
    environment, .none, bound, .none, checked, .nil⟩

theorem active_input_contract
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨expression, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing contract) :
    ∃ record bound, registry owner = some record ∧
      record.joint.contract.input = eraseType input ∧ record.results.input = .storage bound ∧
      ClauseResults.PortBound (eraseType input) bound := by
  obtain ⟨actual, known, inputEq, answerEq⟩ := ScopedPortJoint.active_live_contract valid.joint.effects
  cases found : registry owner with
  | none => simp [ScopedPortJoint.Registry.effects, Registry.joint, found] at known
  | some record =>
      simp only [ScopedPortJoint.Registry.effects, Registry.joint, found, Option.map_some] at known
      cases Option.some.inj known
      obtain ⟨bound, same, finite⟩ := record.inputBound
      exact ⟨record, bound, rfl, inputEq, same, inputEq ▸ finite⟩

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
  have results := (CallableFrames.resume_step resolved valid.results closed).2
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
          obtain ⟨raw, resultRecord, inputBound, inputSame, outputFinite, resultExtended, resultAfter⟩ :=
            CallableFrames.capture_step cut selected beforeTyped operationType isValue valid.results resultFresh
          let contract : ContinuationContract := ⟨output, eraseType handler.answer, residual, residual⟩
          let record : TicketRecord := ⟨⟨contract, policy binder⟩, resultRecord, inputBound, inputSame, outputFinite⟩
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


theorem current_payload_access
    (valid : CallableJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue) :
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient := by
  obtain ⟨inputPort, current, stackTyped⟩ := effect_configuration_has_types valid.joint.effects
  obtain ⟨environment, ticket, inputBound, scopeChecked, code, stack⟩ := valid.results
  obtain ⟨savedEnvironment, savedTicket, answer, handlerScope, clauses, saved, outside⟩ :=
    CallableFrames.handler_cut_certificate cut stack
  cases current with
  | checked scopeTyped current =>
      obtain ⟨argumentPort, declared, available, operandTyped⟩ := typed_perform_inversion current
      obtain ⟨savedTyped, outsideTyped, handlerTyped⟩ := handler_cut_retains_typing cut stackTyped
      cases handlerTyped with
      | handler caller clausesTyped coverage unique =>
          have atHandler := declared
          rw [← ScopedTyping.handler_cut_instance cut] at atHandler
          obtain ⟨parameter, binder, body, selected⟩ := ScopedTyping.clause_at_of_key (coverage _ _ _ atHandler)
          obtain ⟨actualInput, actualOutput, argumentBound, resumeBound, known, inputFinite, outputFinite, bodyChecked⟩ :=
            CallableFrames.selected_clause selected clauses
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans atHandler))
          exact PayloadBoundary.payload_crosses_selected_handler cut valid.joint.support.control declared operandTyped isValue inputFinite

/-- Every actual source-handler cut receives the check derived from its own
    retained clauses and outside support. Non-value operands impose no current
    capture event; their evaluation remains governed by the ordinary machine. -/
theorem request_access_checks
    (valid : CallableJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      result outgoing bound) :
    AccessChecks ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ ambient := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    have impossible := congrArg Configuration.expression same
    dsimp only at impossible
    rw [← impossible] at closed
    cases closed.1
  · intro requested' operation' operand' scope' whole' cap tail handler same cut closed
    rw [same] at valid
    exact current_payload_access valid cut closed.1
  · intro binder ticket scope caller input answer front cap tail plan same resolved built
    cases congrArg Configuration.expression same

theorem capture_without_payload_premise
    (cut : HandlerCut requested whole capture tail handler)
    (valid : CallableJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (isValue : operand.IsValue)
    (fresh : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (parameter binder : Nat) (body : Code) (output : Port) (residual : List Instance)
      (record : CallableJoint.TicketRecord),
      record.joint = ⟨⟨output, eraseType handler.answer, residual, residual⟩, policy binder⟩ ∧
      ClauseAt operation handler.clauses parameter binder body ∧
      (∃ input, signature declarations requested operation = some (input, output)) ∧
      CallableJoint.RegistryExtends registry (registry.insert owner record) ∧
      let before : NamedState := ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer capture handler.scope tail⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) ∧
      CallableJoint.Valid declarations policy (registry.insert owner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket owner] []) result outgoing bound :=
  CallableJoint.capture_preserves cut valid isValue fresh (request_access_checks valid)

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
  obtain ⟨raw, results⟩ := CallableFrames.handler_return_step valid.results (current_closed_value valid isValue)
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
  obtain ⟨raw, results⟩ := CallableFrames.clause_return_step valid.results (current_closed_value valid isValue)
  have checks := value_access_checks (stack := .spent owner answer caller tail) (scope := scope) (ambient := ambient)
    isValue (by intro identity payload caller answer rest same; cases same)
  obtain ⟨step, joint⟩ := ScopedPortJoint.checked_value_event_constructs_joint_step raw isValue valid.joint checks
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩


theorem beta_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.app (.lambda parameter body) argument, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing contract)
    (isValue : argument.IsValue) :
    let before : NamedState := ⟨⟨⟨.app (.lambda parameter body) argument, scope, tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨body.subst parameter argument, .none, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] []) ∧
      Valid declarations policy registry ambient (ScopedPortJoint.advanceState before after [] []) result outgoing contract := by
  obtain ⟨currentPort, current, ports⟩ := effect_configuration_has_types valid.joint.effects
  cases current with
  | checked scopeTyped typed => cases typed with
      | app functionTyped argumentTyped available =>
          have argumentClosed := typed_value_closed argumentTyped isValue
          have functionClosed := typed_value_closed functionTyped (by trivial)
          obtain ⟨step, joint⟩ := ScopedPortJoint.ordinary_step_preserves_joint_configuration
            (.beta argumentClosed functionClosed) valid.joint
          exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using
            (CallableFrames.beta_step valid.results argumentClosed functionClosed).2⟩

theorem bind_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.bind parameter value body, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing contract)
    (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨.bind parameter value body, scope, tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨body.subst parameter value, scope, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] []) ∧
      Valid declarations policy registry ambient (ScopedPortJoint.advanceState before after [] []) result outgoing contract := by
  obtain ⟨currentPort, current, ports⟩ := effect_configuration_has_types valid.joint.effects
  cases current with
  | checked scopeTyped typed => cases typed with
      | bind initializer bodyTyped =>
          have closed := typed_value_closed initializer isValue
          have ready := typed_suffix_ready bodyTyped
          obtain ⟨step, joint⟩ := ScopedPortJoint.ordinary_step_preserves_joint_configuration (.bind closed ready) valid.joint
          exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using (CallableFrames.bind_step valid.results closed ready).2⟩

theorem plug_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, .push (.plain plain) tail⟩, issued, completed⟩, activations⟩ result outgoing contract)
    (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨value, scope, .push (.plain plain) tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨plain.context.plug value, plain.scope, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] []) ∧
      Valid declarations policy registry ambient (ScopedPortJoint.advanceState before after [] []) result outgoing contract := by
  obtain ⟨raw, results⟩ := CallableFrames.plug_step valid.results (current_closed_value valid isValue)
  have checks := value_access_checks (stack := .push (.plain plain) tail) (scope := scope) (ambient := ambient)
    isValue (by intro identity payload caller answer rest same; cases same)
  obtain ⟨step, joint⟩ := ScopedPortJoint.checked_value_event_constructs_joint_step raw isValue valid.joint checks
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩

theorem cell_return_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, .push (.cell identity payload caller answer) tail⟩, issued, completed⟩, activations⟩ result outgoing contract)
    (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨value, scope, .push (.cell identity payload caller answer) tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, caller, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.resource identity]) ∧
      Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [] [.resource identity]) result outgoing contract := by
  obtain ⟨raw, absent, results⟩ := CallableFrames.cell_return_step valid.results (current_closed_value valid isValue)
  have checks : AccessChecks ⟨value, scope, .push (.cell identity payload caller answer) tail⟩ ambient := by
    constructor
    · intro identity' payload' answer' saved' scope' value' tail' same valueClosed
      cases same
      exact absent
    · intro requested operation operand scope' whole cap tail' handler same cut valueClosed
      cases same
      cases isValue
    · intro binder ticket scope' caller input answer' front cap tail' plan same resolve built
      have expression := congrArg Configuration.expression same
      change value = .discard binder at expression
      rw [expression] at isValue
      cases isValue
  obtain ⟨step, joint⟩ := ScopedPortJoint.checked_value_event_constructs_joint_step raw isValue valid.joint checks
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩

theorem entry_access_checks
    (entry : EntryAnnotations.EntryTyping ports tickets world result outgoing before after created) :
    AccessChecks before ambient := by
  cases entry with
  | focus position => exact ScopedPortJoint.focus_access_checks position
  | handler | resource =>
      exact ScopedJoint.ordinary_access_checks (by simp [Code.IsValue])
        (by intro requested operation operand same; cases same) (by intro binder same; cases same)

theorem entry_results
    (entry : EntryAnnotations.EntryTyping ports tickets (resourceWorld issued) result outgoing before after created)
    (checked : CallableFrames.ConfigurationReturns declarations registry (resourceWorld issued) before contract)
    (fresh : (issued ++ created).Nodup) :
    CallableFrames.ConfigurationReturns declarations registry (resourceWorld (issued ++ created)) after contract := by
  cases entry with
  | focus position => simpa using (CallableFrames.focus_step position checked).2
  | handler => simpa using (CallableFrames.handler_entry_step checked).2
  | @resource scope binder payload body answer effects tail identity current tailTyped tailEffects =>
      have unused : identity ∉ resourceWorld issued := by
        intro member
        exact (List.nodup_append.mp fresh).2.2 (.resource identity)
          (ScopedTyping.mem_resource_world.mp member) (.resource identity) (by simp) rfl
      simpa [resource_world_append, resourceWorld] using (CallableFrames.resource_step checked unused).2

theorem entry_preserves
    (entry : EntryAnnotations.EntryTyping (signature declarations) registry.joint.effects (resourceWorld before.execution.issued)
      result outgoing before.execution.configuration after created)
    (valid : Valid declarations policy registry ambient before result outgoing contract)
    (fresh : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup) :
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after created []) ∧
      Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after created []) result outgoing contract := by
  have raw := EntryAnnotations.entry_executes entry
  have checks := entry_access_checks (ambient := ambient) entry
  have step : NamedAccessStep ambient before (ScopedPortJoint.advanceState before after created []) :=
    ⟨.event before after created [] raw fresh freshHandlers, checks⟩
  obtain ⟨ledger, names, support⟩ := named_access_step_preserves step valid.joint.ledger valid.joint.names valid.joint.support
  have history := ScopedPortJoint.usage_history_iff.mpr valid.joint.registry
  have usage := raw_step_preserves_configuration_usage raw
    (usage_checks_from_allocation_and_access history fresh checks) valid.joint.usage
  have nextHistory := raw_step_preserves_usage_registry_history (policy := policy) raw history
  rw [EntryAnnotations.entry_registry_unchanged entry] at usage nextHistory
  exact ⟨step, ⟨ledger, names, support, EntryAnnotations.entry_effects entry fresh, usage,
      ScopedPortJoint.usage_history_iff.mp nextHistory, raw_step_preserves_resource_closure raw valid.joint.closed⟩,
    entry_results entry valid.results fresh⟩

theorem focus_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨whole, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing contract)
    (focus : Focus whole child context) :
    ∃ plain : PlainData, plain.context = context ∧ plain.scope = scope ∧
      let before : NamedState := ⟨⟨⟨whole, scope, tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨child, scope, .push (.plain plain) tail⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] []) ∧
      Valid declarations policy registry ambient (ScopedPortJoint.advanceState before after [] []) result outgoing contract := by
  obtain ⟨plain, shape, savedScope, entry⟩ := EntryAnnotations.focus_annotations_exist valid.joint.effects focus
  have fresh : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.joint.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩).Nodup := by
    simpa [focus_enters_no_activation focus] using valid.joint.names.unique
  obtain ⟨step, checked⟩ := entry_preserves entry valid fresh freshHandlers
  exact ⟨plain, shape, savedScope, step, checked⟩

namespace Examples
open CallableContracts.Examples (declarations scalar identity identityContract applyTo17 higherOrder)

def policy : TicketPolicy := fun _ => ⟨true, false⟩
def initial : NamedState := ⟨⟨⟨higherOrder, .none, .nil⟩, [], []⟩, []⟩
def middle : NamedState := ⟨⟨⟨.app identity (.integer 17), .none, .nil⟩, [], []⟩, []⟩
def final : NamedState := ⟨⟨⟨.integer 17, .none, .nil⟩, [], []⟩, []⟩

theorem higher_order_typed : Typed (signature declarations) [] TypeEnv.empty .none [] higherOrder .integer :=
  .app (.lambda (.app (.variable rfl (List.nil_subset _)) .integer (List.nil_subset _)) (List.nil_subset _))
    (.lambda (.variable rfl (List.nil_subset _)) (List.nil_subset _)) (List.nil_subset _)

theorem higher_order_usage : Uses policy .none .available higherOrder .available :=
  .app (.lambda (.app .variable .integer)) (.lambda .variable)

theorem higher_order_initial : Valid declarations policy (fun _ => none) [] initial .integer [] scalar := by
  apply initial_configuration_valid higher_order_typed higher_order_usage
    (checked := CallableContracts.Examples.higher_order_checked)
  rfl

theorem higher_order_executes : NamedAccessStep [] initial middle ∧
    Valid declarations policy (fun _ => none) [] middle .integer [] scalar ∧
    NamedAccessStep [] middle final ∧ Valid declarations policy (fun _ => none) [] final .integer [] scalar := by
  obtain ⟨first, midway⟩ := beta_preserves higher_order_initial (by trivial)
  change Valid declarations policy (fun _ => none) [] middle .integer [] scalar at midway
  obtain ⟨second, finished⟩ := beta_preserves midway (by trivial)
  exact ⟨first, midway, second, finished⟩

end Examples

theorem execution_append (first : NamedAccessSteps ambient before middle)
    (second : NamedAccessSteps ambient middle after) : NamedAccessSteps ambient before after := by
  induction first with
  | refl => exact second
  | next step rest ih => exact .next step (ih second)

namespace CaptureExample
open CallableFrames.Examples (functionType clauseBody clauses handler pendingFunction outsideCall clauseBinding captured outside spent clauseFront
  s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
open CallableContracts.Examples (identity identityContract scalar)
open GenerativeFrames.Examples (declarations)
open ContinuationBounds.Examples (family)

def policy : TicketPolicy := fun _ => ActionRequirements.resumeOnly
def handled : Code := .handle (freezeEffect family) (.bind 2 (.perform (freezeEffect family) 0 .unit) identity) clauses
def program : Code := .app handled (.integer 17)
def initial : NamedState := ⟨⟨⟨program, .none, .nil⟩, [], []⟩, []⟩
def beforeHandler : NamedState := ⟨⟨⟨handled, .none, outside⟩, [], []⟩, []⟩
def entered : NamedState := ⟨⟨⟨.bind 2 (.perform (freezeEffect family) 0 .unit) identity, .none,
  .push (.handler handler) outside⟩, [], []⟩, [12]⟩
def atRequest : NamedState := ⟨⟨s0, [], []⟩, [12]⟩
def liveState (code : Configuration) : NamedState := ⟨⟨code, [.ticket 5], []⟩, [12]⟩
def spentState (code : Configuration) : NamedState := ⟨⟨code, [.ticket 5], [.ticket 5]⟩, [12]⟩

theorem identity_typed (environment : TypeEnv) (ticket : Ticket) (allowed : List Instance) :
    Typed (signature declarations) [] environment ticket allowed identity (eraseType functionType) :=
  .lambda (.variable rfl (List.nil_subset _)) (List.nil_subset _)

theorem clauses_typed : ClausesTyped (signature declarations) [] TypeEnv.empty family (eraseType functionType) [] clauses :=
  .cons rfl (.bind (.resume .integer (List.nil_subset _) (List.nil_subset _)) (.variable rfl (List.nil_subset _))) .nil

theorem handled_typed : Typed (signature declarations) [] TypeEnv.empty .none [] handled (eraseType functionType) :=
  .handle (.bind (.perform rfl (by simp) .unit (List.nil_subset _)) (identity_typed _ _ _)) clauses_typed
    (ClauseResults.Examples.single_coverage _ _ _) (by decide) (List.nil_subset _)

theorem initial_valid : Valid declarations policy (fun _ => none) [] initial .integer [] scalar := by
  apply initial_configuration_valid
    (.app handled_typed .integer (List.nil_subset _))
    (.app (.handle (.bind (.perform .unit) (.lambda .variable))
      (.cons (.bind (.resume rfl .integer) .variable) .nil)) .integer)
    (show resourceDependencies program.dependencies = [] from rfl)
  exact .app (.handle (.bind (.perform (operandContract := scalar) (.leaf trivial rfl .nil) rfl rfl)
    (CallableFrames.Examples.identity_contract _ _)) CallableFrames.Examples.clauses_contract rfl) (.leaf trivial rfl .nil)

theorem source_enters_request : NamedAccessSteps [] initial atRequest ∧
    Valid declarations policy (fun _ => none) [] atRequest .integer [] scalar := by
  have first : EntryAnnotations.EntryTyping (signature declarations) (Registry.joint (fun _ => none)).effects [] .integer []
      initial.execution.configuration beforeHandler.execution.configuration [] :=
    .focus (plain := outsideCall) (.appFunction (by intro impossible; cases impossible)) .none handled_typed
      (.appFunction .integer (List.nil_subset _)) .nil (.nil (List.nil_subset _))
  obtain ⟨e0, c1⟩ := entry_preserves first initial_valid (by decide) (by decide)
  change Valid declarations policy (fun _ => none) [] beforeHandler .integer [] scalar at c1
  have outerFrame : EffectFrame (signature declarations) (Registry.joint (fun _ => none)).effects []
      (.plain outsideCall) [] [] := .plain .none (.appFunction .integer (List.nil_subset _))
  have outerTypes : StackTyped (signature declarations) (Registry.joint (fun _ => none)).effects.types [] outside
      (eraseType functionType) .integer := .push (effect_frame_has_types outerFrame) .nil
  have outerEffects : EffectStack (signature declarations) (Registry.joint (fun _ => none)).effects [] outside [] [] :=
    .push outerFrame (.nil (List.nil_subset _)) (List.Subset.refl _)
  have second : EntryAnnotations.EntryTyping (signature declarations) (Registry.joint (fun _ => none)).effects [] .integer []
      beforeHandler.execution.configuration entered.execution.configuration [] :=
    .handler (handler := handler) (.checked .none handled_typed) outerTypes outerEffects
  obtain ⟨e1, c2⟩ := entry_preserves second c1 (by decide) (by decide)
  change Valid declarations policy (fun _ => none) [] entered .integer [] scalar at c2
  have handlerFrame : EffectFrame (signature declarations) (Registry.joint (fun _ => none)).effects []
      (.handler handler) [family] [] :=
    .handler ⟨.none, .none⟩ clauses_typed (ClauseResults.Examples.single_coverage _ _ _) (by decide)
  have third : EntryAnnotations.EntryTyping (signature declarations) (Registry.joint (fun _ => none)).effects [] .integer []
      entered.execution.configuration atRequest.execution.configuration [] :=
    .focus (plain := pendingFunction) (.bind (by intro impossible; cases impossible)) .none (.perform rfl (by simp) .unit (List.nil_subset _))
      (.bind (identity_typed _ _ _)) (.push (effect_frame_has_types handlerFrame) outerTypes)
      (.push handlerFrame outerEffects (List.Subset.refl _))
  obtain ⟨e2, c3⟩ := entry_preserves third c2 (by decide) (by decide)
  exact ⟨.next e0 (.next e1 (.next e2 (.refl atRequest))), c3⟩

theorem capture_valid : ∃ registry, NamedAccessStep [] atRequest (liveState s1) ∧
    Valid declarations policy registry [] (liveState s1) .integer [] scalar := by
  obtain ⟨parameter, binder, body, output, residual, record, same, selected, known, extension, step, checked⟩ :=
    capture_without_payload_premise CallableFrames.Examples.selected_cut source_enters_request.2 trivial (owner := 5) (by decide)
  cases selected with
  | hit =>
      obtain ⟨input, known⟩ := known
      change some (Port.unit, Port.integer) = some (input, output) at known
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj known)
      refine ⟨Registry.insert (fun _ => none) 5 record, ?_, ?_⟩
      · simpa [atRequest, liveState, s0, s1, handler, clauses, clauseBody, Code.subst,
          ScopedPortJoint.advanceState, enteredActivations, embedPort] using step
      · simpa [atRequest, liveState, s0, s1, handler, clauses, clauseBody, Code.subst,
          ScopedPortJoint.advanceState, enteredActivations, embedPort] using checked
  | pass different => exact False.elim (different rfl)

theorem continue_captured_callable
    (valid : Valid declarations policy registry [] (liveState s1) .integer [] scalar) :
    NamedAccessSteps [] (liveState s1) (spentState s11) ∧
      Valid declarations policy registry [] (spentState s11) .integer [] scalar := by
  have position : Focus clauseBody (.resume 10 (.integer 17)) (.bind 4 (.variable 4)) :=
    .bind (by intro impossible; cases impossible)
  obtain ⟨plain, shape, savedScope, e1, c2⟩ := focus_preserves valid position
  obtain ⟨e2, c3⟩ := resume_preserves (front := .push (.plain plain) .nil) c2 rfl (by trivial)
  obtain ⟨e3, c4⟩ := plug_preserves c3 (by trivial)
  obtain ⟨e4, c5⟩ := bind_preserves c4 (by trivial)
  obtain ⟨e5, c6⟩ := handler_return_preserves c5 (by trivial)
  obtain ⟨e6, c7⟩ := plug_preserves c6 (by trivial)
  simp only [shape, Context.plug] at c7 e6
  obtain ⟨e7, c8⟩ := bind_preserves c7 (by trivial)
  obtain ⟨e8, c9⟩ := clause_return_preserves c8 (by trivial)
  obtain ⟨e9, c10⟩ := plug_preserves c9 (by trivial)
  obtain ⟨e10, c11⟩ := beta_preserves c10 (by trivial)
  exact ⟨.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.next e7 (.next e8
    (.next e9 (.next e10 (.refl _)))))))))), c11⟩

theorem callable_handler_execution : ∃ registry,
    NamedAccessSteps [] initial (spentState s11) ∧
      Valid declarations policy registry [] (spentState s11) .integer [] scalar := by
  obtain ⟨registry, captured, valid⟩ := capture_valid
  obtain ⟨rest, final⟩ := continue_captured_callable valid
  exact ⟨registry, execution_append source_enters_request.1 (.next captured rest), final⟩

end CaptureExample

end Ash.OneShot.CallableJoint

#print axioms Ash.OneShot.CallableJoint.joint_insert
#print axioms Ash.OneShot.CallableJoint.results_insert
#print axioms Ash.OneShot.CallableJoint.registry_extends_refl
#print axioms Ash.OneShot.CallableJoint.registry_extends_trans
#print axioms Ash.OneShot.CallableJoint.registry_insert_extends
#print axioms Ash.OneShot.CallableJoint.recorded_history
#print axioms Ash.OneShot.CallableJoint.registry_fresh
#print axioms Ash.OneShot.CallableJoint.result_registry_fresh
#print axioms Ash.OneShot.CallableJoint.initial_configuration_valid
#print axioms Ash.OneShot.CallableJoint.active_input_contract
#print axioms Ash.OneShot.CallableJoint.resume_access_checks
#print axioms Ash.OneShot.CallableJoint.resume_preserves
#print axioms Ash.OneShot.CallableJoint.capture_preserves
#print axioms Ash.OneShot.CallableJoint.current_payload_access
#print axioms Ash.OneShot.CallableJoint.request_access_checks
#print axioms Ash.OneShot.CallableJoint.capture_without_payload_premise
#print axioms Ash.OneShot.CallableJoint.current_closed_value
#print axioms Ash.OneShot.CallableJoint.value_access_checks
#print axioms Ash.OneShot.CallableJoint.handler_return_preserves
#print axioms Ash.OneShot.CallableJoint.clause_return_preserves
#print axioms Ash.OneShot.CallableJoint.beta_preserves
#print axioms Ash.OneShot.CallableJoint.bind_preserves
#print axioms Ash.OneShot.CallableJoint.plug_preserves
#print axioms Ash.OneShot.CallableJoint.cell_return_preserves
#print axioms Ash.OneShot.CallableJoint.entry_access_checks
#print axioms Ash.OneShot.CallableJoint.entry_results
#print axioms Ash.OneShot.CallableJoint.entry_preserves
#print axioms Ash.OneShot.CallableJoint.focus_preserves
#print axioms Ash.OneShot.CallableJoint.Examples.higher_order_typed
#print axioms Ash.OneShot.CallableJoint.Examples.higher_order_usage
#print axioms Ash.OneShot.CallableJoint.Examples.higher_order_initial
#print axioms Ash.OneShot.CallableJoint.Examples.higher_order_executes
#print axioms Ash.OneShot.CallableJoint.execution_append
#print axioms Ash.OneShot.CallableJoint.CaptureExample.identity_typed
#print axioms Ash.OneShot.CallableJoint.CaptureExample.clauses_typed
#print axioms Ash.OneShot.CallableJoint.CaptureExample.handled_typed
#print axioms Ash.OneShot.CallableJoint.CaptureExample.initial_valid
#print axioms Ash.OneShot.CallableJoint.CaptureExample.source_enters_request
#print axioms Ash.OneShot.CallableJoint.CaptureExample.capture_valid
#print axioms Ash.OneShot.CallableJoint.CaptureExample.continue_captured_callable
#print axioms Ash.OneShot.CallableJoint.CaptureExample.callable_handler_execution
