import CompletionFrames

/-!
One historical record joins full callable contracts to the independent
port/effect, usage, ownership and name-history invariant on the same machine.
Local preservation is not yet full initial-term execution coverage.
-/

namespace Ash.OneShot.CompletionJoint
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ScopedTyping (resourceWorld resource_world_append)
open DeclarationResults (signature)

open CallableJoint (TicketRecord Registry RegistryExtends registry_extends_refl registry_extends_trans
  registry_insert_extends)

structure Valid (declarations : DeclarationRegistry) (policy : TicketPolicy) (registry : Registry)
    (ambient : List Nat) (state : NamedState) (result : Port) (outgoing : List Instance) (bound : CallableContracts.Contract) : Prop where
  joint : ScopedPortJoint.Valid (signature declarations) policy registry.joint ambient state result outgoing
  results : CompletionFrames.ConfigurationReturns declarations registry.results (resourceWorld state.execution.issued)
    state.execution.configuration bound

variable {front capture tail : Stack} {issued completed : List Owner}

theorem recorded_history (valid : Valid declarations policy registry ambient state result outgoing bound) :
    (∀ owner, (∃ record, registry owner = some record) ↔ .ticket owner ∈ state.execution.issued) ∧
    (∀ owner, (∃ record, registry.results owner = some record) ↔ .ticket owner ∈ state.execution.issued) := by
  constructor <;> intro owner <;> cases found : registry owner <;>
    simpa [CallableJoint.Registry.joint, CallableJoint.Registry.results, found] using valid.joint.registry owner

theorem registry_fresh (valid : Valid declarations policy registry ambient state result outgoing bound)
    (fresh : (state.execution.issued ++ [Owner.ticket owner]).Nodup) : registry owner = none := by
  have absent := ScopedPortJoint.registry_fresh valid.joint.registry fresh
  cases found : registry owner <;> simp_all [CallableJoint.Registry.joint]

theorem result_registry_fresh (valid : Valid declarations policy registry ambient state result outgoing bound)
    (fresh : (state.execution.issued ++ [Owner.ticket owner]).Nodup) : registry.results owner = none := by
  have absent := ScopedPortJoint.registry_fresh valid.joint.registry fresh
  cases found : registry owner <;> simp_all [CallableJoint.Registry.joint, CallableJoint.Registry.results]

theorem initial_configuration_valid
    (typed : Typed (signature declarations) [] TypeEnv.empty .none outgoing expression result)
    (used : Uses policy .none .available expression .available)
    (support : resourceDependencies expression.dependencies = [])
    (checked : CompletionContracts.Derives declarations environment [] .none expression bound) :
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
  | none => simp [ScopedPortJoint.Registry.effects, CallableJoint.Registry.joint, found] at known
  | some record =>
      simp only [ScopedPortJoint.Registry.effects, CallableJoint.Registry.joint, found, Option.map_some] at known
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
  have results := (CompletionFrames.resume_step resolved valid.results closed).2
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
            CompletionFrames.capture_step cut selected beforeTyped operationType isValue valid.results resultFresh
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
            simp [extended, record, CallableJoint.Registry.insert, CallableJoint.Registry.joint, ScopedPortJoint.Registry.effects]
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


/-- Payload support depends on port typing, retained result contracts and
outside resource support. It does not require a pending effect-stack annotation. -/
theorem payload_access_from_ports
    (typed : ConfigurationTyped (signature declarations) tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result)
    (returns : CompletionFrames.ConfigurationReturns declarations registry world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ bound)
    (support : Supported whole.erase ambient)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue) :
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient := by
  obtain ⟨inputPort, current, stackTyped⟩ := typed
  obtain ⟨environment, ticket, inputBound, scopeChecked, code, stack⟩ := returns
  obtain ⟨savedEnvironment, savedTicket, answer, handlerScope, clauses, saved, outside⟩ :=
    CompletionFrames.handler_cut_certificate cut stack
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
            CompletionFrames.selected_clause selected clauses
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans atHandler))
          exact PayloadBoundary.payload_crosses_selected_handler cut support declared operandTyped isValue inputFinite

theorem current_payload_access
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue) :
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient := by
  exact payload_access_from_ports (effect_configuration_has_types valid.joint.effects)
    valid.results valid.joint.support.control cut isValue

/-- Every actual source-handler cut receives the check derived from its own
    retained clauses and outside support. Non-value operands impose no current
    capture event; their evaluation remains governed by the ordinary machine. -/
theorem request_access_checks
    (valid : Valid declarations policy registry ambient
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
    (valid : Valid declarations policy registry ambient
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
      Valid declarations policy (registry.insert owner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket owner] []) result outgoing bound :=
  capture_preserves cut valid isValue fresh (request_access_checks valid)

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
  obtain ⟨raw, results⟩ := CompletionFrames.handler_return_step valid.results (current_closed_value valid isValue)
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
  obtain ⟨raw, results⟩ := CompletionFrames.clause_return_step valid.results (current_closed_value valid isValue)
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
            (CompletionFrames.beta_step valid.results argumentClosed functionClosed).2⟩

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
          exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using (CompletionFrames.bind_step valid.results closed ready).2⟩

theorem plug_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, .push (.plain plain) tail⟩, issued, completed⟩, activations⟩ result outgoing contract)
    (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨value, scope, .push (.plain plain) tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨plain.context.plug value, plain.scope, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] []) ∧
      Valid declarations policy registry ambient (ScopedPortJoint.advanceState before after [] []) result outgoing contract := by
  obtain ⟨raw, results⟩ := CompletionFrames.plug_step valid.results (current_closed_value valid isValue)
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
  obtain ⟨raw, absent, results⟩ := CompletionFrames.cell_return_step valid.results (current_closed_value valid isValue)
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
    (checked : CompletionFrames.ConfigurationReturns declarations registry (resourceWorld issued) before contract)
    (fresh : (issued ++ created).Nodup) :
    CompletionFrames.ConfigurationReturns declarations registry (resourceWorld (issued ++ created)) after contract := by
  cases entry with
  | focus position => simpa using (CompletionFrames.focus_step position checked).2
  | handler => simpa using (CompletionFrames.handler_entry_step checked).2
  | @resource scope binder payload body answer effects tail identity current tailTyped tailEffects =>
      have unused : identity ∉ resourceWorld issued := by
        intro member
        exact (List.nodup_append.mp fresh).2.2 (.resource identity)
          (ScopedTyping.mem_resource_world.mp member) (.resource identity) (by simp) rfl
      simpa [resource_world_append, resourceWorld] using (CompletionFrames.resource_step checked unused).2

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

theorem callable_valid_included
    (valid : CallableJoint.Valid declarations policy registry ambient state result outgoing contract) :
    Valid declarations policy registry ambient state result outgoing contract :=
  ⟨valid.joint, CompletionFrames.callable_configuration_included valid.results⟩

theorem cleanup_start_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, .push (.armed action) tail⟩, issued, completed⟩, activations⟩ result outgoing contract)
    (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨value, scope, .push (.armed action) tail⟩, issued, completed⟩, activations⟩
    ∃ closed : ClosedValue value,
      let after : Configuration := ⟨.app action.action .unit, .none, .push (.running action value closed) tail⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] []) ∧
      Valid declarations policy registry ambient (ScopedPortJoint.advanceState before after [] []) result outgoing contract := by
  have closed := current_closed_value valid isValue
  obtain ⟨raw, results⟩ := CompletionFrames.cleanup_start_step valid.results closed
  have checks := value_access_checks (stack := .push (.armed action) tail) (scope := scope) (ambient := ambient)
    isValue (by intro identity payload caller answer rest same; cases same)
  obtain ⟨step, joint⟩ := ScopedPortJoint.checked_value_event_constructs_joint_step raw isValue valid.joint checks
  exact ⟨closed, step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩

theorem cleanup_finish_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.unit, scope, .push (.running action value closed) tail⟩, issued, completed⟩, activations⟩ result outgoing contract) :
    let before : NamedState := ⟨⟨⟨.unit, scope, .push (.running action value closed) tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, action.scope, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.cleanup action.identity]) ∧
      Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [] [.cleanup action.identity]) result outgoing contract := by
  obtain ⟨raw, results⟩ := CompletionFrames.cleanup_finish_step valid.results
  have checks := value_access_checks (value := .unit) (stack := .push (.running action value closed) tail)
    (scope := scope) (ambient := ambient) trivial (by intro identity payload caller answer rest same; cases same)
  obtain ⟨step, joint⟩ := ScopedPortJoint.checked_value_event_constructs_joint_step raw (show Code.unit.IsValue from trivial) valid.joint checks
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩

theorem cleanup_entry_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.cleanup callback body, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing contract)
    (isValue : callback.IsValue) (fresh : (issued ++ [Owner.cleanup identity]).Nodup) :
    ∃ action : ActionData, action.identity = identity ∧ action.action = callback ∧ action.scope = scope ∧
      let before : NamedState := ⟨⟨⟨.cleanup callback body, scope, tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.armed action) tail⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.cleanup identity] []) ∧
      Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [.cleanup identity] []) result outgoing contract := by
  obtain ⟨answer, effects, current, ports, effectStack⟩ := valid.joint.effects
  cases current with
  | checked scopeTyped typed => cases typed with
      | @cleanup _ _ _ _ _ latent _ _ callbackTyped bodyTyped available =>
          have closed := typed_value_closed callbackTyped isValue
          let action : ActionData := ⟨identity, callback, closed, scope, embedPort answer, latent⟩
          let before : NamedState := ⟨⟨⟨.cleanup callback body, scope, tail⟩, issued, completed⟩, activations⟩
          let after : Configuration := ⟨body, scope, .push (.armed action) tail⟩
          have raw : RawStep before.execution.configuration after [.cleanup identity] [] := .enterCleanup action body tail
          have frame : EffectFrame (signature declarations) registry.joint.effects (resourceWorld issued)
              (.armed action) effects effects :=
            .armed ⟨_, scopeTyped⟩ (typed_value_transport callbackTyped isValue .none []) available
          have effectsAfter : EffectConfigurationTyped (signature declarations) registry.joint.effects
              (resourceWorld issued) after result outgoing :=
            ⟨answer, effects, .checked scopeTyped bodyTyped,
              (by simpa [action, after, ExecFrame.erase, ActionData.erase] using
                (StackTyped.push (effect_frame_has_types frame)
                  (by simpa [action, ExecFrame.erase, ActionData.erase] using ports))),
              .push frame effectStack (List.Subset.refl _)⟩
          have resultsAfter := (CompletionFrames.cleanup_entry_step (action := action) valid.results).2
          have checks : AccessChecks before.execution.configuration ambient :=
            ScopedJoint.ordinary_access_checks (by simp [Code.IsValue])
              (by intro requested operation operand same; cases same) (by intro binder same; cases same)
          have freshHandlers : (activations ++ enteredActivations before.execution.configuration after).Nodup := by
            simpa [before, after, enteredActivations] using valid.joint.names.unique
          have step : NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.cleanup identity] []) :=
            ⟨.event before after [.cleanup identity] [] raw fresh freshHandlers, checks⟩
          obtain ⟨ledger, names, support⟩ := named_access_step_preserves step valid.joint.ledger valid.joint.names valid.joint.support
          have history := ScopedPortJoint.usage_history_iff.mpr valid.joint.registry
          have usage := raw_step_preserves_configuration_usage raw
            (usage_checks_from_allocation_and_access history fresh checks) valid.joint.usage
          have nextHistory := raw_step_preserves_usage_registry_history (policy := policy) raw history
          refine ⟨action, rfl, rfl, rfl, step, ⟨ledger, names, support, ?_, usage,
            ScopedPortJoint.usage_history_iff.mp nextHistory, raw_step_preserves_resource_closure raw valid.joint.closed⟩, ?_⟩
          · simpa [before, after, ScopedPortJoint.advanceState, resource_world_append, resourceWorld] using effectsAfter
          · simpa [before, after, ScopedPortJoint.advanceState, resource_world_append, resourceWorld] using resultsAfter

theorem discard_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing contract)
    (known : registry.joint.effects owner = some effectContract)
    (resolved : scope.resolve binder = some owner) (built : makePlan capture = some plan)
    (planTyped : ScopedPorts.PlanTyped (signature declarations) (resourceWorld issued) effectContract.closeEffects plan)
    (fresh : (issued ++ [Owner.close closeId]).Nodup)
    (checks : AccessChecks ⟨.discard binder, scope,
      front.append (.live owner input answer capture caller tail)⟩ ambient) :
    let before : NamedState := ⟨⟨⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩,
      issued, completed⟩, activations⟩
    let after : Configuration := ⟨.unit, scope, (closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.close closeId] [.ticket owner]) ∧
      Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [.close closeId] [.ticket owner]) result outgoing contract := by
  obtain ⟨step, joint⟩ := ScopedPortJoint.discard_preserves_joint_configuration valid.joint known resolved built planTyped fresh checks
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState, resource_world_append, resourceWorld] using
    (CompletionFrames.discard_step resolved built valid.results (closeId := closeId)).2⟩

theorem closing_finish_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.unit, scope, .push (.closing identity caller) tail⟩, issued, completed⟩, activations⟩ result outgoing contract) :
    let before : NamedState := ⟨⟨⟨.unit, scope, .push (.closing identity caller) tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨.unit, caller, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.close identity]) ∧
      Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [] [.close identity]) result outgoing contract := by
  obtain ⟨raw, results⟩ := CompletionFrames.closing_finish_step valid.results
  have checks := value_access_checks (value := .unit) (stack := .push (.closing identity caller) tail)
    (scope := scope) (ambient := ambient) trivial (by intro identity payload caller answer rest same; cases same)
  obtain ⟨step, joint⟩ := ScopedPortJoint.checked_value_event_constructs_joint_step raw
    (show Code.unit.IsValue from trivial) valid.joint checks
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩

theorem retiring_preserves
    (valid : Valid declarations policy registry ambient
      ⟨⟨⟨.unit, scope, .push (.retiring owner) tail⟩, issued, completed⟩, activations⟩ result outgoing contract) :
    let before : NamedState := ⟨⟨⟨.unit, scope, .push (.retiring owner) tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨.unit, scope, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.ticket owner]) ∧
      Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [] [.ticket owner]) result outgoing contract := by
  obtain ⟨raw, results⟩ := CompletionFrames.retiring_step valid.results
  have checks := value_access_checks (value := .unit) (stack := .push (.retiring owner) tail)
    (scope := scope) (ambient := ambient) trivial (by intro identity payload caller answer rest same; cases same)
  obtain ⟨step, joint⟩ := ScopedPortJoint.checked_value_event_constructs_joint_step raw
    (show Code.unit.IsValue from trivial) valid.joint checks
  exact ⟨step, joint, by simpa [ScopedPortJoint.advanceState] using results⟩

namespace Examples
open CallableContracts.Examples (declarations scalar identity identityContract)
open CompletionContracts.Examples (callback)

def policy : TicketPolicy := fun _ => ActionRequirements.resumeOnly
def program : Code := .app (.cleanup callback identity) (.integer 17)
def initial : NamedState := ⟨⟨⟨program, .none, .nil⟩, [], []⟩, []⟩
def final : NamedState := ⟨⟨⟨.integer 17, .none, .nil⟩, [.cleanup 7], [.cleanup 7]⟩, []⟩

theorem initial_valid : Valid declarations policy (fun _ => none) [] initial .integer [] scalar := by
  apply initial_configuration_valid
    (typed := .app (.cleanup (.lambda .unit (List.nil_subset _))
      (.lambda (.variable rfl (List.nil_subset _)) (List.nil_subset _)) (List.nil_subset _))
      .integer (List.nil_subset _))
    (used := .app (.cleanup (.lambda .unit) (.lambda .variable)) .integer)
    (support := rfl)
  exact .app CompletionContracts.Examples.callable_cleanup (.leaf trivial rfl .nil)

theorem callable_cleanup_execution : NamedAccessSteps [] initial final ∧
    Valid declarations policy (fun _ => none) [] final .integer [] scalar := by
  obtain ⟨plain, shape, savedScope, e0, c1⟩ := focus_preserves initial_valid
    (Focus.appFunction (by intro impossible; cases impossible))
  obtain ⟨action, identityEq, callbackEq, scopeEq, e1, c2⟩ := cleanup_entry_preserves c1 trivial (identity := 7) (by decide)
  obtain ⟨closed, e2, c3⟩ := cleanup_start_preserves c2 trivial
  rw [callbackEq] at e2 c3
  obtain ⟨e3, c4⟩ := beta_preserves c3 trivial
  obtain ⟨e4, c5⟩ := cleanup_finish_preserves c4
  obtain ⟨e5, c6⟩ := plug_preserves c5 trivial
  simp only [shape, Context.plug] at c6 e5
  obtain ⟨e6, c7⟩ := beta_preserves c6 trivial
  refine ⟨?_, ?_⟩
  · simpa [ScopedPortJoint.advanceState, initial, final, identityEq, enteredActivations, Code.subst] using
      (NamedAccessSteps.next e0 (.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.refl _))))))))
  · simpa [ScopedPortJoint.advanceState, initial, final, identityEq, enteredActivations, Code.subst] using c7

end Examples

end Ash.OneShot.CompletionJoint

#print axioms Ash.OneShot.CompletionJoint.recorded_history
#print axioms Ash.OneShot.CompletionJoint.registry_fresh
#print axioms Ash.OneShot.CompletionJoint.result_registry_fresh
#print axioms Ash.OneShot.CompletionJoint.initial_configuration_valid
#print axioms Ash.OneShot.CompletionJoint.active_input_contract
#print axioms Ash.OneShot.CompletionJoint.resume_access_checks
#print axioms Ash.OneShot.CompletionJoint.resume_preserves
#print axioms Ash.OneShot.CompletionJoint.capture_preserves
#print axioms Ash.OneShot.CompletionJoint.payload_access_from_ports
#print axioms Ash.OneShot.CompletionJoint.current_payload_access
#print axioms Ash.OneShot.CompletionJoint.request_access_checks
#print axioms Ash.OneShot.CompletionJoint.capture_without_payload_premise
#print axioms Ash.OneShot.CompletionJoint.current_closed_value
#print axioms Ash.OneShot.CompletionJoint.value_access_checks
#print axioms Ash.OneShot.CompletionJoint.handler_return_preserves
#print axioms Ash.OneShot.CompletionJoint.clause_return_preserves
#print axioms Ash.OneShot.CompletionJoint.beta_preserves
#print axioms Ash.OneShot.CompletionJoint.bind_preserves
#print axioms Ash.OneShot.CompletionJoint.plug_preserves
#print axioms Ash.OneShot.CompletionJoint.cell_return_preserves
#print axioms Ash.OneShot.CompletionJoint.entry_access_checks
#print axioms Ash.OneShot.CompletionJoint.entry_results
#print axioms Ash.OneShot.CompletionJoint.entry_preserves
#print axioms Ash.OneShot.CompletionJoint.focus_preserves
#print axioms Ash.OneShot.CompletionJoint.callable_valid_included
#print axioms Ash.OneShot.CompletionJoint.cleanup_start_preserves
#print axioms Ash.OneShot.CompletionJoint.cleanup_finish_preserves
#print axioms Ash.OneShot.CompletionJoint.cleanup_entry_preserves
#print axioms Ash.OneShot.CompletionJoint.discard_preserves

#print axioms Ash.OneShot.CompletionJoint.closing_finish_preserves
#print axioms Ash.OneShot.CompletionJoint.retiring_preserves
#print axioms Ash.OneShot.CompletionJoint.Examples.initial_valid
#print axioms Ash.OneShot.CompletionJoint.Examples.callable_cleanup_execution
