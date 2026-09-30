import CallableProgress

/-!
Checked events authenticate supplied annotations and full continuation records
against the current state. Finite runs retain exact registries and contain no
intermediate-validity premises. Progress constructs a checked next event from
current validity. Disposal and cleanup remain outside this admitted fragment.
-/

namespace Ash.OneShot.CallableRuns
open Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ScopedTyping (resourceWorld resource_world_append)
open DeclarationResults (signature)

def makeRecord (policy : Syntax.TicketPolicy) (binder : Nat) (output : Port) (answer : Ty)
    (residual : List Instance) (inputBound : List Nat) (answerBound : CallableContracts.Contract)
    (finite : ClauseResults.PortBound output inputBound) : CallableJoint.TicketRecord :=
  ⟨⟨⟨output, eraseType answer, residual, residual⟩, policy binder⟩, ⟨.storage inputBound, answerBound⟩, inputBound, rfl, finite⟩

inductive CheckedCapture (declarations : DeclarationRegistry) (policy : Syntax.TicketPolicy)
    (registry : CallableJoint.Registry) (world : List Nat) (result : Port)
    (outgoing : List Instance) (bound : CallableContracts.Contract) :
    Configuration → Configuration → Nat → CallableJoint.TicketRecord → Prop where
  | capture {capture tail whole : Stack}
      (cut : HandlerCut requested whole capture tail handler)
      (selected : ClauseAt operation handler.clauses parameter binder body)
      (known : signature declarations requested operation = some (input, output))
      (closed : ClosedValue operand) (ready : ClosedExcept parameter body)
      (finite : ClauseResults.PortBound output inputBound)
      (handlerEffects : EffectFrame (signature declarations) registry.joint.effects world (.handler handler)
        (handler.effectInst :: residual) residual)
      (savedEffects : EffectStack (signature declarations) registry.joint.effects world capture [requested] residual)
      (outsideEffects : EffectStack (signature declarations) registry.joint.effects world tail residual outgoing)
      (savedPorts : StackTyped (signature declarations) registry.joint.effects.types world capture output (eraseType handler.answer))
      (outsidePorts : StackTyped (signature declarations) registry.joint.effects.types world tail (eraseType handler.answer) result)
      (handlerScope : CallableFrames.ScopeBound registry.results handler.scope savedTicket)
      (clauses : CallableContracts.ClausesDerive declarations environment world handler.effectInst answerBound handler.clauses)
      (savedResults : CallableFrames.StackReturns declarations registry.results world capture (.storage inputBound) answerBound)
      (outsideResults : CallableFrames.StackReturns declarations registry.results world tail answerBound bound) :
      CheckedCapture declarations policy registry world result outgoing bound
        ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer capture handler.scope tail⟩ owner
        (makeRecord policy binder output handler.answer residual inputBound answerBound finite)

theorem checked_capture_executes
    (event : CheckedCapture declarations policy registry world result outgoing bound before after owner record) :
    RawStep before after [.ticket owner] [] := by
  cases event with
  | capture cut selected known closed ready => exact .capture _ _ _ _ _ _ _ _ _ _ _ _ _ cut selected closed ready

theorem checked_capture_declared
    (event : CheckedCapture declarations policy registry world result outgoing bound before after owner record) :
    CaptureAnnotations.DeclaredCapture declarations before after owner := by
  cases event with
  | capture cut selected known closed ready => exact .capture cut selected (by simpa using known) closed ready

theorem checked_capture_preserves
    (event : CheckedCapture declarations policy registry (resourceWorld before.execution.issued) result outgoing bound
      before.execution.configuration after owner record)
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound)
    (fresh : (before.execution.issued ++ [Owner.ticket owner]).Nodup) :
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) ∧
      CallableJoint.Valid declarations policy (registry.insert owner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket owner] []) result outgoing bound ∧
      CallableJoint.RegistryExtends registry (registry.insert owner record) := by
  have raw := checked_capture_executes event
  have resultFresh := CallableJoint.result_registry_fresh valid fresh
  have jointFresh := ScopedPortJoint.registry_fresh valid.joint.registry fresh
  have effectFresh : registry.joint.effects owner = none := by simp [ScopedPortJoint.Registry.effects, jointFresh]
  obtain ⟨⟨configuration, issued, completed⟩, activations⟩ := before
  cases event with
  | @capture requested handler operation parameter binder body input output operand
      inputBound residual savedTicket environment answerBound scope owner capture tail whole cut selected known closed ready finite
      handlerEffects savedEffects outsideEffects savedPorts outsidePorts handlerScope clauses savedResults outsideResults =>
      let record := makeRecord policy binder output handler.answer residual inputBound answerBound finite
      let extended := registry.insert owner record
      let before : NamedState := ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer capture handler.scope tail⟩
      obtain ⟨currentPort, current, stack⟩ := effect_configuration_has_types valid.joint.effects
      cases current with
      | checked currentScope typed =>
          obtain ⟨actualInput, actualKnown, available, operandTyped⟩ := typed_perform_inversion typed
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans actualKnown))
          have handlerKnown := known
          rw [← ScopedTyping.handler_cut_instance cut] at handlerKnown
          have extension : EffectExtension registry.joint.effects extended.joint.effects := by
            simpa [extended, record, makeRecord] using effect_ticket_insertion_extends
              (contract := ⟨output, eraseType handler.answer, residual, residual⟩) effectFresh
          have recorded : extended.joint.effects owner = some record.joint.contract := by
            simp [extended, CallableJoint.Registry.insert, CallableJoint.Registry.joint, ScopedPortJoint.Registry.effects]
          have recordedTypes : extended.joint.effects.types owner = some (output, eraseType handler.answer) := by
            simp [EffectTickets.types, recorded, record, makeRecord]
          have resultExtension : CallableFrames.RegistryExtends registry.results extended.results := by
            simpa [extended] using CallableFrames.insert_extends (record := record.results) resultFresh
          have recordedResults : extended.results owner = some record.results := by
            simp [extended, CallableJoint.Registry.insert, CallableJoint.Registry.results]
          cases handlerEffects with
          | handler caller clausesTyped coverage unique =>
              have effectsAfter : EffectConfigurationTyped (signature declarations) extended.joint.effects
                  (resourceWorld issued) after result outgoing := by
                refine ⟨eraseType handler.answer, residual, .checked (.bound recorded) ?_, ?_, ?_⟩
                · exact selected_clause_substitution_typed selected clausesTyped handlerKnown operandTyped closed
                · exact .live (by simpa [after] using recordedTypes)
                    (effect_scope_known_has_types (effect_scope_known_extension caller extension))
                    (by simpa using stack_typed_extension savedPorts (effect_extension_has_type_extension extension))
                    (stack_typed_extension outsidePorts (effect_extension_has_type_extension extension))
                · exact .live recorded (effect_scope_known_extension caller extension)
                    (effect_stack_extension savedEffects extension) (effect_stack_extension outsideEffects extension)
                    (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
              obtain ⟨actualClosed, argumentBound, resumeBound, inputFinite, outputFinite, substituted⟩ :=
                CallableFrames.selected_clause_substitution selected clauses handlerKnown operandTyped closed.1
              have sameBound : resumeBound = inputBound := (Option.some.inj (outputFinite.symm.trans finite))
              subst resumeBound
              have resultsAfter : CallableFrames.ConfigurationReturns declarations extended.results
                  (resourceWorld issued) after bound := by
                refine ⟨_, _, answerBound, .bound recordedResults, substituted, ?_⟩
                exact .live recordedResults (CallableFrames.scope_extends handlerScope resultExtension)
                  (CallableFrames.stack_registry_extends savedResults resultExtension)
                  (CallableFrames.stack_registry_extends outsideResults resultExtension)
              have checks := CallableJoint.request_access_checks valid
              have freshHandlers : (activations ++ enteredActivations before.execution.configuration after).Nodup := by
                simpa [before, after, enteredActivations] using valid.joint.names.unique
              have step : NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) :=
                ⟨.event before after [.ticket owner] [] raw fresh freshHandlers, checks⟩
              obtain ⟨ledger, names, support⟩ := named_access_step_preserves step valid.joint.ledger valid.joint.names valid.joint.support
              have history := ScopedPortJoint.usage_history_iff.mpr valid.joint.registry
              have usage := raw_step_preserves_configuration_usage raw
                (usage_checks_from_allocation_and_access history fresh checks) valid.joint.usage
              have nextHistory := raw_step_preserves_usage_registry_history (policy := policy) raw history
              have update : extended.joint.usage = ScopedExecution.advanceUsageTickets policy registry.joint.usage after [.ticket owner] := by
                simp [extended, record, makeRecord, after, ScopedExecution.advanceUsageTickets]
              rw [← update] at usage nextHistory
              refine ⟨step, ⟨⟨ledger, names, support, ?_, usage, ScopedPortJoint.usage_history_iff.mp nextHistory,
                raw_step_preserves_resource_closure raw valid.joint.closed⟩, ?_⟩,
                CallableJoint.registry_insert_extends (CallableJoint.registry_fresh valid fresh)⟩
              · simpa [before, after, extended, record, ScopedPortJoint.advanceState, resource_world_append, resourceWorld] using effectsAfter
              · simpa [before, after, extended, record, ScopedPortJoint.advanceState, resource_world_append, resourceWorld] using resultsAfter

theorem checked_capture_exists
    (event : CaptureAnnotations.DeclaredCapture declarations before.execution.configuration after owner)
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound) :
    ∃ record, CheckedCapture declarations policy registry (resourceWorld before.execution.issued) result outgoing bound
      before.execution.configuration after owner record := by
  obtain ⟨⟨configuration, issued, completed⟩, activations⟩ := before
  cases event with
  | @capture requested whole capture tail handler operation parameter binder body input annotation operand scope owner
      cut selected known closed ready =>
      obtain ⟨currentPort, effects, current, stackPorts, stackEffects⟩ := valid.joint.effects
      obtain ⟨environment, ticket, currentBound, scopeChecked, code, stackResults⟩ := valid.results
      obtain ⟨savedEnvironment, savedTicket, answerBound, handlerScope, clauses, savedResults, outsideResults⟩ :=
        CallableFrames.handler_cut_certificate cut stackResults
      obtain ⟨residual, savedEffects, outsideEffects, handlerEffects⟩ := handler_cut_effect_decomposition cut stackEffects
      obtain ⟨savedPorts, outsidePorts, handlerPorts⟩ := handler_cut_retains_typing cut stackPorts
      cases current with
      | checked scopeTyped typed =>
          obtain ⟨actualInput, actualKnown, available, operandTyped⟩ := typed_perform_inversion typed
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans actualKnown))
          have handlerKnown := known
          rw [← ScopedTyping.handler_cut_instance cut] at handlerKnown
          obtain ⟨argumentPort, resultPort, argumentBound, inputBound, actual, inputFinite, outputFinite, bodyChecked⟩ :=
            CallableFrames.selected_clause selected clauses
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (handlerKnown.symm.trans actual))
          have canonical := CaptureAnnotations.finite_annotation outputFinite rfl
          have narrowedEffects : EffectStack (signature declarations) registry.joint.effects (resourceWorld issued)
              capture [requested] residual := effect_stack_input_weaken savedEffects
                (by intro effect member; obtain rfl := List.mem_singleton.mp member; exact available)
          have sameResult := CallableFrames.declared_output_contract code known outputFinite
          rw [sameResult] at savedResults
          refine ⟨makeRecord policy binder (eraseType annotation) handler.answer residual inputBound answerBound outputFinite, ?_⟩
          have checked := CheckedCapture.capture (policy := policy) (scope := scope) (owner := owner) cut selected known closed ready
            outputFinite handlerEffects narrowedEffects outsideEffects savedPorts outsidePorts handlerScope clauses
            savedResults outsideResults
          simpa only [← canonical] using checked

inductive StableEvent : Configuration → Configuration → List Owner → Prop where
  | value (raw : RawStep before after [] discharged) (isValue : before.expression.IsValue) :
      StableEvent before after discharged
  | ordinary (step : ScopedPortJoint.OrdinaryStep before after) : StableEvent before after []
  | resume {front capture tail : Stack} (closed : ClosedValue value) (resolved : scope.resolve binder = some owner) :
      StableEvent
        ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩
        ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ [.ticket owner]

theorem stable_executes (event : StableEvent before after discharged) : RawStep before after [] discharged := by
  cases event with
  | value raw isValue => exact raw
  | ordinary step => exact ScopedPortJoint.ordinary_step_executes step
  | resume closed resolved => exact .resume _ _ _ _ _ _ _ _ _ _ closed resolved

theorem stable_boundary (event : StableEvent before after discharged) :
    GenerativeProgress.NoSourceRequest before := by
  cases event with
  | value raw isValue => exact GenerativeProgress.value_boundary isValue
  | ordinary step => cases step with
      | read selected | write selected => exact GenerativeProgress.builtin_boundary selected
      | bind | beta | ifTrue | ifFalse =>
          exact GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)
  | resume => exact GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)

theorem stable_effects
    (event : StableEvent before after discharged)
    (typed : EffectConfigurationTyped (signature declarations) tickets world before result outgoing) :
    EffectConfigurationTyped (signature declarations) tickets world after result outgoing := by
  cases event with
  | value raw isValue =>
      have closed := at_type_value_closed (effect_configuration_has_types typed).choose_spec.1 isValue
      exact raw_value_step_preserves_effect_configuration raw closed typed
  | ordinary step => exact ScopedPortJoint.ordinary_step_preserves_effects step typed
  | resume closed resolved => exact resume_preserves_effect_configuration resolved typed closed.1

theorem stable_preserves
    (event : StableEvent before.execution.configuration after discharged)
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup) :
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] discharged) ∧
      CallableJoint.Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [] discharged) result outgoing bound := by
  have raw := stable_executes event
  have boundary := stable_boundary event
  have checks := CallableProgress.return_access_checks (ambient := ambient) valid.results boundary
  have fresh : (before.execution.issued ++ []).Nodup := by simpa [RunState.erase] using valid.joint.ledger.2
  have step : NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] discharged) :=
    ⟨.event before after [] discharged raw fresh freshHandlers, checks⟩
  obtain ⟨ledger, names, support⟩ := named_access_step_preserves step valid.joint.ledger valid.joint.names valid.joint.support
  have history := ScopedPortJoint.usage_history_iff.mpr valid.joint.registry
  have usage := raw_step_preserves_configuration_usage raw
    (usage_checks_from_allocation_and_access history fresh checks) valid.joint.usage
  have nextHistory := raw_step_preserves_usage_registry_history (policy := policy) raw history
  refine ⟨step, ⟨ledger, names, support, ?_, usage, ScopedPortJoint.usage_history_iff.mp nextHistory,
    raw_step_preserves_resource_closure raw valid.joint.closed⟩, ?_⟩
  · simpa [ScopedPortJoint.advanceState] using stable_effects event valid.joint.effects
  · exact CallableProgress.named_preserves_results step valid.results boundary

inductive CheckedEvent (declarations : DeclarationRegistry) (policy : Syntax.TicketPolicy)
    (registry : CallableJoint.Registry) (result : Port) (outgoing : List Instance)
    (bound : CallableContracts.Contract) (before : NamedState) :
    CallableJoint.Registry → Configuration → List Owner → List Owner → Prop where
  | stable (event : StableEvent before.execution.configuration after discharged) :
      CheckedEvent declarations policy registry result outgoing bound before registry after [] discharged
  | entry (event : EntryAnnotations.EntryTyping (signature declarations) registry.joint.effects
      (resourceWorld before.execution.issued) result outgoing before.execution.configuration after created) :
      CheckedEvent declarations policy registry result outgoing bound before registry after created []
  | capture (event : CheckedCapture declarations policy registry
      (resourceWorld before.execution.issued) result outgoing bound before.execution.configuration after owner record) :
      CheckedEvent declarations policy registry result outgoing bound before (registry.insert owner record)
        after [.ticket owner] []

theorem checked_executes
    (event : CheckedEvent declarations policy registry result outgoing bound before nextRegistry after created discharged) :
    RawStep before.execution.configuration after created discharged := by
  cases event with
  | stable event => exact stable_executes event
  | entry event => exact EntryAnnotations.entry_executes event
  | capture event => exact checked_capture_executes event

theorem checked_preserves
    (event : CheckedEvent declarations policy registry result outgoing bound before nextRegistry after created discharged)
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound)
    (fresh : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup) :
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after created discharged) ∧
      CallableJoint.Valid declarations policy nextRegistry ambient
        (ScopedPortJoint.advanceState before after created discharged) result outgoing bound ∧
      CallableJoint.RegistryExtends registry nextRegistry := by
  cases event with
  | stable event =>
      obtain ⟨step, valid⟩ := stable_preserves event valid freshHandlers
      exact ⟨step, valid, CallableJoint.registry_extends_refl _⟩
  | entry event =>
      obtain ⟨step, valid⟩ := CallableJoint.entry_preserves event valid fresh freshHandlers
      exact ⟨step, valid, CallableJoint.registry_extends_refl _⟩
  | capture event => exact checked_capture_preserves event valid fresh

inductive CheckedStep (declarations : DeclarationRegistry) (policy : Syntax.TicketPolicy)
    (result : Port) (outgoing : List Instance) (bound : CallableContracts.Contract) :
    CallableJoint.Registry → NamedState → CallableJoint.Registry → NamedState → Prop where
  | event (checked : CheckedEvent declarations policy registry result outgoing bound
      before nextRegistry after created discharged)
      (fresh : (before.execution.issued ++ created).Nodup)
      (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup) :
      CheckedStep declarations policy result outgoing bound registry before nextRegistry
        (ScopedPortJoint.advanceState before after created discharged)

inductive CheckedRun (declarations : DeclarationRegistry) (policy : Syntax.TicketPolicy)
    (result : Port) (outgoing : List Instance) (bound : CallableContracts.Contract) :
    CallableJoint.Registry → NamedState → CallableJoint.Registry → NamedState → Prop where
  | refl : CheckedRun declarations policy result outgoing bound registry state registry state
  | next (step : CheckedStep declarations policy result outgoing bound registry before nextRegistry middle)
      (rest : CheckedRun declarations policy result outgoing bound nextRegistry middle finalRegistry after) :
      CheckedRun declarations policy result outgoing bound registry before finalRegistry after

theorem step_preserves
    (checked : CheckedStep declarations policy result outgoing bound registry before nextRegistry after)
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound) :
    NamedAccessStep ambient before after ∧
      CallableJoint.Valid declarations policy nextRegistry ambient after result outgoing bound ∧
      CallableJoint.RegistryExtends registry nextRegistry := by
  cases checked with
  | event checked fresh freshHandlers => exact checked_preserves checked valid fresh freshHandlers

theorem run_preserves
    (run : CheckedRun declarations policy result outgoing bound registry before finalRegistry after)
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound) :
    NamedAccessSteps ambient before after ∧
      CallableJoint.Valid declarations policy finalRegistry ambient after result outgoing bound ∧
      CallableJoint.RegistryExtends registry finalRegistry := by
  induction run with
  | refl => exact ⟨.refl _, valid, CallableJoint.registry_extends_refl _⟩
  | next step rest ih =>
      obtain ⟨actual, nextValid, extended⟩ := step_preserves step valid
      obtain ⟨execution, finalValid, later⟩ := ih nextValid
      exact ⟨.next actual execution, finalValid, CallableJoint.registry_extends_trans extended later⟩

theorem run_closed_progress
    (run : CheckedRun declarations policy result [] bound registry before finalRegistry after)
    (valid : CallableJoint.Valid declarations policy registry ambient before result [] bound) :
    ScopedPortProgress.Terminal after.execution.configuration ∨
      ∃ next successor, NamedAccessStep ambient after successor ∧
        CallableJoint.Valid declarations policy next ambient successor result [] bound ∧
        CallableJoint.RegistryExtends finalRegistry next := by
  exact CallableProgress.closed_progress (run_preserves run valid).2.1

theorem run_terminal_accounting
    (run : CheckedRun declarations policy result outgoing bound registry before finalRegistry after)
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound)
    (terminal : ScopedPortProgress.Terminal after.execution.configuration) :
    after.execution.issued.Perm after.execution.completed ∧ after.execution.completed.Nodup := by
  exact CallableProgress.terminal_accounting (run_preserves run valid).2.1 terminal

theorem run_terminal_result_support
    (run : CheckedRun declarations policy result outgoing bound registry before finalRegistry after)
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound)
    (terminal : ScopedPortProgress.Terminal after.execution.configuration) :
    Syntax.resourceDependencies after.execution.configuration.expression.dependencies ⊆ bound.storageOf := by
  exact CallableProgress.terminal_result_support (run_preserves run valid).2.1 terminal

theorem stable_step
    (event : StableEvent before.execution.configuration after discharged)
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound) :
    CheckedStep declarations policy result outgoing bound registry before registry
      (ScopedPortJoint.advanceState before after [] discharged) := by
  obtain ⟨⟨configuration, issued, completed⟩, activations⟩ := before
  have fresh : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.joint.ledger.2
  have noEntry : enteredActivations configuration after = [] := by
    cases event with
    | value raw isValue =>
        exact value_enters_no_activation (CallableJoint.current_closed_value valid isValue)
    | ordinary ordinary => exact ScopedPortJoint.ordinary_step_has_no_activation ordinary
    | resume => rfl
  exact .event (.stable event) fresh (by simpa [noEntry] using valid.joint.names.unique)

theorem named_value_checked
    (step : NamedAccessStep ambient before after)
    (isValue : before.execution.configuration.expression.IsValue) :
    CheckedStep declarations policy result outgoing bound registry before registry after := by
  obtain ⟨⟨configuration, issued, completed⟩, activations⟩ := before
  cases step.execution with
  | event after created discharged raw fresh freshHandlers =>
      have noOwners : created = [] := by cases raw <;> first | rfl | cases isValue
      subst created
      exact .event (.stable (.value raw isValue)) fresh freshHandlers

theorem declared_capture_exists
    (typed : EffectConfigurationTyped (signature declarations) tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result outgoing)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (owner : Nat) :
    ∃ after, CaptureAnnotations.DeclaredCapture declarations
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ after owner := by
  obtain ⟨output, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, known, available, operandTyped⟩ := typed_perform_inversion expression
      obtain ⟨residual, capturedEffects, outsideEffects, handlerEffects⟩ := handler_cut_effect_decomposition cut effectStack
      cases handlerEffects with
      | handler caller clauses coverage unique =>
          have atHandler := known
          rw [← ScopedTyping.handler_cut_instance cut] at atHandler
          obtain ⟨parameter, binder, body, selected⟩ := ScopedTyping.clause_at_of_key (coverage _ _ _ atHandler)
          obtain ⟨clauseInput, clauseOutput, clauseKnown, bodyTyped⟩ := selected_clause_typed selected clauses
          exact ⟨_, .capture (annotation := embedPort output) cut selected (by simpa using known)
            (typed_value_closed operandTyped isValue) (typed_suffix_ready bodyTyped)⟩

theorem request_progress
    (valid : CallableJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (isValue : operand.IsValue) :
    (requested ∈ outgoing ∧ stack.erase.resolve requested = none) ∨
      ∃ next after, CheckedStep declarations policy result outgoing bound registry
        ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ next after := by
  cases resolved : stack.erase.resolve requested with
  | none =>
      rcases current_request_is_interpreted_or_exported valid.joint.effects with ⟨target, found⟩ | exported
      · simp [resolved] at found
      · exact Or.inl ⟨exported, rfl⟩
  | some target => cases target with
      | builtin identity =>
          obtain rfl := ScopedTyping.builtin_resolution_instance stack resolved
          obtain ⟨after, raw, effects⟩ := builtin_effect_progress valid.joint.effects isValue resolved
          exact Or.inr ⟨registry, _, stable_step
            (.ordinary (ScopedPortProgress.nonallocating_request_is_ordinary raw rfl isValue)) valid⟩
      | source activation =>
          obtain ⟨capture, tail, handler, cut, active⟩ := ScopedTyping.handler_selection_of_resolution stack resolved
          obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) valid.joint.ledger.2
          obtain ⟨after, declared⟩ := declared_capture_exists valid.joint.effects cut isValue owner
          obtain ⟨record, checked⟩ := checked_capture_exists declared valid
          have noEntry : enteredActivations
              ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ after = [] := rfl
          exact Or.inr ⟨registry.insert owner record, _, .event (.capture checked) fresh
            (by simpa [noEntry] using valid.joint.names.unique)⟩

theorem resume_progress
    (valid : CallableJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (isValue : value.IsValue) :
    ∃ after, CheckedStep declarations policy result outgoing bound registry
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ registry after := by
  obtain ⟨current, demand, code, control, accessible, balance, unique⟩ := valid.joint.usage
  obtain ⟨owner, resolved, same⟩ := ScopedPortJoint.resume_demand_supplies_owner code
  have present : owner ∈ activeTickets stack := accessible (same ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := ScopedPortJoint.active_ticket_has_boundary present
  subst stack
  obtain ⟨output, expression, ports⟩ := effect_configuration_has_types valid.joint.effects
  cases expression with
  | checked scopeTyped typed => cases typed with
      | resume operand available =>
          exact ⟨_, stable_step (.resume (typed_value_closed operand isValue) resolved) valid⟩

theorem current_progress
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ScopedPortProgress.OutwardRequest before.execution.configuration outgoing ∨
      ∃ next after, CheckedStep declarations policy result outgoing bound registry before next after := by
  obtain ⟨⟨⟨expression, scope, stack⟩, issued, completed⟩, activations⟩ := before
  obtain ⟨input, current, ports⟩ := effect_configuration_has_types valid.joint.effects
  have admitted : CallableProgress.SupportedHead expression := by
    obtain ⟨environment, ticket, bound, scope, code, rest⟩ := valid.results
    exact CallableProgress.supported_head code
  have form : ScopedPortProgress.CurrentForm expression := by
    cases current with
    | checked scopeTyped typed => exact ScopedPortProgress.typed_current_form typed
  have sameOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.joint.ledger.2
  cases form with
  | value isValue =>
      have boundary := GenerativeProgress.value_boundary (configuration := ⟨expression, scope, stack⟩) isValue
      rcases ScopedPortJoint.checked_value_progress valid.joint isValue
        (CallableProgress.return_access_checks valid.results boundary) with terminal | next
      · exact Or.inl ⟨isValue, terminal⟩
      · obtain ⟨after, step, joint⟩ := next
        exact Or.inr (Or.inr ⟨registry, after, named_value_checked step isValue⟩)
  | focus position =>
      obtain ⟨plain, contextEq, scopeEq, entry⟩ := EntryAnnotations.focus_annotations_exist valid.joint.effects position
      exact Or.inr (Or.inr ⟨registry, _, .event (.entry entry) sameOwners
        (by simpa [focus_enters_no_activation position] using valid.joint.names.unique)⟩)
  | bind isValue =>
      cases current with
      | checked scopeTyped typed => cases typed with
          | bind initializer suffix =>
              exact Or.inr (Or.inr ⟨registry, _, stable_step
                (.ordinary (.bind (typed_value_closed initializer isValue) (typed_suffix_ready suffix))) valid⟩)
  | branch isValue =>
      cases current with
      | checked scopeTyped typed => cases typed with
          | branch conditionTyped yesTyped noTyped =>
              obtain ⟨boolean, rfl⟩ := typed_boolean_value conditionTyped isValue
              cases boolean
              · exact Or.inr (Or.inr ⟨registry, _, stable_step (.ordinary .ifFalse) valid⟩)
              · exact Or.inr (Or.inr ⟨registry, _, stable_step (.ordinary .ifTrue) valid⟩)
  | request isValue =>
      rcases request_progress valid isValue with outward | next
      · exact Or.inr (Or.inl ⟨_, _, _, rfl, isValue, outward⟩)
      · exact Or.inr (Or.inr next)
  | handler =>
      obtain ⟨activation, fresh⟩ := ScopedPortProgress.fresh_activation_exists valid.joint.names.unique
      obtain ⟨handler, active, entry⟩ := EntryAnnotations.handler_annotations_exist valid.joint.effects activation
      exact Or.inr (Or.inr ⟨registry, _, .event (.entry entry) sameOwners
        (by simpa [enteredActivations, active] using fresh)⟩)
  | resume isValue =>
      obtain ⟨after, step⟩ := resume_progress valid isValue
      exact Or.inr (Or.inr ⟨registry, after, step⟩)
  | resource isValue =>
      cases current with
      | checked scopeTyped typed =>
          rename_i binder initializer body ticket allowed
          have integerTyped : Typed (signature declarations) (resourceWorld issued) TypeEnv.empty ticket allowed initializer .integer := by
            cases typed with | resource initializer _ _ _ _ => exact initializer
          obtain ⟨payload, rfl⟩ := typed_integer_value integerTyped isValue
          obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.resource (fun _ => rfl) valid.joint.ledger.2
          obtain ⟨answer, entry⟩ := EntryAnnotations.resource_annotations_exist valid.joint.effects identity
          exact Or.inr (Or.inr ⟨registry, _, .event (.entry entry) fresh
            (by simpa [enteredActivations] using valid.joint.names.unique)⟩)
  | app functionValue argumentValue =>
      cases current with
      | checked scopeTyped typed => cases typed with
          | app functionTyped argumentTyped available =>
              obtain ⟨parameter, body, rfl⟩ := typed_function_value functionTyped functionValue
              exact Or.inr (Or.inr ⟨registry, _, stable_step
                (.ordinary (.beta (typed_value_closed argumentTyped argumentValue)
                  (typed_value_closed functionTyped functionValue))) valid⟩)
  | discard | cleanup => exact False.elim admitted

theorem closed_progress
    (valid : CallableJoint.Valid declarations policy registry ambient before result [] bound) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ∃ next after, CheckedStep declarations policy result [] bound registry before next after := by
  rcases current_progress valid with terminal | outward | next
  · exact Or.inl terminal
  · obtain ⟨requested, operation, operand, same, isValue, exported, missing⟩ := outward
    cases exported
  · exact Or.inr next

theorem checked_progress_preserves
    (valid : CallableJoint.Valid declarations policy registry ambient before result [] bound) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ∃ next after, CheckedStep declarations policy result [] bound registry before next after ∧
        NamedAccessStep ambient before after ∧
        CallableJoint.Valid declarations policy next ambient after result [] bound ∧
        CallableJoint.RegistryExtends registry next := by
  rcases closed_progress valid with terminal | ⟨next, after, step⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨next, after, step, step_preserves step valid⟩

theorem run_append
    (first : CheckedRun declarations policy result outgoing bound registry before middleRegistry middle)
    (second : CheckedRun declarations policy result outgoing bound middleRegistry middle finalRegistry after) :
    CheckedRun declarations policy result outgoing bound registry before finalRegistry after := by
  induction first with
  | refl => exact second
  | next step rest ih => exact .next step (ih second)

theorem run_progress
    (run : CheckedRun declarations policy result [] bound registry before finalRegistry after)
    (valid : CallableJoint.Valid declarations policy registry ambient before result [] bound) :
    ScopedPortProgress.Terminal after.execution.configuration ∨
      ∃ next successor, CheckedStep declarations policy result [] bound finalRegistry after next successor ∧
        CheckedRun declarations policy result [] bound registry before next successor ∧
        NamedAccessStep ambient after successor ∧
        CallableJoint.Valid declarations policy next ambient successor result [] bound ∧
        CallableJoint.RegistryExtends finalRegistry next := by
  have finalValid := (run_preserves run valid).2.1
  rcases checked_progress_preserves finalValid with terminal | ⟨next, successor, step, rest⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨next, successor, step, run_append run (.next step .refl), rest⟩

theorem initial_run_safety
    (typed : Typed (signature declarations) [] TypeEnv.empty .none [] expression result)
    (used : Uses policy .none .available expression .available)
    (support : Syntax.resourceDependencies expression.dependencies = [])
    (checked : CallableContracts.Derives declarations environment [] .none expression bound)
    (run : CheckedRun declarations policy result [] bound (fun _ => none)
      ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ finalRegistry after) :
    NamedAccessSteps [] ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ after ∧
      CallableJoint.Valid declarations policy finalRegistry [] after result [] bound ∧
      (ScopedPortProgress.Terminal after.execution.configuration ∨
        ∃ next successor, CheckedStep declarations policy result [] bound finalRegistry after next successor ∧
          CheckedRun declarations policy result [] bound (fun _ => none)
            ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ next successor ∧
          NamedAccessStep [] after successor ∧
          CallableJoint.Valid declarations policy next [] successor result [] bound ∧
          CallableJoint.RegistryExtends finalRegistry next) := by
  have valid := CallableJoint.initial_configuration_valid typed used support checked
  have preserved := run_preserves run valid
  exact ⟨preserved.1, preserved.2.1, run_progress run valid⟩

namespace Examples
open CallableContracts.Examples (declarations scalar identity identityContract applyTo17 higherOrder)
open CallableJoint.Examples (policy initial middle final higher_order_initial higher_order_typed higher_order_usage)

theorem higher_order_run : CheckedRun declarations policy .integer [] scalar
    (fun _ => none) initial (fun _ => none) final := by
  have first : CheckedStep declarations policy .integer [] scalar (fun _ => none) initial (fun _ => none) middle :=
    stable_step (.ordinary (.beta
      (by exact ⟨trivial, rfl, by intro dependency member; cases member⟩)
      (by exact ⟨trivial, rfl, by intro dependency member; cases member⟩))) higher_order_initial
  have midway := (step_preserves first higher_order_initial).2.1
  have second : CheckedStep declarations policy .integer [] scalar (fun _ => none) middle (fun _ => none) final :=
    stable_step (.ordinary (.beta
      (by exact ⟨trivial, rfl, by intro dependency member; cases member⟩)
      (by exact ⟨trivial, rfl, by intro dependency member; cases member⟩))) midway
  exact .next first (.next second .refl)

theorem higher_order_safety : NamedAccessSteps [] initial final ∧
    CallableJoint.Valid declarations policy (fun _ => none) [] final .integer [] scalar ∧
    ScopedPortProgress.Terminal final.execution.configuration := by
  have safety := initial_run_safety higher_order_typed higher_order_usage rfl
    CallableContracts.Examples.higher_order_checked higher_order_run
  exact ⟨safety.1, safety.2.1, by exact ⟨trivial, rfl⟩⟩

end Examples

namespace CaptureExample
open CallableJoint.CaptureExample (policy initial beforeHandler entered atRequest liveState spentState
  handled_typed clauses_typed identity_typed initial_valid)
open CallableFrames.Examples (functionType clauseBody clauses handler pendingFunction outsideCall captured outside s0 s1 s11)
open CallableContracts.Examples (identity identityContract scalar)
open GenerativeFrames.Examples (declarations)
open ContinuationBounds.Examples (family)

theorem source_enters_request : CheckedRun declarations policy .integer [] scalar (fun _ => none) initial (fun _ => none) atRequest ∧
    CallableJoint.Valid declarations policy (fun _ => none) [] atRequest .integer [] scalar := by
  have first : EntryAnnotations.EntryTyping (signature declarations) (CallableJoint.Registry.joint (fun _ => none)).effects [] .integer []
      initial.execution.configuration beforeHandler.execution.configuration [] :=
    .focus (plain := outsideCall) (.appFunction (by intro impossible; cases impossible)) .none handled_typed
      (.appFunction .integer (List.nil_subset _)) .nil (.nil (List.nil_subset _))
  obtain ⟨e0, c1⟩ := CallableJoint.entry_preserves first initial_valid (by decide) (by decide)
  change CallableJoint.Valid declarations policy (fun _ => none) [] beforeHandler .integer [] scalar at c1
  have outerFrame : EffectFrame (signature declarations) (CallableJoint.Registry.joint (fun _ => none)).effects []
      (.plain outsideCall) [] [] := .plain .none (.appFunction .integer (List.nil_subset _))
  have outerTypes : StackTyped (signature declarations) (CallableJoint.Registry.joint (fun _ => none)).effects.types [] outside
      (eraseType functionType) .integer := .push (effect_frame_has_types outerFrame) .nil
  have outerEffects : EffectStack (signature declarations) (CallableJoint.Registry.joint (fun _ => none)).effects [] outside [] [] :=
    .push outerFrame (.nil (List.nil_subset _)) (List.Subset.refl _)
  have second : EntryAnnotations.EntryTyping (signature declarations) (CallableJoint.Registry.joint (fun _ => none)).effects [] .integer []
      beforeHandler.execution.configuration entered.execution.configuration [] :=
    .handler (handler := handler) (.checked .none handled_typed) outerTypes outerEffects
  obtain ⟨e1, c2⟩ := CallableJoint.entry_preserves second c1 (by decide) (by decide)
  change CallableJoint.Valid declarations policy (fun _ => none) [] entered .integer [] scalar at c2
  have handlerFrame : EffectFrame (signature declarations) (CallableJoint.Registry.joint (fun _ => none)).effects []
      (.handler handler) [family] [] :=
    .handler ⟨.none, .none⟩ clauses_typed (ClauseResults.Examples.single_coverage _ _ _) (by decide)
  have third : EntryAnnotations.EntryTyping (signature declarations) (CallableJoint.Registry.joint (fun _ => none)).effects [] .integer []
      entered.execution.configuration atRequest.execution.configuration [] :=
    .focus (plain := pendingFunction) (.bind (by intro impossible; cases impossible)) .none (.perform rfl (by simp) .unit (List.nil_subset _))
      (.bind (identity_typed _ _ _)) (.push (effect_frame_has_types handlerFrame) outerTypes)
      (.push handlerFrame outerEffects (List.Subset.refl _))
  obtain ⟨e2, c3⟩ := CallableJoint.entry_preserves third c2 (by decide) (by decide)
  exact ⟨.next (.event (.entry first) (by decide) (by decide))
    (.next (.event (.entry second) (by decide) (by decide))
      (.next (.event (.entry third) (by decide) (by decide)) .refl)), c3⟩


theorem capture_run : ∃ registry,
    CheckedRun declarations policy .integer [] scalar (fun _ => none) initial registry (liveState s1) ∧
      CallableJoint.Valid declarations policy registry [] (liveState s1) .integer [] scalar := by
  have declared : CaptureAnnotations.DeclaredCapture declarations atRequest.execution.configuration s1 5 := by
    have event := CaptureAnnotations.DeclaredCapture.capture (annotation := Ty.integer)
      (declarations := declarations) (operand := Code.unit) (scope := .none) (owner := 5) CallableFrames.Examples.selected_cut
      (ClauseAt.hit (rest := Clauses.nil)) (by rfl)
      (by exact ⟨trivial, rfl, by intro dependency member; cases member⟩)
      (by intro name member; simp [clauseBody, Code.dependencies, Syntax.without] at member)
    simpa [atRequest, s0, s1, handler, clauses, clauseBody, Code.subst] using event
  obtain ⟨record, capture⟩ := checked_capture_exists declared source_enters_request.2
  have step : CheckedStep declarations policy .integer [] scalar (fun _ => none) atRequest
      (CallableJoint.Registry.insert (fun _ => none) 5 record) (liveState s1) := by
    have event := CheckedStep.event (.capture capture) (by decide)
      (show (atRequest.activations ++ enteredActivations atRequest.execution.configuration s1).Nodup from by decide)
    simpa [atRequest, liveState, s0, ScopedPortJoint.advanceState, enteredActivations] using event
  exact ⟨_, run_append source_enters_request.1 (.next step .refl),
    (step_preserves step source_enters_request.2).2.1⟩

end CaptureExample

end Ash.OneShot.CallableRuns

#print axioms Ash.OneShot.CallableRuns.checked_capture_executes
#print axioms Ash.OneShot.CallableRuns.checked_capture_declared
#print axioms Ash.OneShot.CallableRuns.checked_capture_preserves
#print axioms Ash.OneShot.CallableRuns.checked_capture_exists
#print axioms Ash.OneShot.CallableRuns.stable_executes
#print axioms Ash.OneShot.CallableRuns.stable_boundary
#print axioms Ash.OneShot.CallableRuns.stable_effects
#print axioms Ash.OneShot.CallableRuns.stable_preserves
#print axioms Ash.OneShot.CallableRuns.checked_executes
#print axioms Ash.OneShot.CallableRuns.checked_preserves
#print axioms Ash.OneShot.CallableRuns.step_preserves
#print axioms Ash.OneShot.CallableRuns.run_preserves
#print axioms Ash.OneShot.CallableRuns.run_closed_progress
#print axioms Ash.OneShot.CallableRuns.run_terminal_accounting
#print axioms Ash.OneShot.CallableRuns.run_terminal_result_support
#print axioms Ash.OneShot.CallableRuns.stable_step
#print axioms Ash.OneShot.CallableRuns.named_value_checked
#print axioms Ash.OneShot.CallableRuns.declared_capture_exists
#print axioms Ash.OneShot.CallableRuns.request_progress
#print axioms Ash.OneShot.CallableRuns.resume_progress
#print axioms Ash.OneShot.CallableRuns.current_progress
#print axioms Ash.OneShot.CallableRuns.closed_progress
#print axioms Ash.OneShot.CallableRuns.checked_progress_preserves
#print axioms Ash.OneShot.CallableRuns.run_append
#print axioms Ash.OneShot.CallableRuns.run_progress
#print axioms Ash.OneShot.CallableRuns.initial_run_safety

#print axioms Ash.OneShot.CallableRuns.Examples.higher_order_run
#print axioms Ash.OneShot.CallableRuns.Examples.higher_order_safety
#print axioms Ash.OneShot.CallableRuns.CaptureExample.source_enters_request
#print axioms Ash.OneShot.CallableRuns.CaptureExample.capture_run
