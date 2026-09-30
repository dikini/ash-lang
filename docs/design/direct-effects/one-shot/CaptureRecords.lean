import EntryAnnotations

/-!
Supplied capture records are checked against before-state code and control.
The record update is explicit, so finite preservation can follow one registry
sequence without assuming validity at any successor.
-/

namespace Ash.OneShot.CaptureRecords
open Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ScopedTyping (resourceWorld resource_world_append)
open DeclarationResults (signature)

def makeRecord (policy : Syntax.TicketPolicy) (binder : Nat) (output : Port) (answer : Ty)
    (residual : List Instance) (inputBound answerBound : List Nat)
    (finite : ClauseResults.PortBound output inputBound) : ClauseJoint.TicketRecord :=
  ⟨⟨⟨output, eraseType answer, residual, residual⟩, policy binder⟩, ⟨inputBound, answerBound⟩, finite⟩

inductive CheckedCapture (declarations : DeclarationRegistry) (policy : Syntax.TicketPolicy)
    (registry : ClauseJoint.Registry) (world : List Nat) (result : Port)
    (outgoing : List Instance) (bound : List Nat) :
    Configuration → Configuration → Nat → ClauseJoint.TicketRecord → Prop where
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
      (handlerScope : ClauseFrames.ScopeBound registry.results handler.scope savedTicket)
      (clauses : ClauseResults.HandlerResults declarations environment world handler answerBound)
      (savedResults : ClauseFrames.StackReturns declarations registry.results world capture inputBound answerBound)
      (outsideResults : ClauseFrames.StackReturns declarations registry.results world tail answerBound bound) :
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
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound)
    (fresh : (before.execution.issued ++ [Owner.ticket owner]).Nodup) :
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) ∧
      ClauseJoint.Valid declarations policy (registry.insert owner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket owner] []) result outgoing bound ∧
      ClauseJoint.RegistryExtends registry (registry.insert owner record) := by
  have raw := checked_capture_executes event
  have resultFresh := ClauseJoint.result_registry_fresh valid fresh
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
            simp [extended, ClauseJoint.Registry.insert, ClauseJoint.Registry.joint, ScopedPortJoint.Registry.effects]
          have recordedTypes : extended.joint.effects.types owner = some (output, eraseType handler.answer) := by
            simp [EffectTickets.types, recorded, record, makeRecord]
          have resultExtension : ClauseFrames.RegistryExtends registry.results extended.results := by
            simpa [extended] using ClauseFrames.insert_extends (record := record.results) resultFresh
          have recordedResults : extended.results owner = some record.results := by
            simp [extended, ClauseJoint.Registry.insert, ClauseJoint.Registry.results]
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
                ClauseResults.selected_clause_substitution selected clauses handlerKnown operandTyped closed.1
              have sameBound : resumeBound = inputBound := (Option.some.inj (outputFinite.symm.trans finite))
              subst resumeBound
              have resultsAfter : ClauseFrames.ConfigurationReturns declarations extended.results
                  (resourceWorld issued) after bound := by
                refine ⟨_, _, answerBound, .bound recordedResults, substituted, ?_⟩
                exact .live recordedResults (ClauseFrames.scope_extends handlerScope resultExtension)
                  (ClauseFrames.stack_registry_extends savedResults resultExtension) (List.Subset.refl _)
                  (ClauseFrames.stack_registry_extends outsideResults resultExtension)
              have checks := PayloadBoundary.request_access_checks valid
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
                ClauseJoint.registry_insert_extends (ClauseJoint.registry_fresh valid fresh)⟩
              · simpa [before, after, extended, record, ScopedPortJoint.advanceState, resource_world_append, resourceWorld] using effectsAfter
              · simpa [before, after, extended, record, ScopedPortJoint.advanceState, resource_world_append, resourceWorld] using resultsAfter

theorem checked_capture_exists
    (event : CaptureAnnotations.DeclaredCapture declarations before.execution.configuration after owner)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound) :
    ∃ record, CheckedCapture declarations policy registry (resourceWorld before.execution.issued) result outgoing bound
      before.execution.configuration after owner record := by
  obtain ⟨⟨configuration, issued, completed⟩, activations⟩ := before
  cases event with
  | @capture requested whole capture tail handler operation parameter binder body input annotation operand scope owner
      cut selected known closed ready =>
      obtain ⟨currentPort, effects, current, stackPorts, stackEffects⟩ := valid.joint.effects
      obtain ⟨environment, ticket, currentBound, scopeChecked, code, stackResults⟩ := valid.results
      obtain ⟨savedEnvironment, savedTicket, answerBound, handlerScope, clauses, savedResults, outsideResults⟩ :=
        ClauseFrames.handler_cut_certificate cut stackResults
      obtain ⟨residual, savedEffects, outsideEffects, handlerEffects⟩ := handler_cut_effect_decomposition cut stackEffects
      obtain ⟨savedPorts, outsidePorts, handlerPorts⟩ := handler_cut_retains_typing cut stackPorts
      cases current with
      | checked scopeTyped typed =>
          obtain ⟨actualInput, actualKnown, available, operandTyped⟩ := typed_perform_inversion typed
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans actualKnown))
          have handlerKnown := known
          rw [← ScopedTyping.handler_cut_instance cut] at handlerKnown
          obtain ⟨argumentPort, resultPort, argumentBound, inputBound, actual, inputFinite, outputFinite, bodyChecked⟩ :=
            ClauseResults.selected_clause selected clauses
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (handlerKnown.symm.trans actual))
          have canonical := CaptureAnnotations.finite_annotation outputFinite rfl
          have narrowedEffects : EffectStack (signature declarations) registry.joint.effects (resourceWorld issued)
              capture [requested] residual := effect_stack_input_weaken savedEffects
                (by intro effect member; obtain rfl := List.mem_singleton.mp member; exact available)
          have narrowedResults := ClauseFrames.stack_input_weaken savedResults
            (ClauseFrames.declared_output_included code known outputFinite)
          refine ⟨makeRecord policy binder (eraseType annotation) handler.answer residual inputBound answerBound outputFinite, ?_⟩
          have checked := CheckedCapture.capture (policy := policy) (scope := scope) (owner := owner) cut selected known closed ready
            outputFinite handlerEffects narrowedEffects outsideEffects savedPorts outsidePorts handlerScope clauses
            narrowedResults outsideResults
          simpa only [← canonical] using checked

end Ash.OneShot.CaptureRecords

#print axioms Ash.OneShot.CaptureRecords.checked_capture_executes
#print axioms Ash.OneShot.CaptureRecords.checked_capture_declared
#print axioms Ash.OneShot.CaptureRecords.checked_capture_preserves
#print axioms Ash.OneShot.CaptureRecords.checked_capture_exists
