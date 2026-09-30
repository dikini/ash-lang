import CaptureAnnotations

/-!
Structural typing of the annotations created by focus, handler entry and cell
entry. Premises inspect current code, its context and the existing tail. They
do not require successor configuration typing or combined validity.
-/

namespace Ash.OneShot.EntryAnnotations
open Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ScopedTyping (resourceWorld resource_world_append)
open DeclarationResults (signature)

inductive EntryTyping (ports : Signature) (tickets : EffectTickets) (world : List Nat)
    (result : Port) (outgoing : List Instance) :
    Configuration → Configuration → List Owner → Prop where
  | focus (position : Focus whole child plain.context)
      (scope : EffectScope tickets plain.scope ticket)
      (childTyped : Typed ports world TypeEnv.empty ticket effects child (eraseType plain.input))
      (contextTyped : ContextTyped ports world TypeEnv.empty ticket effects plain.context
        (eraseType plain.input) (eraseType plain.output))
      (tailTyped : StackTyped ports tickets.types world tail (eraseType plain.output) result)
      (tailEffects : EffectStack ports tickets world tail effects outgoing) :
      EntryTyping ports tickets world result outgoing
        ⟨whole, plain.scope, tail⟩ ⟨child, plain.scope, .push (.plain plain) tail⟩ []
  | handler
      (current : EffectAtType ports tickets world handler.scope
        (.handle (freezeEffect handler.effectInst) body handler.clauses) (eraseType handler.answer) effects)
      (tailTyped : StackTyped ports tickets.types world tail (eraseType handler.answer) result)
      (tailEffects : EffectStack ports tickets world tail effects outgoing) :
      EntryTyping ports tickets world result outgoing
        ⟨.handle (freezeEffect handler.effectInst) body handler.clauses, handler.scope, tail⟩
        ⟨body, handler.scope, .push (.handler handler) tail⟩ []
  | resource
      (current : EffectAtType ports tickets world scope
        (.resource binder (.integer payload) body) (eraseType answer) effects)
      (tailTyped : StackTyped ports tickets.types world tail (eraseType answer) result)
      (tailEffects : EffectStack ports tickets world tail effects outgoing) :
      EntryTyping ports tickets world result outgoing
        ⟨.resource binder (.integer payload) body, scope, tail⟩
        ⟨body.instantiate (Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) tail⟩ [.resource identity]

theorem entry_executes (entry : EntryTyping ports tickets world result outgoing before after created) :
    RawStep before after created [] := by
  cases entry with
  | focus position scope child context tail effects => exact .focus _ position _
  | handler => exact .enterHandler _ _ _
  | resource current tail effects =>
      cases current with
      | checked scope typed => exact .enterCell _ _ _ _ _ _ _ (typed_resource_closed typed)

theorem entry_boundary (entry : EntryTyping ports tickets world result outgoing before after created) :
    GenerativeProgress.NoSourceRequest before := by
  cases entry with
  | focus position => exact ClauseExecution.focus_boundary position
  | handler | resource =>
      exact GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)

theorem entry_registry_unchanged
    (entry : EntryTyping ports tickets world result outgoing before after created) :
    ScopedExecution.advanceUsageTickets policy registry after created = registry := by
  cases entry <;> rfl

theorem entry_effects
    (entry : EntryTyping ports tickets (resourceWorld issued) result outgoing before after created)
    (fresh : (issued ++ created).Nodup) :
    EffectConfigurationTyped ports tickets (resourceWorld (issued ++ created)) after result outgoing := by
  cases entry with
  | focus position scope child context tail effects =>
      simp only [List.append_nil]
      have frame := EffectFrame.plain scope context
      exact ⟨_, _, .checked scope child, .push (effect_frame_has_types frame) tail,
        .push frame effects (List.Subset.refl _)⟩
  | @handler body effects tail handler current tailTyped tailEffects =>
      simp only [List.append_nil]
      generalize sourceEq : freezeEffect handler.effectInst = source at current
      cases current with
      | checked scope typed => cases typed with
          | handle bodyTyped clauses coverage unique available =>
              have same := freeze_effect_injective sourceEq
              rw [← same] at bodyTyped clauses coverage
              have frame := EffectFrame.handler (handler := handler) ⟨_, scope⟩ clauses coverage unique
              exact ⟨_, _, .checked scope bodyTyped, .push (effect_frame_has_types frame) tailTyped,
                .push frame (effect_stack_input_weaken tailEffects available) (List.Subset.refl _)⟩
  | @resource scope binder payload body answer effects tail identity current tailTyped tailEffects =>
      have unused : Owner.resource identity ∉ issued := by
        intro member
        exact (List.nodup_append.mp fresh).2.2 (.resource identity) member (.resource identity) (by simp) rfl
      have larger : resourceWorld issued ⊆ resourceWorld (issued ++ [.resource identity]) := by
        rw [resource_world_append]; exact List.subset_append_left _ _
      cases current with
      | checked scopeTyped typed =>
          obtain ⟨residual, opened, noEscape, noEffectEscape, available⟩ := resource_body_typed_at_fresh typed unused
          have frame : EffectFrame ports tickets (resourceWorld (issued ++ [.resource identity]))
              (.cell identity payload scope answer) (.cell identity :: residual) residual :=
            .cell ⟨_, scopeTyped⟩ noEscape
          exact ⟨_, _, .checked scopeTyped opened,
            .push (effect_frame_has_types frame) (stack_world_weaken tailTyped larger),
            .push frame (effect_stack_input_weaken (effect_stack_world_weaken tailEffects larger) available)
              (List.Subset.refl _)⟩

theorem entry_preserves
    (entry : EntryTyping (signature declarations) registry.joint.effects (resourceWorld before.execution.issued)
      result outgoing before.execution.configuration after created)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound)
    (fresh : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup) :
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after created []) ∧
      ClauseJoint.Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after created []) result outgoing bound := by
  have raw := entry_executes entry
  have boundary := entry_boundary entry
  have checks := ClauseExecution.return_access_checks (ambient := ambient) valid.results boundary
  have step : NamedAccessStep ambient before (ScopedPortJoint.advanceState before after created []) :=
    ⟨.event before after created [] raw fresh freshHandlers, checks⟩
  obtain ⟨ledger, names, support⟩ := named_access_step_preserves step valid.joint.ledger valid.joint.names valid.joint.support
  have history := ScopedPortJoint.usage_history_iff.mpr valid.joint.registry
  have usage := raw_step_preserves_configuration_usage raw
    (usage_checks_from_allocation_and_access history fresh checks) valid.joint.usage
  have nextHistory := raw_step_preserves_usage_registry_history (policy := policy) raw history
  rw [entry_registry_unchanged entry] at usage nextHistory
  refine ⟨step, ⟨ledger, names, support, ?_, usage, ScopedPortJoint.usage_history_iff.mp nextHistory,
    raw_step_preserves_resource_closure raw valid.joint.closed⟩, ?_⟩
  · exact entry_effects entry fresh
  · exact ClauseExecution.raw_preserves_results raw fresh valid.results boundary

theorem focus_annotations_exist
    (typed : EffectConfigurationTyped ports tickets world ⟨whole, scope, tail⟩ result outgoing)
    (position : Focus whole child context) :
    ∃ plain : PlainData, plain.context = context ∧ plain.scope = scope ∧
      EntryTyping ports tickets world result outgoing
        ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩ [] := by
  obtain ⟨input, effects, current, tailTyped, tailEffects⟩ := typed
  cases current with
  | checked scopeTyped expression =>
      obtain ⟨plain, raw, childTyped, contextTyped, output, shape, savedScope⟩ :=
        typed_focus_progress position expression
          (scope_typed_names_match (effect_scope_has_types scopeTyped)) tail
      refine ⟨plain, shape, savedScope, ?_⟩
      have checked : EntryTyping ports tickets world result outgoing
          ⟨whole, plain.scope, tail⟩ ⟨child, plain.scope, .push (.plain plain) tail⟩ [] :=
        .focus (by rw [shape]; exact position) (by rw [savedScope]; exact scopeTyped)
          childTyped (by rw [output]; exact contextTyped) (by rw [output]; exact tailTyped) tailEffects
      simpa [savedScope] using checked

theorem handler_annotations_exist
    (typed : EffectConfigurationTyped ports tickets world
      ⟨.handle effect body clauses, scope, tail⟩ result outgoing) (activation : Nat) :
    ∃ handler : HandlerData, handler.activation = activation ∧
      EntryTyping ports tickets world result outgoing
        ⟨.handle effect body clauses, scope, tail⟩ ⟨body, scope, .push (.handler handler) tail⟩ [] := by
  obtain ⟨input, effects, current, tailTyped, tailEffects⟩ := typed
  cases current with
  | checked scopeTyped expression => cases expression with
      | @handle _ _ _ effect _ _ _ _ _ bodyTyped clausesTyped coverage unique available =>
          let handler : HandlerData := ⟨activation, effect, clauses, scope, embedPort input,
            clauses_have_ticket_barrier clausesTyped⟩
          refine ⟨handler, rfl, ?_⟩
          have checked : EntryTyping ports tickets world result outgoing
              ⟨.handle (freezeEffect handler.effectInst) body handler.clauses, handler.scope, tail⟩
              ⟨body, handler.scope, .push (.handler handler) tail⟩ [] :=
            .handler (by simpa [handler] using (EffectAtType.checked scopeTyped
              (Typed.handle bodyTyped clausesTyped coverage unique available)))
              (by simpa [handler] using tailTyped) tailEffects
          exact checked

theorem resource_annotations_exist
    (typed : EffectConfigurationTyped ports tickets world
      ⟨.resource binder (.integer payload) body, scope, tail⟩ result outgoing) (identity : Nat) :
    ∃ answer : Ty, EntryTyping ports tickets world result outgoing
      ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] := by
  obtain ⟨input, effects, current, tailTyped, tailEffects⟩ := typed
  exact ⟨embedPort input, .resource (by simpa using current) (by simpa using tailTyped) tailEffects⟩

end Ash.OneShot.EntryAnnotations

#print axioms Ash.OneShot.EntryAnnotations.entry_executes
#print axioms Ash.OneShot.EntryAnnotations.entry_boundary
#print axioms Ash.OneShot.EntryAnnotations.entry_registry_unchanged
#print axioms Ash.OneShot.EntryAnnotations.entry_effects
#print axioms Ash.OneShot.EntryAnnotations.entry_preserves
#print axioms Ash.OneShot.EntryAnnotations.focus_annotations_exist
#print axioms Ash.OneShot.EntryAnnotations.handler_annotations_exist
#print axioms Ash.OneShot.EntryAnnotations.resource_annotations_exist
