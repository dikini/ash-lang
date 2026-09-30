import CheckedEvents

/-!
Progress in the checked step relation itself. Current structural validity
constructs local annotations and fresh identities; no next-state certificate
or checked-step witness is a premise. This remains the finite-result fragment.
-/

namespace Ash.OneShot.CheckedProgress
open Instantiation ScopedExpressions ScopedExecution ScopedPorts CheckedEvents
open ScopedTyping (resourceWorld)
open DeclarationResults (signature)

theorem stable_step
    (event : StableEvent before.execution.configuration after discharged)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound) :
    CheckedStep declarations policy result outgoing bound registry before registry
      (ScopedPortJoint.advanceState before after [] discharged) := by
  obtain ⟨⟨configuration, issued, completed⟩, activations⟩ := before
  have fresh : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.joint.ledger.2
  have noEntry : enteredActivations configuration after = [] := by
    cases event with
    | value raw isValue =>
        exact value_enters_no_activation (ClauseJoint.current_closed_value valid isValue)
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
    (valid : ClauseJoint.Valid declarations policy registry ambient
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
          obtain ⟨record, checked⟩ := CaptureRecords.checked_capture_exists declared valid
          have noEntry : enteredActivations
              ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ after = [] := rfl
          exact Or.inr ⟨registry.insert owner record, _, .event (.capture checked) fresh
            (by simpa [noEntry] using valid.joint.names.unique)⟩

theorem resume_progress
    (valid : ClauseJoint.Valid declarations policy registry ambient
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
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ScopedPortProgress.OutwardRequest before.execution.configuration outgoing ∨
      ∃ next after, CheckedStep declarations policy result outgoing bound registry before next after := by
  obtain ⟨⟨⟨expression, scope, stack⟩, issued, completed⟩, activations⟩ := before
  obtain ⟨input, current, ports⟩ := effect_configuration_has_types valid.joint.effects
  have admitted : ClauseExecution.SupportedHead expression := by
    obtain ⟨environment, ticket, bound, scope, code, rest⟩ := valid.results
    exact ClauseExecution.supported_head code
  have form : ScopedPortProgress.CurrentForm expression := by
    cases current with
    | checked scopeTyped typed => exact ScopedPortProgress.typed_current_form typed
  have sameOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using valid.joint.ledger.2
  cases form with
  | value isValue =>
      have boundary := GenerativeProgress.value_boundary (configuration := ⟨expression, scope, stack⟩) isValue
      rcases ScopedPortJoint.checked_value_progress valid.joint isValue
        (ClauseExecution.return_access_checks valid.results boundary) with terminal | next
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
  | app | discard | cleanup => exact False.elim admitted

theorem closed_progress
    (valid : ClauseJoint.Valid declarations policy registry ambient before result [] bound) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ∃ next after, CheckedStep declarations policy result [] bound registry before next after := by
  rcases current_progress valid with terminal | outward | next
  · exact Or.inl terminal
  · obtain ⟨requested, operation, operand, same, isValue, exported, missing⟩ := outward
    cases exported
  · exact Or.inr next

theorem checked_progress_preserves
    (valid : ClauseJoint.Valid declarations policy registry ambient before result [] bound) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ∃ next after, CheckedStep declarations policy result [] bound registry before next after ∧
        NamedAccessStep ambient before after ∧
        ClauseJoint.Valid declarations policy next ambient after result [] bound ∧
        ClauseJoint.RegistryExtends registry next := by
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
    (valid : ClauseJoint.Valid declarations policy registry ambient before result [] bound) :
    ScopedPortProgress.Terminal after.execution.configuration ∨
      ∃ next successor, CheckedStep declarations policy result [] bound finalRegistry after next successor ∧
        CheckedRun declarations policy result [] bound registry before next successor ∧
        NamedAccessStep ambient after successor ∧
        ClauseJoint.Valid declarations policy next ambient successor result [] bound ∧
        ClauseJoint.RegistryExtends finalRegistry next := by
  have finalValid := (run_preserves run valid).2.1
  rcases checked_progress_preserves finalValid with terminal | ⟨next, successor, step, rest⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨next, successor, step, run_append run (.next step .refl), rest⟩

theorem initial_run_safety
    (typed : Typed (signature declarations) [] TypeEnv.empty .none [] expression result)
    (used : Uses policy .none .available expression .available)
    (support : Syntax.resourceDependencies expression.dependencies = [])
    (checked : ClauseResults.Derives declarations environment [] .none expression bound)
    (run : CheckedRun declarations policy result [] bound (fun _ => none)
      ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ finalRegistry after) :
    NamedAccessSteps [] ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ after ∧
      ClauseJoint.Valid declarations policy finalRegistry [] after result [] bound ∧
      (ScopedPortProgress.Terminal after.execution.configuration ∨
        ∃ next successor, CheckedStep declarations policy result [] bound finalRegistry after next successor ∧
          CheckedRun declarations policy result [] bound (fun _ => none)
            ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ next successor ∧
          NamedAccessStep [] after successor ∧
          ClauseJoint.Valid declarations policy next [] successor result [] bound ∧
          ClauseJoint.RegistryExtends finalRegistry next) := by
  have valid := ClauseJoint.initial_configuration_valid typed used support checked
  have preserved := run_preserves run valid
  exact ⟨preserved.1, preserved.2.1, run_progress run valid⟩

end Ash.OneShot.CheckedProgress

#print axioms Ash.OneShot.CheckedProgress.stable_step
#print axioms Ash.OneShot.CheckedProgress.named_value_checked
#print axioms Ash.OneShot.CheckedProgress.declared_capture_exists
#print axioms Ash.OneShot.CheckedProgress.request_progress
#print axioms Ash.OneShot.CheckedProgress.resume_progress

#print axioms Ash.OneShot.CheckedProgress.current_progress
#print axioms Ash.OneShot.CheckedProgress.closed_progress
#print axioms Ash.OneShot.CheckedProgress.checked_progress_preserves

#print axioms Ash.OneShot.CheckedProgress.run_append
#print axioms Ash.OneShot.CheckedProgress.run_progress
#print axioms Ash.OneShot.CheckedProgress.initial_run_safety
