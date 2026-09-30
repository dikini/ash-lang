import ScopedPortEffects

/-!
Connected port/effect preservation for actual capture, builtin requests,
closed-value completion and ordinary computation. Value support, ownership
and continuation permissions remain independently checked properties.
-/

namespace Ash.OneShot.ScopedPorts
open Syntax Instantiation ScopedExpressions ScopedExecution
open ScopedTyping (World handler_cut_instance clause_at_of_key cell_selection_of_resolution
  builtin_resolution_instance handler_selection_of_resolution)

def withCellSignatures (users : Signature) : Signature
  | .cell identity, 0 => some (.reference identity, .integer)
  | .cell identity, 1 => some (.product (.reference identity) .integer, .unit)
  | .cell _, _ => none
  | effectInst@(.user _ _), operation => users effectInst operation

theorem typed_reference_value
    (typed : Typed signature world TypeEnv.empty ticket allowed value (.reference identity))
    (isValue : value.IsValue) : value = .resourceRef (.activation identity) := by
  cases typed <;> simp_all [Code.IsValue]

theorem typed_product_value
    (typed : Typed signature world TypeEnv.empty ticket allowed value (.product leftType rightType))
    (isValue : value.IsValue) :
    ∃ left right, value = .pair left right ∧ left.IsValue ∧ right.IsValue ∧
      Typed signature world TypeEnv.empty ticket allowed left leftType ∧
      Typed signature world TypeEnv.empty ticket allowed right rightType := by
  cases typed <;> simp_all [Code.IsValue]
  exact ⟨_, _, ⟨rfl, rfl⟩, isValue.1, isValue.2, by assumption, by assumption⟩

theorem cell_update_preserves_stack_typing
    (update : CellUpdate identity old new before after)
    (typed : StackTyped signature tickets world before input result) :
    StackTyped signature tickets world after input result := by
  induction update generalizing input result with
  | hit => cases typed with
      | push frame rest => cases frame with
          | cell caller noEscape => exact .push (.cell caller noEscape) rest
  | push miss next ih => cases typed with
      | push frame rest => exact .push frame (ih rest)
  | live next ih => cases typed with
      | live known caller saved rest => exact .live known caller saved (ih rest)
  | spent next ih => cases typed with
      | spent known caller rest => exact .spent known caller (ih rest)

theorem cell_update_preserves_effect_stack
    (update : CellUpdate identity old new before after)
    (typed : EffectStack signature tickets world before incoming outgoing) :
    EffectStack signature tickets world after incoming outgoing := by
  induction update generalizing incoming with
  | hit => cases typed with
      | push frame rest bound => cases frame with
          | cell scope noEscape => exact .push (.cell scope noEscape) rest bound
  | push miss next ih => cases typed with
      | push frame rest bound => exact .push frame (ih rest) bound
  | live next ih => cases typed with
      | live known scope saved rest resume close bound => exact .live known scope saved (ih rest) resume close bound
  | spent next ih => cases typed with
      | spent known scope rest bound => exact .spent known scope (ih rest) bound

theorem cell_read_preserves_effect_configuration
    (typed : EffectConfigurationTyped (withCellSignatures users) tickets world
      ⟨.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before⟩ result outgoing)
    (selected : CellUpdate identity payload payload before after) :
    EffectConfigurationTyped (withCellSignatures users) tickets world ⟨.integer payload, scope, after⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
          obtain ⟨input, operation, available, operand⟩ := typed_perform_inversion expression
          simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
          obtain ⟨rfl, rfl⟩ := operation
          exact ⟨.integer, [], .checked scopeTyped .integer, cell_update_preserves_stack_typing selected stack,
            effect_stack_input_weaken (cell_update_preserves_effect_stack selected effectStack) (by simp)⟩

theorem cell_write_preserves_effect_configuration
    (typed : EffectConfigurationTyped (withCellSignatures users) tickets world
      ⟨.perform (freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before⟩ result outgoing)
    (selected : CellUpdate identity old new before after) :
    EffectConfigurationTyped (withCellSignatures users) tickets world ⟨.unit, scope, after⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
          obtain ⟨input, operation, available, operand⟩ := typed_perform_inversion expression
          simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
          obtain ⟨rfl, rfl⟩ := operation
          exact ⟨.unit, [], .checked scopeTyped .unit, cell_update_preserves_stack_typing selected stack,
            effect_stack_input_weaken (cell_update_preserves_effect_stack selected effectStack) (by simp)⟩


/-- Capture chooses its contract from the selected handler interface. Scoped
    substitution supplies lexical readiness without a source-slot freshness
    side condition. Permissions and disposal readiness are separate checks. -/
theorem capture_constructs_effect_configuration
    (cut : HandlerCut requested whole cap tail handler)
    (typed : EffectConfigurationTyped signature tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result outgoing)
    (isValue : operand.IsValue) (fresh : tickets owner = none) :
    ∃ (parameter binder : Nat) (body : Code) (output : Port) (residual : List Instance),
      let contract : ContinuationContract := ⟨output, eraseType handler.answer, residual, residual⟩
      let extended := tickets.insert owner contract
      RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer cap handler.scope tail⟩ [.ticket owner] [] ∧
      EffectExtension tickets extended ∧
      EffectConfigurationTyped signature extended world
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer cap handler.scope tail⟩ result outgoing := by
  obtain ⟨output, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, operationType, available, operandTyped⟩ := typed_perform_inversion expression
      have closed := typed_value_closed operandTyped isValue
      obtain ⟨residual, capturedEffects, outsideEffects, handlerEffects⟩ := handler_cut_effect_decomposition cut effectStack
      obtain ⟨capturedTypes, outsideTypes, handlerTypes⟩ := handler_cut_retains_typing cut stack
      cases handlerEffects with
      | handler caller clauses coverage unique =>
          have operationAtHandler := operationType
          rw [← handler_cut_instance cut] at operationAtHandler
          obtain ⟨parameter, binder, body, selected⟩ := clause_at_of_key (coverage _ _ _ operationAtHandler)
          obtain ⟨clauseInput, clauseOutput, clauseSignature, bodyTyped⟩ := selected_clause_typed selected clauses
          let contract : ContinuationContract := ⟨output, eraseType handler.answer, residual, residual⟩
          let extended := tickets.insert owner contract
          have extension : EffectExtension tickets extended := effect_ticket_insertion_extends fresh
          have newTicket : extended owner = some contract := by simp [extended, EffectTickets.insert]
          have typeExtension := effect_extension_has_type_extension extension
          have newTypes : extended.types owner = some (output, eraseType handler.answer) := by
            simp [EffectTickets.types, newTicket, contract]
          refine ⟨parameter, binder, body, output, residual,
            .capture requested operation parameter binder owner operand body scope whole cap tail handler (embedPort output)
              cut selected closed (typed_suffix_ready bodyTyped),
            extension, eraseType handler.answer, residual, ?_, ?_, ?_⟩
          · exact .checked (.bound newTicket)
              (selected_clause_substitution_typed selected clauses operationAtHandler operandTyped closed)
          · exact .live (by simpa using newTypes) (effect_scope_known_has_types (effect_scope_known_extension caller extension))
              (by simpa using stack_typed_extension capturedTypes typeExtension) (stack_typed_extension outsideTypes typeExtension)
          · exact .live newTicket (effect_scope_known_extension caller extension)
              (effect_stack_extension capturedEffects extension) (effect_stack_extension outsideEffects extension)
              (fun _ used => used) (fun _ used => used) (fun _ used => used)

theorem builtin_effect_progress
    (typed : EffectConfigurationTyped (withCellSignatures users) tickets world
      ⟨.perform (freezeEffect (.cell identity)) operation operand, scope, stack⟩ result outgoing)
    (isValue : operand.IsValue)
    (resolved : stack.erase.resolve (.cell identity) = some (.builtin identity)) :
    ∃ after, RawStep ⟨.perform (freezeEffect (.cell identity)) operation operand, scope, stack⟩ after [] [] ∧
      EffectConfigurationTyped (withCellSignatures users) tickets world after result outgoing := by
  obtain ⟨old, update⟩ := cell_selection_of_resolution stack resolved
  obtain ⟨answer, effects, expression, retained, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, known, available, operandTyped⟩ := typed_perform_inversion expression
      cases operation with
      | zero =>
          simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at known
          obtain ⟨rfl, rfl⟩ := known
          obtain rfl := typed_reference_value operandTyped isValue
          obtain ⟨after, selected⟩ := update old
          exact ⟨_, .readCell identity old scope stack after selected,
            cell_read_preserves_effect_configuration ⟨_, effects, .checked scopeTyped expression, retained, effectStack⟩ selected⟩
      | succ operation => cases operation with
          | zero =>
              simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at known
              obtain ⟨rfl, rfl⟩ := known
              obtain ⟨reference, value, rfl, referenceValue, numberValue, referenceTyped, numberTyped⟩ :=
                typed_product_value operandTyped isValue
              obtain rfl := typed_reference_value referenceTyped referenceValue
              obtain ⟨new, rfl⟩ := typed_integer_value numberTyped numberValue
              obtain ⟨after, selected⟩ := update new
              exact ⟨_, .writeCell identity old new scope stack after selected,
                cell_write_preserves_effect_configuration ⟨_, effects, .checked scopeTyped expression, retained, effectStack⟩ selected⟩
          | succ operation => cases known

/-- Relative request progress derives executable selection and preserves both
    value and connected effect typing. The combined theorem takes a fresh historical slot; only its
    source-capture branch uses that premise; ownership freshness and permissions remain separate.
    The observation alternative requires absence of a local interpretation. -/
theorem request_effect_progress
    (typed : EffectConfigurationTyped (withCellSignatures users) tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ result outgoing)
    (isValue : operand.IsValue) (fresh : tickets owner = none) :
    (requested ∈ outgoing ∧ stack.erase.resolve requested = none) ∨
      ∃ next after created,
        RawStep ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ after created [] ∧
        EffectExtension tickets next ∧
        EffectConfigurationTyped (withCellSignatures users) next world after result outgoing := by
  cases resolved : stack.erase.resolve requested with
  | none =>
      rcases current_request_is_interpreted_or_exported typed with ⟨target, found⟩ | exported
      · simp [resolved] at found
      · exact Or.inl ⟨exported, rfl⟩
  | some target => cases target with
      | builtin identity =>
          obtain rfl := builtin_resolution_instance stack resolved
          obtain ⟨after, step, afterTyped⟩ := builtin_effect_progress typed isValue resolved
          exact Or.inr ⟨tickets, after, [], step, fun _ _ known => known, afterTyped⟩
      | source activation =>
          obtain ⟨cap, outside, handler, cut, active⟩ := handler_selection_of_resolution stack resolved
          obtain ⟨parameter, binder, body, output, residual, step, extension, afterTyped⟩ :=
            capture_constructs_effect_configuration cut typed isValue fresh
          exact Or.inr ⟨_, _, [.ticket owner], step, extension, afterTyped⟩

/-- A request with a value operand and no outward effects takes an actual step.
    This is the request case, not yet progress for every expression or a theorem
    about the joint ownership/access/permission admission judgment. -/
theorem closed_request_effect_progress
    (typed : EffectConfigurationTyped (withCellSignatures users) tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ result [])
    (isValue : operand.IsValue) (fresh : tickets owner = none) :
    ∃ next after created,
      RawStep ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ after created [] ∧
      EffectExtension tickets next ∧
      EffectConfigurationTyped (withCellSignatures users) next world after result [] := by
  rcases request_effect_progress typed isValue fresh with ⟨impossible, missing⟩ | next
  · cases impossible
  · exact next

theorem effect_value_transport (typed : EffectAtType signature tickets world scope value type effects)
    (isValue : value.IsValue) (destination : EffectScopeKnown tickets otherScope) (newEffects : List Instance) :
    EffectAtType signature tickets world otherScope value type newEffects := by
  obtain ⟨ticket, scopeTyped⟩ := destination
  cases typed with
  | checked oldScope typed => exact .checked scopeTyped (typed_value_transport typed isValue ticket newEffects)

theorem effect_value_closed_type (typed : EffectAtType signature tickets world scope value type effects)
    (isValue : value.IsValue) : Typed signature world TypeEnv.empty .none [] value type := by
  cases typed with
  | checked scope typed => exact typed_value_transport typed isValue .none []

/-- Every raw closed-value transition preserves both actual retained-code
    types and their connected effect interfaces. Ownership and use admission
    remain independent obligations. -/
theorem raw_value_step_preserves_effect_configuration
    (step : RawStep before after created discharged) (closed : ClosedValue before.expression)
    (typed : EffectConfigurationTyped signature tickets world before result outgoing) :
    EffectConfigurationTyped signature tickets world after result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases step with
  | focus plain focus tail => exact False.elim (focus_is_not_value focus closed.1)
  | bind | beta | ifTrue | ifFalse | enterHandler | enterCell | enterCleanup
  | capture | resume | discard | readCell | writeCell => cases closed.1
  | plug plain value valueClosed scope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | plain scopeTyped context =>
                  have operand := effect_value_closed_type expression valueClosed.1
                  exact ⟨_, _, .checked scopeTyped (context_plug_typed context
                    (typed_value_transport operand valueClosed.1 _ _)), rest, effectRest⟩
  | leaveHandler handler value valueClosed scope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | handler caller clauses coverage unique =>
                  exact ⟨_, _, effect_value_transport expression valueClosed.1 caller _, rest, effectRest⟩
  | leaveCell identity payload answer savedScope scope value valueClosed tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | cell caller noEscape =>
                  exact ⟨_, _, effect_value_transport expression valueClosed.1 caller _, rest, effectRest⟩
  | startCleanup action saved savedClosed scope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | armed caller callable requests =>
                  have savedTyped := effect_value_closed_type expression savedClosed.1
                  exact ⟨.unit, _, .checked .none (.app
                    (typed_value_transport callable action.closed.1 .none _) .unit requests),
                    .push (.running (effect_scope_known_has_types caller) callable savedTyped) rest,
                    .push (.running caller callable savedTyped requests) effectRest (fun _ used => used)⟩
  | finishCleanup action saved savedClosed scope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | running caller callable savedTyped requests =>
                  obtain ⟨ticket, caller⟩ := caller
                  exact ⟨_, _, .checked caller (typed_value_transport savedTyped savedClosed.1 ticket _), rest, effectRest⟩
  | leaveClause owner answer value valueClosed scope callerScope tail => cases stack with
      | spent known caller rest => cases effectStack with
          | spent actual effectCaller effectRest bound =>
              exact ⟨_, _, effect_value_transport expression valueClosed.1 effectCaller _, rest, effectRest⟩
  | finishClose identity scope callerScope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | closing caller =>
                  exact ⟨_, _, effect_value_transport expression closed.1 caller _, rest, effectRest⟩
  | retire owner scope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | retiring known => cases expression with
                  | checked scopeTyped typed =>
                      exact ⟨.unit, _, .checked scopeTyped (typed_value_transport typed closed.1 _ _), rest, effectRest⟩

theorem bind_preserves_effect_configuration
    (typed : EffectConfigurationTyped signature tickets world ⟨.bind parameter value body, scope, tail⟩ result outgoing)
    (isValue : value.IsValue) :
    EffectConfigurationTyped signature tickets world ⟨body.subst parameter value, scope, tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | bind initializer suffix =>
          exact ⟨input, effects, .checked scopeTyped
            (typed_substitution suffix (typed_value_transport initializer isValue .none [])
              (typed_value_closed initializer isValue)), stack, effectStack⟩

theorem beta_preserves_effect_configuration
    (typed : EffectConfigurationTyped signature tickets world ⟨.app (.lambda parameter body) value, scope, tail⟩ result outgoing)
    (isValue : value.IsValue) :
    EffectConfigurationTyped signature tickets world ⟨body.subst parameter value, .none, tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | app function argument available => cases function with
          | lambda bodyTyped formed =>
              exact ⟨input, _, .checked .none
                (typed_substitution bodyTyped (typed_value_transport argument isValue .none [])
                  (typed_value_closed argument isValue)), stack, effect_stack_input_weaken effectStack available⟩


/-- Capture constructs a single event with connected typing, ledger and live
    support. Actual capture access and issued-owner freshness are explicit. -/
theorem capture_constructs_effects_ledger_support
    (cut : HandlerCut requested whole cap tail handler)
    (typed : EffectConfigurationTyped signature tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result outgoing)
    (isValue : operand.IsValue) (freshTicket : tickets owner = none)
    (freshOwners : (issued ++ [.ticket owner]).Nodup)
    (ledger : Ledger (RunState.erase ⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩))
    (support : AccessValid ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ ambient)
    (checks : AccessChecks ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ ambient) :
    ∃ (parameter binder : Nat) (body : Code) (output : Port) (residual : List Instance),
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer cap handler.scope tail⟩
      let extended := tickets.insert owner ⟨output, eraseType handler.answer, residual, residual⟩
      RunStep ⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩
        ⟨after, issued ++ [.ticket owner], completed⟩ ∧
      EffectExtension tickets extended ∧
      EffectConfigurationTyped signature extended world after result outgoing ∧
      Ledger (RunState.erase ⟨after, issued ++ [.ticket owner], completed⟩) ∧ AccessValid after ambient := by
  obtain ⟨parameter, binder, body, output, residual, raw, extension, afterTyped⟩ :=
    capture_constructs_effect_configuration cut typed isValue freshTicket
  have step := RunStep.event
    ⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩
    _ [.ticket owner] [] raw freshOwners
  exact ⟨parameter, binder, body, output, residual, step, extension, afterTyped,
    run_step_preserves_ledger step ledger, raw_step_preserves_access raw support checks⟩

namespace StepExamples
open ScopedSignatureGap.Examples
open Ash.OneShot.ScopedPorts.Examples (signature)
open RetainedExamples (afterResume)

theorem capture_has_connected_successor :
    ∃ (parameter binder : Nat) (body : Code) (output : Port) (residual : List Instance),
      let extended := EffectTickets.insert (fun _ => none) 7 ⟨output, eraseType handler.answer, residual, residual⟩
      RawStep RetainedExamples.beforeRequest
        ⟨body.subst parameter (payload (.activation 0)), .ticket binder 7,
          .live 7 (embedPort output) handler.answer capture handler.scope outside⟩ [.ticket 7] [] ∧
      EffectExtension (fun _ => none) extended ∧
      EffectConfigurationTyped signature extended [0]
        ⟨body.subst parameter (payload (.activation 0)), .ticket binder 7,
          .live 7 (embedPort output) handler.answer capture handler.scope outside⟩ .unit [] :=
  capture_constructs_effect_configuration actual_boundary_supports_payload.1 EffectExamples.request_connected trivial rfl

theorem completion_states_connected :
    EffectConfigurationTyped signature EffectExamples.records [0] ⟨.unit, .none, .spent 7 .unit .none outside⟩ .unit [] ∧
    EffectConfigurationTyped signature EffectExamples.records [0] ⟨.unit, .none, outside⟩ .unit [] ∧
    EffectConfigurationTyped signature EffectExamples.records [0] ⟨.unit, .none, .nil⟩ .unit [] := by
  have closed : ClosedValue Code.unit := ScopedExecution.Examples.unit_closed
  have first := raw_value_step_preserves_effect_configuration
    (RawStep.leaveHandler handler .unit closed (.ticket 9 7) (.spent 7 .unit .none outside))
    closed EffectExamples.resumed_connected
  have second := raw_value_step_preserves_effect_configuration
    (RawStep.leaveClause 7 .unit .unit closed .none .none outside) closed first
  have last := raw_value_step_preserves_effect_configuration
    (RawStep.leaveCell 0 41 .unit .none .none .unit closed .nil) closed second
  exact ⟨first, second, last⟩

end StepExamples

end Ash.OneShot.ScopedPorts

#print axioms Ash.OneShot.ScopedPorts.typed_reference_value
#print axioms Ash.OneShot.ScopedPorts.typed_product_value
#print axioms Ash.OneShot.ScopedPorts.cell_update_preserves_stack_typing
#print axioms Ash.OneShot.ScopedPorts.cell_update_preserves_effect_stack
#print axioms Ash.OneShot.ScopedPorts.cell_read_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedPorts.cell_write_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedPorts.capture_constructs_effect_configuration
#print axioms Ash.OneShot.ScopedPorts.builtin_effect_progress
#print axioms Ash.OneShot.ScopedPorts.request_effect_progress
#print axioms Ash.OneShot.ScopedPorts.closed_request_effect_progress
#print axioms Ash.OneShot.ScopedPorts.effect_value_transport
#print axioms Ash.OneShot.ScopedPorts.effect_value_closed_type
#print axioms Ash.OneShot.ScopedPorts.raw_value_step_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedPorts.bind_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedPorts.beta_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedPorts.capture_constructs_effects_ledger_support
#print axioms Ash.OneShot.ScopedPorts.StepExamples.capture_has_connected_successor
#print axioms Ash.OneShot.ScopedPorts.StepExamples.completion_states_connected
