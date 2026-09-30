import ScopedEntries

/-!
Connected effect interfaces for the actual scoped interpretation stack.
Each frame checks its retained code at its own interface; live records also
check the dormant capture and its historical continuation contract. The
ordered stack determines lookup. Effect rows bound requests, not stack order.
-/

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (Signature TypeEnv TicketType EffectTickets ContinuationContract EffectScope EffectScopeKnown
  effect_scope_has_types effect_scope_known_has_types EffectExtension effect_ticket_insertion_extends
  effect_extension_has_type_extension effect_scope_extension effect_scope_known_extension withCellSignatures)

inductive EffectFrame (signature : Signature) (tickets : EffectTickets) (world : World) :
    ExecFrame → List Instance → List Instance → Prop where
  | plain (scope : EffectScope tickets data.scope ticket)
      (code : ContextTyped signature world TypeEnv.empty ticket effects data.context data.input data.output) :
      EffectFrame signature tickets world (.plain data) effects effects
  | handler (scope : EffectScopeKnown tickets handler.scope)
      (clauses : ClausesTyped signature world TypeEnv.empty handler.effectInst handler.answer residual handler.clauses)
      (coverage : Covers signature handler.effectInst handler.clauses)
      (unique : (clauseKeys handler.clauses).Nodup) :
      EffectFrame signature tickets world (.handler handler) (handler.effectInst :: residual) residual
  | cell (scope : EffectScopeKnown tickets runtimeScope) (noEscape : identity ∉ answer.resources) :
      EffectFrame signature tickets world (.cell identity payload runtimeScope answer) (.cell identity :: residual) residual
  | armed (scope : EffectScopeKnown tickets action.scope)
      (callable : Typed signature world TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests retained)) (requests : action.requests ⊆ effects) :
      EffectFrame signature tickets world (.armed action) effects effects
  | running (scope : EffectScopeKnown tickets action.scope)
      (callable : Typed signature world TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests retained))
      (result : Typed signature world TypeEnv.empty .none [] saved action.answer)
      (requests : action.requests ⊆ effects) :
      EffectFrame signature tickets world (.running action saved closed) effects effects
  | closing (scope : EffectScopeKnown tickets runtimeScope) :
      EffectFrame signature tickets world (.closing identity runtimeScope) effects effects
  | retiring (known : tickets owner = some contract) :
      EffectFrame signature tickets world (.retiring owner) effects effects

theorem effect_frame_has_types (frame : EffectFrame signature tickets world entry incoming outgoing) :
    FrameTyped signature tickets.types world entry := by
  cases frame with
  | plain scope code => exact .plain (effect_scope_has_types scope) code
  | handler scope clauses coverage unique => exact .handler (effect_scope_known_has_types scope) clauses coverage unique
  | cell scope noEscape => exact .cell (effect_scope_known_has_types scope) noEscape
  | armed scope callable requests => exact .armed (effect_scope_known_has_types scope) callable
  | running scope callable result requests => exact .running (effect_scope_known_has_types scope) callable result
  | closing scope => exact .closing (effect_scope_known_has_types scope)
  | retiring known => exact .retiring (by simp [EffectTickets.types, known]; exact ⟨rfl, rfl⟩)

/-- Incoming requests are bounded at each active frame. A dormant capture has
    its own interface, whose outward contracts must be supported at its live
    boundary. Spent boundaries provide no effects. -/
inductive EffectStack (signature : Signature) (tickets : EffectTickets) (world : World) :
    Stack → List Instance → List Instance → Prop where
  | nil (bound : incoming ⊆ outgoing) : EffectStack signature tickets world .nil incoming outgoing
  | push (frame : EffectFrame signature tickets world entry inner outer)
      (rest : EffectStack signature tickets world tail outer outgoing) (bound : incoming ⊆ inner) :
      EffectStack signature tickets world (.push entry tail) incoming outgoing
  | live (known : tickets owner = some contract) (scope : EffectScopeKnown tickets callerScope)
      (saved : EffectStack signature tickets world capture captured contract.resumeEffects)
      (rest : EffectStack signature tickets world tail boundary outgoing)
      (resume : contract.resumeEffects ⊆ boundary) (close : contract.closeEffects ⊆ boundary)
      (bound : incoming ⊆ boundary) :
      EffectStack signature tickets world (.live owner contract.input contract.answer capture callerScope tail) incoming outgoing
  | spent (known : tickets owner = some contract) (scope : EffectScopeKnown tickets callerScope)
      (rest : EffectStack signature tickets world tail boundary outgoing) (bound : incoming ⊆ boundary) :
      EffectStack signature tickets world (.spent owner contract.answer callerScope tail) incoming outgoing

theorem effect_stack_input_weaken (typed : EffectStack signature tickets world stack incoming outgoing)
    (bound : smaller ⊆ incoming) : EffectStack signature tickets world stack smaller outgoing := by
  cases typed with
  | nil old => exact .nil (List.Subset.trans bound old)
  | push frame rest old => exact .push frame rest (List.Subset.trans bound old)
  | live known scope saved rest resume close old =>
      exact .live known scope saved rest resume close (List.Subset.trans bound old)
  | spent known scope rest old => exact .spent known scope rest (List.Subset.trans bound old)

theorem effect_stack_output_weaken (typed : EffectStack signature tickets world stack incoming outgoing)
    (bound : outgoing ⊆ larger) : EffectStack signature tickets world stack incoming larger := by
  induction typed with
  | nil old => exact .nil (List.Subset.trans old bound)
  | push frame rest input ih => exact .push frame (ih bound) input
  | live known scope saved rest resume close input ihSaved ihRest =>
      exact .live known scope saved (ihRest bound) resume close input
  | spent known scope rest input ih => exact .spent known scope (ih bound) input

theorem effect_stack_append
    (front : EffectStack signature tickets world left incoming middle)
    (tail : EffectStack signature tickets world right middle outgoing) :
    EffectStack signature tickets world (left.append right) incoming outgoing := by
  induction front with
  | nil bound => exact effect_stack_input_weaken tail bound
  | push frame rest bound ih => exact .push frame (ih tail) bound
  | live known scope saved rest resume close bound ihSaved ihRest =>
      exact .live known scope saved (ihRest tail) resume close bound
  | spent known scope rest bound ih => exact .spent known scope (ih tail) bound

theorem effect_stack_decompose (front : Stack)
    (typed : EffectStack signature tickets world (front.append tail) incoming outgoing) :
    ∃ middle, EffectStack signature tickets world front incoming middle ∧
      EffectStack signature tickets world tail middle outgoing := by
  induction front generalizing incoming with
  | nil => exact ⟨incoming, .nil (fun _ used => used), typed⟩
  | push frame rest ih => cases typed with
      | push frameTyped restTyped bound =>
          obtain ⟨middle, inside, outside⟩ := ih restTyped
          exact ⟨middle, .push frameTyped inside bound, outside⟩
  | live owner q a saved scope rest ihSaved ihRest => cases typed with
      | live known caller cap rest resume close bound =>
          obtain ⟨middle, inside, outside⟩ := ihRest rest
          exact ⟨middle, .live known caller cap inside resume close bound, outside⟩
  | spent owner a scope rest ih => cases typed with
      | spent known caller rest bound =>
          obtain ⟨middle, inside, outside⟩ := ih rest
          exact ⟨middle, .spent known caller inside bound, outside⟩

theorem handler_cut_effect_decomposition
    (cut : HandlerCut requested whole cap tail handler)
    (typed : EffectStack signature tickets world whole incoming outgoing) :
    ∃ residual, EffectStack signature tickets world cap incoming residual ∧
      EffectStack signature tickets world tail residual outgoing ∧
      EffectFrame signature tickets world (.handler handler) (handler.effectInst :: residual) residual := by
  induction cut generalizing incoming with
  | hit handler tail same => cases typed with
      | push frame rest bound => cases frame with
          | handler scope clauses coverage unique =>
              exact ⟨_, .push (.handler scope clauses coverage unique) (.nil (fun _ used => used)) bound,
                rest, .handler scope clauses coverage unique⟩
  | push frame rest cap tail handler miss next ih => cases typed with
      | push frameTyped restTyped bound =>
          obtain ⟨residual, inside, outside, handlerTyped⟩ := ih restTyped
          exact ⟨residual, .push frameTyped inside bound, outside, handlerTyped⟩
  | live owner q a saved scope rest cap tail handler next ih => cases typed with
      | live known caller savedTyped restTyped resume close bound =>
          obtain ⟨residual, inside, outside, handlerTyped⟩ := ih restTyped
          exact ⟨residual, .live known caller savedTyped inside resume close bound, outside, handlerTyped⟩
  | spent owner a scope rest cap tail handler next ih => cases typed with
      | spent known caller restTyped bound =>
          obtain ⟨residual, inside, outside, handlerTyped⟩ := ih restTyped
          exact ⟨residual, .spent known caller inside bound, outside, handlerTyped⟩

/-- Resume effects come from the same historical contract as the actual live
    occurrence. The full clause prefix is retained in recomposition. -/
theorem resume_effect_recomposition {front cap tail : Stack}
    (known : tickets owner = some contract)
    (typed : EffectStack signature tickets world
      (front.append (.live owner input answer cap callerScope tail)) incoming outgoing)
    (resumeAllowed : contract.resumeEffects ⊆ incoming) :
    EffectStack signature tickets world (cap.append (front.append (.spent owner answer callerScope tail))) [] outgoing := by
  obtain ⟨middle, inside, outside⟩ := effect_stack_decompose front typed
  cases outside with
  | live actual scope saved rest resume close bound =>
      have same := Option.some.inj (known.symm.trans actual)
      cases same
      apply effect_stack_input_weaken (effect_stack_append
        (effect_stack_output_weaken saved resumeAllowed)
        (effect_stack_append inside (.spent actual scope rest bound)))
      simp

theorem effect_frame_forwards (frame : EffectFrame signature tickets world entry incoming outgoing)
    (used : request ∈ incoming) :
    (∃ target, entry.erase.resolve request = some target) ∨ request ∈ outgoing := by
  cases frame with
  | plain | armed | running | closing | retiring => exact Or.inr used
  | handler scope clauses coverage unique =>
      rcases List.mem_cons.mp used with same | used
      · subst request
        exact Or.inl ⟨_, by simp [ExecFrame.erase, HandlerData.erase, Frame.resolve]; rfl⟩
      · exact Or.inr used
  | cell scope noEscape =>
      rcases List.mem_cons.mp used with same | used
      · subst request
        exact Or.inl ⟨_, by simp [ExecFrame.erase, Frame.resolve]; rfl⟩
      · exact Or.inr used

/-- Lookup is the existing nearest exact resolver. Only the active spine can
    discharge a current request; dormant captures are not searched. -/
theorem effect_stack_provides_or_exports
    (typed : EffectStack signature tickets world stack incoming outgoing) (used : request ∈ incoming) :
    (∃ target, stack.erase.resolve request = some target) ∨ request ∈ outgoing := by
  induction typed with
  | nil bound => exact Or.inr (bound used)
  | @push entry inner outer tail outgoing incoming frame rest bound ih =>
      rcases effect_frame_forwards frame (bound used) with ⟨target, found⟩ | forwarded
      · exact Or.inl ⟨target, by simp [Stack.erase, Control.resolve, found]⟩
      · rcases ih forwarded with ⟨target, found⟩ | exported
        · cases first : entry.erase.resolve request with
          | none => exact Or.inl ⟨target, by simp [Stack.erase, Control.resolve, first, found]⟩
          | some nearer => exact Or.inl ⟨nearer, by simp [Stack.erase, Control.resolve, first]⟩
        · exact Or.inr exported
  | live known scope saved rest resume close bound ihSaved ihRest =>
      exact ihRest (bound used)
  | spent known scope rest bound ih => exact ih (bound used)

inductive EffectAtType (signature : Signature) (tickets : EffectTickets) (world : World) :
    Scope → Code → Ty → List Instance → Prop where
  | checked (scope : EffectScope tickets runtimeScope ticket)
      (typed : Typed signature world TypeEnv.empty ticket effects expression type) :
      EffectAtType signature tickets world runtimeScope expression type effects

def EffectConfigurationTyped (signature : Signature) (tickets : EffectTickets) (world : World)
    (configuration : Configuration) (result : Ty) (outgoing : List Instance) : Prop :=
  ∃ input effects, EffectAtType signature tickets world configuration.scope configuration.expression input effects ∧
    StackTyped signature tickets.types world configuration.stack input result ∧
    EffectStack signature tickets world configuration.stack effects outgoing

theorem effect_configuration_has_types
    (typed : EffectConfigurationTyped signature tickets world configuration result outgoing) :
    ConfigurationTyped signature tickets.types world configuration result := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scope expression => exact ⟨input, .checked (effect_scope_has_types scope) expression, stack⟩

theorem current_request_is_interpreted_or_exported
    (typed : EffectConfigurationTyped signature tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ result outgoing) :
    (∃ target, stack.erase.resolve requested = some target) ∨ requested ∈ outgoing := by
  obtain ⟨input, effects, expression, ports, control⟩ := typed
  cases expression with
  | checked scope expression =>
      obtain ⟨operandType, known, available, operandTyped⟩ := typed_perform_inversion expression
      exact effect_stack_provides_or_exports control available

theorem current_request_has_interpretation
    (typed : EffectConfigurationTyped signature tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ result []) :
    ∃ target, stack.erase.resolve requested = some target := by
  rcases current_request_is_interpreted_or_exported typed with found | impossible
  · exact found
  · cases impossible

theorem resume_preserves_effect_configuration {front cap tail : Stack}
    (known : tickets owner = some contract) (resolved : scope.resolve binder = some owner)
    (typed : EffectConfigurationTyped signature tickets world
      ⟨.resume binder value, scope, front.append (.live owner contract.input contract.answer cap callerScope tail)⟩ result outgoing)
    (isValue : value.IsValue) :
    EffectConfigurationTyped signature tickets world
      ⟨value, scope, cap.append (front.append (.spent owner contract.answer callerScope tail))⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | resume operand resumeEffects formed => cases scopeTyped with
          | bound actual =>
              simp [Execution.Scope.resolve] at resolved
              subst owner
              have same := Option.some.inj (known.symm.trans actual)
              cases same
              exact ⟨contract.input, [], .checked (.bound actual)
                (typed_value_transport operand isValue _ []), resume_retains_stack_typing stack,
                resume_effect_recomposition actual effectStack resumeEffects⟩


theorem effect_frame_extension (frame : EffectFrame signature before world entry incoming outgoing)
    (extension : EffectExtension before after) : EffectFrame signature after world entry incoming outgoing := by
  cases frame with
  | plain scope code => exact .plain (effect_scope_extension scope extension) code
  | handler scope clauses coverage unique =>
      exact .handler (effect_scope_known_extension scope extension) clauses coverage unique
  | cell scope noEscape => exact .cell (effect_scope_known_extension scope extension) noEscape
  | armed scope callable requests => exact .armed (effect_scope_known_extension scope extension) callable requests
  | running scope callable result requests => exact .running (effect_scope_known_extension scope extension) callable result requests
  | closing scope => exact .closing (effect_scope_known_extension scope extension)
  | retiring known => exact .retiring (extension _ _ known)

theorem effect_stack_extension (typed : EffectStack signature before world stack incoming outgoing)
    (extension : EffectExtension before after) : EffectStack signature after world stack incoming outgoing := by
  induction typed with
  | nil bound => exact .nil bound
  | push frame rest bound ih => exact .push (effect_frame_extension frame extension) ih bound
  | live known scope saved rest resume close bound ihSaved ihRest =>
      exact .live (extension _ _ known) (effect_scope_known_extension scope extension) ihSaved ihRest resume close bound
  | spent known scope rest bound ih =>
      exact .spent (extension _ _ known) (effect_scope_known_extension scope extension) ih bound


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
    ∃ (parameter binder : Nat) (body : Code) (output : Ty) (residual : List Instance),
      let contract : ContinuationContract := ⟨output, handler.answer, residual, residual⟩
      let extended := tickets.insert owner contract
      RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner output handler.answer cap handler.scope tail⟩ [.ticket owner] [] ∧
      EffectExtension tickets extended ∧
      EffectConfigurationTyped signature extended world
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner output handler.answer cap handler.scope tail⟩ result outgoing := by
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
          let contract : ContinuationContract := ⟨output, handler.answer, residual, residual⟩
          let extended := tickets.insert owner contract
          have extension : EffectExtension tickets extended := effect_ticket_insertion_extends fresh
          have newTicket : extended owner = some contract := by simp [extended, EffectTickets.insert]
          have typeExtension := effect_extension_has_type_extension extension
          have newTypes : extended.types owner = some (output, handler.answer) := by
            simp [EffectTickets.types, newTicket, contract]
          refine ⟨parameter, binder, body, output, residual,
            .capture requested operation parameter binder owner operand body scope whole cap tail handler output
              cut selected closed (typed_suffix_ready bodyTyped),
            extension, handler.answer, residual, ?_, ?_, ?_⟩
          · exact .checked (.bound newTicket)
              (selected_clause_substitution_typed selected clauses operationAtHandler operandTyped closed)
          · exact .live newTypes (effect_scope_known_has_types (effect_scope_known_extension caller extension))
              (stack_typed_extension capturedTypes typeExtension) (stack_typed_extension outsideTypes typeExtension)
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
    value and connected effect typing. A fresh historical ticket slot is needed
    only for source capture; ownership freshness and permissions remain separate.
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
          | lambda bodyTyped retained formed =>
              exact ⟨input, _, .checked .none
                (typed_substitution bodyTyped (typed_value_transport argument isValue .none [])
                  (typed_value_closed argument isValue)), stack, effect_stack_input_weaken effectStack available⟩


namespace EffectExamples

def twoRequests : Signature := withCellSignatures fun effect operation =>
  match effect, operation with
  | .user 1 [], 0 | .user 2 [], 0 => some (.unit, .unit)
  | _, _ => none

def innerClauses : ScopedExpressions.Clauses := .cons 0 1 9 (.resume 9 .unit) .nil
def outerClauses : ScopedExpressions.Clauses := .cons 0 1 10 (.resume 10 .unit) .nil

theorem inner_clauses_typed : ClausesTyped twoRequests [] TypeEnv.empty (.user 1 []) .unit [.user 2 []] innerClauses :=
  .cons rfl (.resume .unit (fun _ used => used) (List.nil_subset _)) .nil

theorem outer_clauses_typed : ClausesTyped twoRequests [] TypeEnv.empty (.user 2 []) .unit [] outerClauses :=
  .cons rfl (.resume .unit (fun _ used => used) (List.nil_subset _)) .nil

def inner : HandlerData := ⟨8, .user 1 [], innerClauses, .none, .unit, clauses_have_ticket_barrier inner_clauses_typed⟩
def outer : HandlerData := ⟨20, .user 2 [], outerClauses, .none, .unit, clauses_have_ticket_barrier outer_clauses_typed⟩
def pending : PlainData := ⟨.bind 0 (.perform (.user 2 []) 0 .unit), .none, .unit, .unit, [], rfl⟩
def captured : Stack := .push (.plain pending) (.push (.handler inner) .nil)
def outside : Stack := .push (.handler outer) .nil
def noTickets : EffectTickets := fun _ => none
def contract : ContinuationContract := ⟨.unit, .unit, [.user 2 []], [.user 2 []]⟩
def capturedTickets : EffectTickets := noTickets.insert 3 contract

theorem inner_frame_effects : EffectFrame twoRequests tickets [] (.handler inner) [.user 1 [], .user 2 []] [.user 2 []] := by
  apply EffectFrame.handler ⟨_, .none⟩ inner_clauses_typed
  · intro operation input output known
    cases operation with
    | zero => simp [inner, innerClauses, clauseKeys]
    | succ n => simp [inner, twoRequests, withCellSignatures] at known
  · decide

theorem outer_frame_effects : EffectFrame twoRequests tickets [] (.handler outer) [.user 2 []] [] := by
  apply EffectFrame.handler ⟨_, .none⟩ outer_clauses_typed
  · intro operation input output known
    cases operation with
    | zero => simp [outer, outerClauses, clauseKeys]
    | succ n => simp [outer, twoRequests, withCellSignatures] at known
  · decide

theorem pending_frame_effects : EffectFrame twoRequests tickets [] (.plain pending) [.user 1 [], .user 2 []] [.user 1 [], .user 2 []] :=
  .plain .none (.bind (.perform (effect := .user 2 []) rfl (by simp) .unit (List.nil_subset _)))

theorem captured_effects : EffectStack twoRequests tickets [] captured [.user 1 [], .user 2 []] [.user 2 []] :=
  .push pending_frame_effects (.push inner_frame_effects (.nil (fun _ used => used)) (fun _ used => used)) (fun _ used => used)

theorem outside_effects : EffectStack twoRequests tickets [] outside [.user 2 []] [] :=
  .push outer_frame_effects (.nil (fun _ used => used)) (fun _ used => used)

theorem captured_types {tickets : EffectTickets} : StackTyped twoRequests tickets.types [] captured .unit .unit :=
  .push (effect_frame_has_types pending_frame_effects) (.push (effect_frame_has_types inner_frame_effects) .nil)

theorem outside_types {tickets : EffectTickets} : StackTyped twoRequests tickets.types [] outside .unit .unit :=
  .push (effect_frame_has_types outer_frame_effects) .nil

theorem nested_request_typed : EffectConfigurationTyped twoRequests noTickets []
    ⟨.perform (.user 1 []) 0 .unit, .none, captured.append outside⟩ .unit [] :=
  ⟨.unit, [.user 1 [], .user 2 []], .checked .none (.perform (effect := .user 1 []) rfl (by simp) .unit (List.nil_subset _)),
    stack_typed_append captured_types outside_types, effect_stack_append captured_effects outside_effects⟩

theorem nested_capture_typed : EffectConfigurationTyped twoRequests capturedTickets []
    ⟨.resume 9 .unit, .ticket 9 3, .live 3 .unit .unit captured .none outside⟩ .unit [] := by
  have known : capturedTickets 3 = some contract := rfl
  exact ⟨.unit, [.user 2 []], .checked (.bound known) (.resume .unit (fun _ used => used) (List.nil_subset _)),
    .live (by simp [EffectTickets.types, known, contract]) ⟨_, .none⟩ captured_types outside_types,
    .live known ⟨_, .none⟩ captured_effects outside_effects
      (fun _ used => used) (fun _ used => used) (fun _ used => used)⟩

theorem nested_request_progress :
    ∃ next after created,
      RawStep ⟨.perform (freezeEffect (.user 1 [])) 0 .unit, .none, captured.append outside⟩ after created [] ∧
      EffectExtension noTickets next ∧
      EffectConfigurationTyped twoRequests next [] after .unit [] :=
  closed_request_effect_progress nested_request_typed trivial (owner := 3) rfl

theorem nested_capture_executes :
    RawStep ⟨.perform (freezeEffect (.user 1 [])) 0 .unit, .none, captured.append outside⟩
      ⟨.resume 9 .unit, .ticket 9 3, .live 3 .unit .unit captured .none outside⟩ [.ticket 3] [] :=
  .capture (.user 1 []) 0 1 9 3 .unit (.resume 9 .unit) .none (captured.append outside) captured outside inner .unit
    (.push _ _ _ _ _ (by simp [ExecFrame.erase, PlainData.erase, Frame.target]) (.hit inner outside rfl))
    .hit ScopedExecution.Examples.unit_closed (by simp [ScopedExpressions.ClosedExcept, Code.dependencies])

theorem nested_resume_reaches_outer_effect :
    EffectConfigurationTyped twoRequests capturedTickets []
      ⟨.perform (freezeEffect (.user 2 [])) 0 .unit, .none, .push (.handler inner) (.spent 3 .unit .none outside)⟩ .unit [] ∧
    (Stack.push (.handler inner) (.spent 3 .unit .none outside)).erase.resolve (.user 2 []) = some (.source 20) := by
  have resumed := resume_preserves_effect_configuration (front := .nil) (contract := contract)
    (show capturedTickets 3 = some contract from rfl) rfl nested_capture_typed trivial
  have plugged := raw_value_step_preserves_effect_configuration
    (RawStep.plug pending .unit ScopedExecution.Examples.unit_closed (.ticket 9 3)
      (.push (.handler inner) (.spent 3 .unit .none outside))) ScopedExecution.Examples.unit_closed resumed
  have suffix := bind_preserves_effect_configuration plugged trivial
  exact ⟨suffix, by simp [Stack.erase, ExecFrame.erase, HandlerData.erase, inner, outer, outside,
    Control.resolve, Frame.resolve]⟩

def initial : RunState :=
  ⟨⟨.perform (freezeEffect (.user 1 [])) 0 .unit, .none, captured.append outside⟩, [], []⟩
def terminal : RunState :=
  ⟨⟨.perform (freezeEffect (.user 2 [])) 0 .unit, .none,
      .push (.handler inner) (.spent 3 .unit .none outside)⟩, [.ticket 3], [.ticket 3]⟩

/-- Four actual steps capture, resume, plug, and sequence. The resumed suffix
    requests the outer effect through the reinstalled inner interpretation. -/
theorem nested_execution : RunSteps initial terminal := by
  have resume := RawStep.resume 9 3 (.ticket 9 3) .none .unit .unit .nil captured outside
    .unit ScopedExecution.Examples.unit_closed rfl
  have plug := RawStep.plug pending .unit ScopedExecution.Examples.unit_closed (.ticket 9 3)
    (.push (.handler inner) (.spent 3 .unit .none outside))
  have bind := RawStep.bind 0 .unit (.perform (freezeEffect (.user 2 [])) 0 .unit) .none
    (.push (.handler inner) (.spent 3 .unit .none outside)) ScopedExecution.Examples.unit_closed
    (by simp [ScopedExpressions.ClosedExcept, Code.dependencies, effectAtoms, Effect.resources, freezeEffect])
  exact .next (.event initial _ _ _ nested_capture_executes (by decide))
    (.next (.event _ _ _ _ resume (by decide))
      (.next (.event _ _ _ _ plug (by decide))
        (.next (.event _ _ _ _ bind (by decide)) (.refl terminal))))

theorem nested_execution_preserves_ledger : Ledger terminal.erase :=
  run_steps_preserve_ledger nested_execution ⟨.refl _, by decide⟩

/-- The old value-typed unhandled request cannot claim a closed effect interface. -/
theorem unhandled_request_rejected :
    ¬ EffectConfigurationTyped twoRequests noTickets []
      ⟨.perform (freezeEffect (.user 1 [])) 0 .unit, .none, .nil⟩ .unit [] := by
  intro typed
  obtain ⟨target, found⟩ := current_request_has_interpretation typed
  cases found

theorem unhandled_request_is_outward :
    EffectConfigurationTyped twoRequests noTickets []
      ⟨.perform (freezeEffect (.user 1 [])) 0 .unit, .none, .nil⟩ .unit [.user 1 []] :=
  ⟨.unit, [.user 1 []], .checked .none (.perform (effect := .user 1 []) rfl (by simp) .unit (List.nil_subset _)),
    .nil, .nil (List.Subset.refl _)⟩

def pureContract : ContinuationContract := ⟨.unit, .unit, [], []⟩
def pureTickets : EffectTickets := noTickets.insert 5 pureContract

theorem matching_dormant_handler_is_inhabited :
    EffectConfigurationTyped twoRequests pureTickets []
      ⟨.resume 11 .unit, .ticket 11 5, .live 5 .unit .unit outside .none .nil⟩ .unit [] := by
  have known : pureTickets 5 = some pureContract := rfl
  exact ⟨.unit, [], .checked (.bound known) (.resume .unit (fun _ used => used) (List.nil_subset _)),
    .live (by simp [EffectTickets.types, known, pureContract]) ⟨_, .none⟩ outside_types .nil,
    .live known ⟨_, .none⟩ outside_effects (.nil (fun _ used => used))
      (fun _ used => used) (fun _ used => used) (fun _ used => used)⟩

theorem dormant_handler_does_not_supply_active_request :
    ¬ EffectStack twoRequests pureTickets [] (.live 5 .unit .unit outside .none .nil) [.user 2 []] [] := by
  intro typed
  rcases effect_stack_provides_or_exports typed (request := .user 2 []) (by simp) with ⟨target, found⟩ | impossible
  · simp [Stack.erase, Control.resolve] at found
  · cases impossible

def cellOnly : Signature := withCellSignatures (fun _ _ => none)

theorem read_configuration : EffectConfigurationTyped cellOnly noTickets [4]
    ⟨.perform (freezeEffect (.cell 4)) 0 (.resourceRef (.activation 4)), .none,
      .push (.cell 4 17 .none .integer) .nil⟩ .integer [] :=
  ⟨.integer, [.cell 4], .checked .none (.perform rfl (by simp) (.reference (by simp)) (List.nil_subset _)),
    .push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) .nil,
    .push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) (.nil (List.Subset.refl _)) (List.Subset.refl _)⟩

theorem builtin_read_executes_with_effect_typing :
    RawStep ⟨.perform (freezeEffect (.cell 4)) 0 (.resourceRef (.activation 4)), .none,
      .push (.cell 4 17 .none .integer) .nil⟩
      ⟨.integer 17, .none, .push (.cell 4 17 .none .integer) .nil⟩ [] [] ∧
    EffectConfigurationTyped cellOnly noTickets [4]
      ⟨.integer 17, .none, .push (.cell 4 17 .none .integer) .nil⟩ .integer [] :=
  ⟨.readCell 4 17 .none _ _ .hit, cell_read_preserves_effect_configuration read_configuration .hit⟩

theorem write_configuration : EffectConfigurationTyped cellOnly noTickets [4]
    ⟨.perform (freezeEffect (.cell 4)) 1 (.pair (.resourceRef (.activation 4)) (.integer 23)), .none,
      .push (.cell 4 17 .none .unit) .nil⟩ .unit [] :=
  ⟨.unit, [.cell 4], .checked .none (.perform rfl (by simp) (.pair (.reference (by simp)) .integer) (List.nil_subset _)),
    .push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) .nil,
    .push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) (.nil (List.Subset.refl _)) (List.Subset.refl _)⟩

theorem builtin_write_executes_with_effect_typing :
    RawStep ⟨.perform (freezeEffect (.cell 4)) 1 (.pair (.resourceRef (.activation 4)) (.integer 23)), .none,
      .push (.cell 4 17 .none .unit) .nil⟩
      ⟨.unit, .none, .push (.cell 4 23 .none .unit) .nil⟩ [] [] ∧
    EffectConfigurationTyped cellOnly noTickets [4]
      ⟨.unit, .none, .push (.cell 4 23 .none .unit) .nil⟩ .unit [] :=
  ⟨.writeCell 4 17 23 .none _ _ .hit, cell_write_preserves_effect_configuration write_configuration .hit⟩

end EffectExamples

end Ash.OneShot.ScopedTyping

#print axioms Ash.OneShot.ScopedTyping.effect_stack_append
#print axioms Ash.OneShot.ScopedTyping.effect_stack_decompose
#print axioms Ash.OneShot.ScopedTyping.handler_cut_effect_decomposition
#print axioms Ash.OneShot.ScopedTyping.resume_effect_recomposition
#print axioms Ash.OneShot.ScopedTyping.effect_stack_provides_or_exports
#print axioms Ash.OneShot.ScopedTyping.current_request_has_interpretation
#print axioms Ash.OneShot.ScopedTyping.effect_configuration_has_types
#print axioms Ash.OneShot.ScopedTyping.resume_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.effect_stack_extension
#print axioms Ash.OneShot.ScopedTyping.cell_update_preserves_effect_stack
#print axioms Ash.OneShot.ScopedTyping.cell_read_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.cell_write_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.capture_constructs_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.builtin_effect_progress
#print axioms Ash.OneShot.ScopedTyping.request_effect_progress
#print axioms Ash.OneShot.ScopedTyping.closed_request_effect_progress
#print axioms Ash.OneShot.ScopedTyping.raw_value_step_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.bind_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.beta_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedTyping.EffectExamples.nested_request_progress
#print axioms Ash.OneShot.ScopedTyping.EffectExamples.nested_resume_reaches_outer_effect
#print axioms Ash.OneShot.ScopedTyping.EffectExamples.nested_execution
#print axioms Ash.OneShot.ScopedTyping.EffectExamples.nested_execution_preserves_ledger
#print axioms Ash.OneShot.ScopedTyping.EffectExamples.unhandled_request_rejected
#print axioms Ash.OneShot.ScopedTyping.EffectExamples.unhandled_request_is_outward
#print axioms Ash.OneShot.ScopedTyping.EffectExamples.matching_dormant_handler_is_inhabited
#print axioms Ash.OneShot.ScopedTyping.EffectExamples.dormant_handler_does_not_supply_active_request
#print axioms Ash.OneShot.ScopedTyping.EffectExamples.builtin_read_executes_with_effect_typing
#print axioms Ash.OneShot.ScopedTyping.EffectExamples.builtin_write_executes_with_effect_typing
