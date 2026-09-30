import Entries

/-!
Effect interfaces of ordered stack segments. Actual retained code is checked
against its frame interface; continuation signatures record separate resume
and disposal effects. These judgments complement ownership, support and usage
checks. Effect availability does not establish safe disposal or permission to
consume a continuation.
-/

namespace Ash.OneShot.Typing
open Syntax Execution

structure ContinuationContract where
  input : Ty
  answer : Ty
  resumeEffects : List Instance
  closeEffects : List Instance
  deriving DecidableEq, Repr

abbrev EffectTickets := Nat → Option ContinuationContract

def EffectTickets.types (tickets : EffectTickets) : TicketSignatures :=
  fun owner => (tickets owner).map fun contract => (contract.input, contract.answer)

inductive EffectScope (tickets : EffectTickets) : Scope → TicketType → Prop where
  | none : EffectScope tickets .none .none
  | bound (known : tickets owner = some contract) :
      EffectScope tickets (.ticket binder owner)
        (.bound binder contract.input contract.answer contract.resumeEffects contract.closeEffects)

def EffectScopeKnown (tickets : EffectTickets) (scope : Scope) : Prop :=
  ∃ ticket, EffectScope tickets scope ticket

theorem effect_scope_has_types (scope : EffectScope tickets runtimeScope ticket) :
    ScopeTyped tickets.types runtimeScope ticket := by
  cases scope with
  | none => exact .none
  | bound known => exact .bound (by simp [EffectTickets.types, known])

theorem effect_scope_known_has_types (scope : EffectScopeKnown tickets runtimeScope) :
    ScopeKnown tickets.types runtimeScope := by
  obtain ⟨ticket, scope⟩ := scope
  exact ⟨ticket, effect_scope_has_types scope⟩

inductive EffectFrame (signature : Signature) (tickets : EffectTickets) :
    ExecFrame → List Instance → List Instance → Prop where
  | plain (scope : EffectScope tickets data.scope ticket)
      (code : ContextTyped signature TypeEnv.empty ticket effects data.context data.input data.output) :
      EffectFrame signature tickets (.plain data) effects effects
  | handler (scope : EffectScopeKnown tickets handler.scope)
      (clauses : ClausesTyped signature TypeEnv.empty handler.effectInst handler.answer residual handler.clauses)
      (coverage : Covers signature handler.effectInst handler.clauses)
      (unique : (clauseKeys handler.clauses).Nodup) :
      EffectFrame signature tickets (.handler handler) (handler.effectInst :: residual) residual
  | cell (scope : EffectScopeKnown tickets runtimeScope) (noEscape : identity ∉ answer.resources) :
      EffectFrame signature tickets (.cell identity payload runtimeScope answer) (.cell identity :: residual) residual
  | armed (scope : EffectScopeKnown tickets action.scope)
      (callable : Typed signature TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests retained)) (requests : action.requests ⊆ effects) :
      EffectFrame signature tickets (.armed action) effects effects
  | running (scope : EffectScopeKnown tickets action.scope)
      (callable : Typed signature TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests retained))
      (result : Typed signature TypeEnv.empty .none [] saved action.answer)
      (requests : action.requests ⊆ effects) :
      EffectFrame signature tickets (.running action saved closed) effects effects
  | closing (scope : EffectScopeKnown tickets runtimeScope) :
      EffectFrame signature tickets (.closing identity runtimeScope) effects effects
  | retiring (known : tickets owner = some contract) :
      EffectFrame signature tickets (.retiring owner) effects effects

theorem effect_frame_has_types (frame : EffectFrame signature tickets entry incoming outgoing) :
    FrameTyped signature tickets.types entry := by
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
inductive EffectStack (signature : Signature) (tickets : EffectTickets) :
    Stack → List Instance → List Instance → Prop where
  | nil (bound : incoming ⊆ outgoing) : EffectStack signature tickets .nil incoming outgoing
  | push (frame : EffectFrame signature tickets entry inner outer)
      (rest : EffectStack signature tickets tail outer outgoing) (bound : incoming ⊆ inner) :
      EffectStack signature tickets (.push entry tail) incoming outgoing
  | live (known : tickets owner = some contract) (scope : EffectScopeKnown tickets callerScope)
      (saved : EffectStack signature tickets capture captured contract.resumeEffects)
      (rest : EffectStack signature tickets tail boundary outgoing)
      (resume : contract.resumeEffects ⊆ boundary) (close : contract.closeEffects ⊆ boundary)
      (bound : incoming ⊆ boundary) :
      EffectStack signature tickets (.live owner contract.input contract.answer capture callerScope tail) incoming outgoing
  | spent (known : tickets owner = some contract) (scope : EffectScopeKnown tickets callerScope)
      (rest : EffectStack signature tickets tail boundary outgoing) (bound : incoming ⊆ boundary) :
      EffectStack signature tickets (.spent owner contract.answer callerScope tail) incoming outgoing

theorem effect_stack_input_weaken (typed : EffectStack signature tickets stack incoming outgoing)
    (bound : smaller ⊆ incoming) : EffectStack signature tickets stack smaller outgoing := by
  cases typed with
  | nil old => exact .nil (List.Subset.trans bound old)
  | push frame rest old => exact .push frame rest (List.Subset.trans bound old)
  | live known scope saved rest resume close old =>
      exact .live known scope saved rest resume close (List.Subset.trans bound old)
  | spent known scope rest old => exact .spent known scope rest (List.Subset.trans bound old)

theorem effect_stack_output_weaken (typed : EffectStack signature tickets stack incoming outgoing)
    (bound : outgoing ⊆ larger) : EffectStack signature tickets stack incoming larger := by
  induction typed with
  | nil old => exact .nil (List.Subset.trans old bound)
  | push frame rest input ih => exact .push frame (ih bound) input
  | live known scope saved rest resume close input ihSaved ihRest =>
      exact .live known scope saved (ihRest bound) resume close input
  | spent known scope rest input ih => exact .spent known scope (ih bound) input

theorem effect_stack_append
    (front : EffectStack signature tickets left incoming middle)
    (tail : EffectStack signature tickets right middle outgoing) :
    EffectStack signature tickets (left.append right) incoming outgoing := by
  induction front with
  | nil bound => exact effect_stack_input_weaken tail bound
  | push frame rest bound ih => exact .push frame (ih tail) bound
  | live known scope saved rest resume close bound ihSaved ihRest =>
      exact .live known scope saved (ihRest tail) resume close bound
  | spent known scope rest bound ih => exact .spent known scope (ih tail) bound

theorem effect_stack_decompose (front : Stack)
    (typed : EffectStack signature tickets (front.append tail) incoming outgoing) :
    ∃ middle, EffectStack signature tickets front incoming middle ∧
      EffectStack signature tickets tail middle outgoing := by
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
    (typed : EffectStack signature tickets whole incoming outgoing) :
    ∃ residual, EffectStack signature tickets cap incoming residual ∧
      EffectStack signature tickets tail residual outgoing ∧
      EffectFrame signature tickets (.handler handler) (handler.effectInst :: residual) residual := by
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
    (typed : EffectStack signature tickets
      (front.append (.live owner input answer cap callerScope tail)) incoming outgoing)
    (resumeAllowed : contract.resumeEffects ⊆ incoming) :
    EffectStack signature tickets (cap.append (front.append (.spent owner answer callerScope tail))) [] outgoing := by
  obtain ⟨middle, inside, outside⟩ := effect_stack_decompose front typed
  cases outside with
  | live actual scope saved rest resume close bound =>
      have same := Option.some.inj (known.symm.trans actual)
      cases same
      apply effect_stack_input_weaken (effect_stack_append
        (effect_stack_output_weaken saved resumeAllowed)
        (effect_stack_append inside (.spent actual scope rest bound)))
      simp

theorem effect_frame_forwards (frame : EffectFrame signature tickets entry incoming outgoing)
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
    (typed : EffectStack signature tickets stack incoming outgoing) (used : request ∈ incoming) :
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

inductive EffectAtType (signature : Signature) (tickets : EffectTickets) :
    Scope → Expr → Ty → List Instance → Prop where
  | checked (scope : EffectScope tickets runtimeScope ticket)
      (typed : Typed signature TypeEnv.empty ticket effects expression type) :
      EffectAtType signature tickets runtimeScope expression type effects

def EffectConfigurationTyped (signature : Signature) (tickets : EffectTickets)
    (configuration : Configuration) (result : Ty) (outgoing : List Instance) : Prop :=
  ∃ input effects, EffectAtType signature tickets configuration.scope configuration.expression input effects ∧
    StackTyped signature tickets.types configuration.stack input result ∧
    EffectStack signature tickets configuration.stack effects outgoing

theorem effect_configuration_has_types
    (typed : EffectConfigurationTyped signature tickets configuration result outgoing) :
    ConfigurationTyped signature tickets.types configuration result := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scope expression => exact ⟨input, .checked (effect_scope_has_types scope) expression, stack⟩

theorem current_request_is_interpreted_or_exported
    (typed : EffectConfigurationTyped signature tickets ⟨.perform requested operation operand, scope, stack⟩ result outgoing) :
    (∃ target, stack.erase.resolve requested = some target) ∨ requested ∈ outgoing := by
  obtain ⟨input, effects, expression, ports, control⟩ := typed
  cases expression with
  | checked scope expression => cases expression with
      | perform operation available operand => exact effect_stack_provides_or_exports control available

theorem current_request_has_interpretation
    (typed : EffectConfigurationTyped signature tickets ⟨.perform requested operation operand, scope, stack⟩ result []) :
    ∃ target, stack.erase.resolve requested = some target := by
  rcases current_request_is_interpreted_or_exported typed with found | impossible
  · exact found
  · cases impossible

theorem resume_preserves_effect_configuration {front cap tail : Stack}
    (known : tickets owner = some contract) (resolved : scope.resolve binder = some owner)
    (typed : EffectConfigurationTyped signature tickets
      ⟨.resume binder value, scope, front.append (.live owner contract.input contract.answer cap callerScope tail)⟩ result outgoing)
    (isValue : value.IsValue) :
    EffectConfigurationTyped signature tickets
      ⟨value, scope, cap.append (front.append (.spent owner contract.answer callerScope tail))⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | resume operand resumeEffects => cases scopeTyped with
          | bound actual =>
              simp [Scope.resolve] at resolved
              subst owner
              have same := Option.some.inj (known.symm.trans actual)
              cases same
              exact ⟨contract.input, [], .checked (.bound actual)
                (typed_value_transport operand isValue _ []), resume_retains_stack_typing stack,
                resume_effect_recomposition actual effectStack resumeEffects⟩

def EffectExtension (before after : EffectTickets) : Prop :=
  ∀ owner contract, before owner = some contract → after owner = some contract

def EffectTickets.insert (tickets : EffectTickets) (owner : Nat) (contract : ContinuationContract) : EffectTickets :=
  fun other => if other = owner then some contract else tickets other

theorem effect_ticket_insertion_extends (fresh : tickets owner = none) :
    EffectExtension tickets (tickets.insert owner contract) := by
  intro other previous known
  by_cases same : other = owner
  · subst other
    rw [fresh] at known
    cases known
  · simp [EffectTickets.insert, same, known]

theorem effect_extension_has_type_extension (extension : EffectExtension before after) :
    TicketExtension before.types after.types := by
  intro owner input answer known
  cases previous : before owner with
  | none => simp [EffectTickets.types, previous] at known
  | some contract =>
      have next := extension owner contract previous
      simpa [EffectTickets.types, next] using (show some (contract.input, contract.answer) = some (input, answer) from
        by simpa [EffectTickets.types, previous] using known)

theorem effect_scope_extension (scope : EffectScope before runtimeScope ticket)
    (extension : EffectExtension before after) : EffectScope after runtimeScope ticket := by
  cases scope with
  | none => exact .none
  | bound known => exact .bound (extension _ _ known)

theorem effect_scope_known_extension (scope : EffectScopeKnown before runtimeScope)
    (extension : EffectExtension before after) : EffectScopeKnown after runtimeScope := by
  obtain ⟨ticket, scope⟩ := scope
  exact ⟨ticket, effect_scope_extension scope extension⟩

theorem effect_frame_extension (frame : EffectFrame signature before entry incoming outgoing)
    (extension : EffectExtension before after) : EffectFrame signature after entry incoming outgoing := by
  cases frame with
  | plain scope code => exact .plain (effect_scope_extension scope extension) code
  | handler scope clauses coverage unique =>
      exact .handler (effect_scope_known_extension scope extension) clauses coverage unique
  | cell scope noEscape => exact .cell (effect_scope_known_extension scope extension) noEscape
  | armed scope callable requests => exact .armed (effect_scope_known_extension scope extension) callable requests
  | running scope callable result requests => exact .running (effect_scope_known_extension scope extension) callable result requests
  | closing scope => exact .closing (effect_scope_known_extension scope extension)
  | retiring known => exact .retiring (extension _ _ known)

theorem effect_stack_extension (typed : EffectStack signature before stack incoming outgoing)
    (extension : EffectExtension before after) : EffectStack signature after stack incoming outgoing := by
  induction typed with
  | nil bound => exact .nil bound
  | push frame rest bound ih => exact .push (effect_frame_extension frame extension) ih bound
  | live known scope saved rest resume close bound ihSaved ihRest =>
      exact .live (extension _ _ known) (effect_scope_known_extension scope extension) ihSaved ihRest resume close bound
  | spent known scope rest bound ih =>
      exact .spent (extension _ _ known) (effect_scope_known_extension scope extension) ih bound

theorem capture_constructs_effect_configuration
    (cut : HandlerCut requested whole cap tail handler)
    (typed : EffectConfigurationTyped signature tickets ⟨.perform requested operation operand, scope, whole⟩ result outgoing)
    (isValue : operand.IsValue)
    (hygiene : ∀ parameter binder body, ClauseAt operation handler.clauses parameter binder body → ResourceFresh operand body)
    (fresh : tickets owner = none) :
    ∃ (parameter binder : Nat) (body : Expr) (output : Ty) (residual : List Instance),
      let contract : ContinuationContract := ⟨output, handler.answer, residual, residual⟩
      let extended := tickets.insert owner contract
      RawStep ⟨.perform requested operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner output handler.answer cap handler.scope tail⟩ [.ticket owner] [] ∧
      EffectExtension tickets extended ∧
      EffectConfigurationTyped signature extended
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner output handler.answer cap handler.scope tail⟩ result outgoing := by
  have lexical := typed_capture_lexical_admission (effect_configuration_has_types typed) cut isValue
  obtain ⟨output, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | perform operationType available operandTyped =>
          obtain ⟨residual, capturedEffects, outsideEffects, handlerEffects⟩ := handler_cut_effect_decomposition cut effectStack
          obtain ⟨capturedTypes, outsideTypes, handlerTypes⟩ := handler_cut_retains_typing cut stack
          cases handlerEffects with
          | handler caller clauses coverage unique =>
              have operationAtHandler := operationType
              rw [← handler_cut_instance cut] at operationAtHandler
              obtain ⟨parameter, binder, body, selected⟩ := covered_operation_selects_clause coverage operationAtHandler
              let contract : ContinuationContract := ⟨output, handler.answer, residual, residual⟩
              let extended := tickets.insert owner contract
              have extension : EffectExtension tickets extended := effect_ticket_insertion_extends fresh
              have newTicket : extended owner = some contract := by simp [extended, EffectTickets.insert]
              have typeExtension := effect_extension_has_type_extension extension
              have newTypes : extended.types owner = some (output, handler.answer) := by
                simp [EffectTickets.types, newTicket, contract]
              refine ⟨parameter, binder, body, output, residual,
                .capture requested operation parameter binder owner operand body scope whole cap tail handler output
                  cut selected lexical.1 (lexical.2 parameter binder body selected) (hygiene parameter binder body selected),
                extension, handler.answer, residual, ?_, ?_, ?_⟩
              · exact .checked (.bound newTicket)
                  (selected_clause_substitution_typed selected clauses operationAtHandler operandTyped lexical.1)
              · exact .live newTypes (effect_scope_known_has_types (effect_scope_known_extension caller extension))
                  (stack_typed_extension capturedTypes typeExtension) (stack_typed_extension outsideTypes typeExtension)
              · exact .live newTicket (effect_scope_known_extension caller extension)
                  (effect_stack_extension capturedEffects extension) (effect_stack_extension outsideEffects extension)
                  (fun _ used => used) (fun _ used => used) (fun _ used => used)

theorem effect_ticket_from_types {tickets : EffectTickets} (known : tickets.types owner = some (input, answer)) :
    ∃ contract, tickets owner = some contract := by
  cases found : tickets owner with
  | none => simp [EffectTickets.types, found] at known
  | some contract => exact ⟨contract, rfl⟩

theorem effect_live_to_spent
    (typed : EffectStack signature tickets (.live owner input answer cap callerScope tail) incoming outgoing) :
    EffectStack signature tickets (.spent owner answer callerScope tail) incoming outgoing := by
  cases typed with
  | live known scope saved rest resume close bound => exact .spent known scope rest bound

theorem close_plan_has_effect_interface
    (contents : PlanContentsTyped signature tickets.types plan)
    (typed : PlanTyped signature closing plan) (scope : EffectScopeKnown tickets runtimeScope) :
    EffectStack signature tickets (closeControl runtimeScope plan) (planProvides plan ++ closing) closing := by
  induction typed with
  | nil => exact .nil (fun _ used => used)
  | release rest ih => cases contents with
      | release remaining =>
          exact .push (.cell scope (by simp [Ty.resources])) (ih remaining) (fun _ used => used)
  | retire rest ih => cases contents with
      | retire known remaining =>
          obtain ⟨contract, known⟩ := effect_ticket_from_types known
          exact .push (.retiring known) (ih remaining) (fun _ used => used)
  | invoke callable effects rest ih => cases contents with
      | invoke oldCallable remaining => exact .push (.armed scope callable effects) (ih remaining) (fun _ used => used)

theorem discard_preserves_effect_configuration {front cap tail : Stack}
    (known : tickets owner = some contract) (resolved : scope.resolve binder = some owner)
    (typed : EffectConfigurationTyped signature tickets
      ⟨.discard binder, scope, front.append (.live owner contract.input contract.answer cap callerScope tail)⟩ result outgoing)
    (built : makePlan cap = some plan) (planTyped : PlanTyped signature contract.closeEffects plan) :
    EffectConfigurationTyped signature tickets
      ⟨.unit, scope, (closeControl scope plan).append
        (.push (.closing closeId scope) (front.append (.spent owner contract.answer callerScope tail)))⟩ result outgoing := by
  have oldAfter := discard_preserves_configuration_typing (closeId := closeId) resolved built (effect_configuration_has_types typed)
  obtain ⟨oldInput, oldExpression, oldStack⟩ := oldAfter
  cases oldExpression with
  | checked oldScope oldExpression => cases oldExpression with
      | unit =>
          obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
          cases expression with
          | checked scopeTyped expression => cases expression with
              | discard closeAllowed => cases scopeTyped with
                  | bound actual =>
                      simp [Scope.resolve] at resolved
                      subst owner
                      have same := Option.some.inj (known.symm.trans actual)
                      cases same
                      obtain ⟨middleType, frontTypes, liveTypes⟩ := stack_typed_decompose front stack
                      cases liveTypes with
                      | live oldKnown oldCaller capturedTypes outsideTypes =>
                          have contents := make_plan_retains_types capturedTypes built
                          have closeEffects := close_plan_has_effect_interface contents planTyped ⟨_, .bound (binder := binder) actual⟩
                          obtain ⟨middle, inside, outside⟩ := effect_stack_decompose front effectStack
                          refine ⟨.unit, [], .checked (.bound actual) .unit, oldStack, ?_⟩
                          apply effect_stack_input_weaken (effect_stack_append
                            (effect_stack_output_weaken closeEffects closeAllowed)
                            (.push (.closing ⟨_, .bound actual⟩)
                              (effect_stack_append inside (effect_live_to_spent outside)) (fun _ used => used)))
                          simp

theorem effect_value_transport (typed : EffectAtType signature tickets scope value type effects)
    (isValue : value.IsValue) (destination : EffectScopeKnown tickets otherScope) (newEffects : List Instance) :
    EffectAtType signature tickets otherScope value type newEffects := by
  obtain ⟨ticket, scopeTyped⟩ := destination
  cases typed with
  | checked oldScope typed => exact .checked scopeTyped (typed_value_transport typed isValue ticket newEffects)

theorem effect_value_closed_type (typed : EffectAtType signature tickets scope value type effects)
    (isValue : value.IsValue) : Typed signature TypeEnv.empty .none [] value type := by
  cases typed with
  | checked scope typed => exact typed_value_transport typed isValue .none []

/-- Every raw closed-value transition preserves both actual retained-code
    types and their connected effect interfaces. Ownership and use admission
    remain independent obligations. -/
theorem raw_value_step_preserves_effect_configuration
    (step : RawStep before after created discharged) (closed : ClosedValue before.expression)
    (typed : EffectConfigurationTyped signature tickets before result outgoing) :
    EffectConfigurationTyped signature tickets after result outgoing := by
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
    (typed : EffectConfigurationTyped signature tickets ⟨.bind parameter value body, scope, tail⟩ result outgoing)
    (isValue : value.IsValue) :
    EffectConfigurationTyped signature tickets ⟨body.subst parameter value, scope, tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | bind initializer suffix =>
          exact ⟨input, effects, .checked scopeTyped
            (typed_substitution suffix (typed_value_transport initializer isValue .none [])
              (typed_value_is_closed initializer isValue)), stack, effectStack⟩

theorem beta_preserves_effect_configuration
    (typed : EffectConfigurationTyped signature tickets ⟨.app (.lambda parameter body) value, scope, tail⟩ result outgoing)
    (isValue : value.IsValue) :
    EffectConfigurationTyped signature tickets ⟨body.subst parameter value, .none, tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | app function argument available => cases function with
          | lambda bodyTyped retained =>
              exact ⟨input, _, .checked .none
                (typed_substitution bodyTyped (typed_value_transport argument isValue .none [])
                  (typed_value_is_closed argument isValue)), stack, effect_stack_input_weaken effectStack available⟩

theorem focus_constructs_effect_configuration
    (typed : EffectConfigurationTyped signature tickets ⟨whole, scope, tail⟩ result outgoing)
    (focus : Focus whole child context) :
    ∃ plain : PlainData, plain.context = context ∧ plain.scope = scope ∧
      RawStep ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩ [] [] ∧
      EffectConfigurationTyped signature tickets ⟨child, scope, .push (.plain plain) tail⟩ result outgoing := by
  obtain ⟨output, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped wholeTyped =>
      obtain ⟨input, childTyped, contextTyped⟩ := typed_focus_decomposition focus wholeTyped
      have contextBound : context.dependencies ⊆ whole.dependencies := by
        cases focus <;> simp_all [Context.dependencies, Context.plug, Expr.dependencies, List.subset_def]
      obtain ⟨pending, translated⟩ := scope_translates_scoped_dependencies (effect_scope_has_types scopeTyped)
        (fun binder used => typed_tickets_scoped wholeTyped (contextBound used))
      let plain : PlainData := ⟨context, scope, input, output, pending, translated⟩
      exact ⟨plain, rfl, rfl, .focus plain focus tail,
        input, effects, .checked scopeTyped childTyped,
        .push (.plain (effect_scope_has_types scopeTyped) contextTyped) stack,
        .push (.plain scopeTyped contextTyped) effectStack (fun _ used => used)⟩

theorem handler_entry_constructs_effect_configuration
    (typed : EffectConfigurationTyped signature tickets ⟨.handle effectInst body clauses, scope, tail⟩ result outgoing)
    (activation : Nat) :
    ∃ handler : HandlerData, handler.activation = activation ∧
      RawStep ⟨.handle effectInst body clauses, scope, tail⟩ ⟨body, scope, .push (.handler handler) tail⟩ [] [] ∧
      EffectConfigurationTyped signature tickets ⟨body, scope, .push (.handler handler) tail⟩ result outgoing := by
  obtain ⟨answer, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | handle bodyTyped clausesTyped coverage unique available =>
          let handler : HandlerData := ⟨activation, effectInst, clauses, scope, answer, typed_clauses_have_barrier clausesTyped⟩
          have frame : EffectFrame signature tickets (.handler handler) _ _ :=
            .handler ⟨_, scopeTyped⟩ clausesTyped coverage unique
          exact ⟨handler, rfl, .enterHandler handler body tail,
            answer, _, .checked scopeTyped bodyTyped, .push (effect_frame_has_types frame) stack,
            .push frame (effect_stack_input_weaken effectStack available) (fun _ used => used)⟩

theorem cell_entry_constructs_effect_configuration
    (typed : EffectConfigurationTyped signature tickets ⟨.resource identity (.integer payload) body, scope, tail⟩ result outgoing) :
    ∃ answer : Ty,
      RawStep ⟨.resource identity (.integer payload) body, scope, tail⟩
        ⟨body, scope, .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
      EffectConfigurationTyped signature tickets ⟨body, scope, .push (.cell identity payload scope answer) tail⟩ result outgoing := by
  obtain ⟨answer, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | resource initializer bodyTyped noEscape noEffectEscape available =>
          exact ⟨answer, .enterCell identity payload body scope answer tail,
            answer, _, .checked scopeTyped bodyTyped, .push (.cell ⟨_, effect_scope_has_types scopeTyped⟩ noEscape) stack,
            .push (.cell ⟨_, scopeTyped⟩ noEscape) (effect_stack_input_weaken effectStack available) (fun _ used => used)⟩

theorem cleanup_entry_constructs_effect_configuration
    (typed : EffectConfigurationTyped signature tickets ⟨.cleanup callback body, scope, tail⟩ result outgoing)
    (isValue : callback.IsValue) (identity : Nat) :
    ∃ action : ActionData,
      RawStep ⟨.cleanup callback body, scope, tail⟩ ⟨body, scope, .push (.armed action) tail⟩ [.cleanup identity] [] ∧
      EffectConfigurationTyped signature tickets ⟨body, scope, .push (.armed action) tail⟩ result outgoing := by
  obtain ⟨answer, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | @cleanup _ _ _ _ latent retained _ _ callbackTyped bodyTyped available =>
          have closed := typed_value_is_closed callbackTyped isValue
          let action : ActionData := ⟨identity, callback, closed, scope, answer, latent⟩
          have frame : EffectFrame signature tickets (.armed action) effects effects :=
            .armed ⟨_, scopeTyped⟩ (typed_value_transport callbackTyped isValue .none []) available
          exact ⟨action, .enterCleanup action body tail,
            answer, effects, .checked scopeTyped bodyTyped, .push (effect_frame_has_types frame) stack,
            .push frame effectStack (fun _ used => used)⟩

theorem branch_preserves_effect_configuration
    (typed : EffectConfigurationTyped signature tickets ⟨.branch (.boolean condition) yes no, scope, tail⟩ result outgoing) :
    EffectConfigurationTyped signature tickets ⟨if condition then yes else no, scope, tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | branch test yesTyped noTyped =>
          cases condition
          · exact ⟨input, effects, .checked scopeTyped noTyped, stack, effectStack⟩
          · exact ⟨input, effects, .checked scopeTyped yesTyped, stack, effectStack⟩

theorem cell_update_preserves_effect_stack
    (update : CellUpdate identity old new before after)
    (typed : EffectStack signature tickets before incoming outgoing) :
    EffectStack signature tickets after incoming outgoing := by
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
    (typed : EffectConfigurationTyped (withCellSignatures users) tickets
      ⟨.perform (.cell identity) 0 (.resourceRef identity), scope, before⟩ result outgoing)
    (selected : CellUpdate identity payload payload before after) :
    EffectConfigurationTyped (withCellSignatures users) tickets ⟨.integer payload, scope, after⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | perform operation available operand =>
          simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
          obtain ⟨rfl, rfl⟩ := operation
          exact ⟨.integer, [], .checked scopeTyped .integer, cell_update_preserves_stack_typing selected stack,
            effect_stack_input_weaken (cell_update_preserves_effect_stack selected effectStack) (by simp)⟩

theorem cell_write_preserves_effect_configuration
    (typed : EffectConfigurationTyped (withCellSignatures users) tickets
      ⟨.perform (.cell identity) 1 (.pair (.resourceRef identity) (.integer new)), scope, before⟩ result outgoing)
    (selected : CellUpdate identity old new before after) :
    EffectConfigurationTyped (withCellSignatures users) tickets ⟨.unit, scope, after⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | perform operation available operand =>
          simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
          obtain ⟨rfl, rfl⟩ := operation
          exact ⟨.unit, [], .checked scopeTyped .unit, cell_update_preserves_stack_typing selected stack,
            effect_stack_input_weaken (cell_update_preserves_effect_stack selected effectStack) (by simp)⟩

namespace EffectExamples

def twoRequests : Signature
  | .user 1 [], 0 | .user 2 [], 0 => some (.unit, .unit)
  | _, _ => none

def innerClauses : Clauses := .cons 0 1 9 (.resume 9 .unit) .nil
def outerClauses : Clauses := .cons 0 1 10 (.resume 10 .unit) .nil

theorem inner_clauses_typed : ClausesTyped twoRequests TypeEnv.empty (.user 1 []) .unit [.user 2 []] innerClauses :=
  .cons rfl (.resume .unit (fun _ used => used)) .nil

theorem outer_clauses_typed : ClausesTyped twoRequests TypeEnv.empty (.user 2 []) .unit [] outerClauses :=
  .cons rfl (.resume .unit (fun _ used => used)) .nil

def inner : HandlerData := ⟨8, .user 1 [], innerClauses, .none, .unit, typed_clauses_have_barrier inner_clauses_typed⟩
def outer : HandlerData := ⟨20, .user 2 [], outerClauses, .none, .unit, typed_clauses_have_barrier outer_clauses_typed⟩
def pending : PlainData := ⟨.bind 0 (.perform (.user 2 []) 0 .unit), .none, .unit, .unit, [], rfl⟩
def captured : Stack := .push (.plain pending) (.push (.handler inner) .nil)
def outside : Stack := .push (.handler outer) .nil
def noTickets : EffectTickets := fun _ => none
def contract : ContinuationContract := ⟨.unit, .unit, [.user 2 []], [.user 2 []]⟩
def capturedTickets : EffectTickets := noTickets.insert 3 contract

theorem inner_frame_effects : EffectFrame twoRequests tickets (.handler inner) [.user 1 [], .user 2 []] [.user 2 []] := by
  apply EffectFrame.handler ⟨_, .none⟩ inner_clauses_typed
  · intro operation input output known
    cases operation with
    | zero => simp [inner, innerClauses, clauseKeys]
    | succ n => simp [inner, twoRequests] at known
  · decide

theorem outer_frame_effects : EffectFrame twoRequests tickets (.handler outer) [.user 2 []] [] := by
  apply EffectFrame.handler ⟨_, .none⟩ outer_clauses_typed
  · intro operation input output known
    cases operation with
    | zero => simp [outer, outerClauses, clauseKeys]
    | succ n => simp [outer, twoRequests] at known
  · decide

theorem pending_frame_effects : EffectFrame twoRequests tickets (.plain pending) [.user 1 [], .user 2 []] [.user 1 [], .user 2 []] :=
  .plain .none (.bind (.perform rfl (by simp) .unit))

theorem captured_effects : EffectStack twoRequests tickets captured [.user 1 [], .user 2 []] [.user 2 []] :=
  .push pending_frame_effects (.push inner_frame_effects (.nil (fun _ used => used)) (fun _ used => used)) (fun _ used => used)

theorem outside_effects : EffectStack twoRequests tickets outside [.user 2 []] [] :=
  .push outer_frame_effects (.nil (fun _ used => used)) (fun _ used => used)

theorem captured_types {tickets : EffectTickets} : StackTyped twoRequests tickets.types captured .unit .unit :=
  .push (effect_frame_has_types pending_frame_effects) (.push (effect_frame_has_types inner_frame_effects) .nil)

theorem outside_types {tickets : EffectTickets} : StackTyped twoRequests tickets.types outside .unit .unit :=
  .push (effect_frame_has_types outer_frame_effects) .nil

theorem nested_request_typed : EffectConfigurationTyped twoRequests noTickets
    ⟨.perform (.user 1 []) 0 .unit, .none, captured.append outside⟩ .unit [] :=
  ⟨.unit, [.user 1 [], .user 2 []], .checked .none (.perform rfl (by simp) .unit),
    stack_typed_append captured_types outside_types, effect_stack_append captured_effects outside_effects⟩

theorem nested_capture_typed : EffectConfigurationTyped twoRequests capturedTickets
    ⟨.resume 9 .unit, .ticket 9 3, .live 3 .unit .unit captured .none outside⟩ .unit [] := by
  have known : capturedTickets 3 = some contract := rfl
  exact ⟨.unit, [.user 2 []], .checked (.bound known) (.resume .unit (fun _ used => used)),
    .live (by simp [EffectTickets.types, known, contract]) ⟨_, .none⟩ captured_types outside_types,
    .live known ⟨_, .none⟩ captured_effects outside_effects
      (fun _ used => used) (fun _ used => used) (fun _ used => used)⟩

theorem nested_capture_executes :
    RawStep ⟨.perform (.user 1 []) 0 .unit, .none, captured.append outside⟩
      ⟨.resume 9 .unit, .ticket 9 3, .live 3 .unit .unit captured .none outside⟩ [.ticket 3] [] :=
  .capture (.user 1 []) 0 1 9 3 .unit (.resume 9 .unit) .none (captured.append outside) captured outside inner .unit
    (.push _ _ _ _ _ (by simp [ExecFrame.erase, PlainData.erase, Frame.target]) (.hit inner outside rfl))
    .hit Execution.Examples.closed_unit (by simp [ClosedExcept, Expr.dependencies]) (by simp [ResourceFresh, Expr.dependencies])

/-- The saved suffix really uses the nonempty residual. After resume, it
    reaches the outer interpretation through the inner handler and spent ticket. -/
theorem nested_resume_reaches_outer_effect :
    EffectConfigurationTyped twoRequests capturedTickets
      ⟨.perform (.user 2 []) 0 .unit, .none, .push (.handler inner) (.spent 3 .unit .none outside)⟩ .unit [] ∧
    (Stack.push (.handler inner) (.spent 3 .unit .none outside)).erase.resolve (.user 2 []) = some (.source 20) := by
  have resumed := resume_preserves_effect_configuration (front := .nil) (contract := contract)
    (show capturedTickets 3 = some contract from rfl) rfl nested_capture_typed trivial
  have plugged := raw_value_step_preserves_effect_configuration
    (RawStep.plug pending .unit Execution.Examples.closed_unit (.ticket 9 3)
      (.push (.handler inner) (.spent 3 .unit .none outside))) Execution.Examples.closed_unit resumed
  have suffix := bind_preserves_effect_configuration plugged trivial
  exact ⟨suffix, by simp [Stack.erase, ExecFrame.erase, HandlerData.erase, inner, outer, outside,
    Control.resolve, Frame.resolve]⟩

theorem nested_capture_resume_trace :
    RawTrace ⟨.perform (.user 1 []) 0 .unit, .none, captured.append outside⟩
      ⟨.perform (.user 2 []) 0 .unit, .none, .push (.handler inner) (.spent 3 .unit .none outside)⟩
      [.ticket 3] [.ticket 3] := by
  have resume := RawStep.resume 9 3 (.ticket 9 3) .none .unit .unit .nil captured outside
    .unit Execution.Examples.closed_unit rfl
  have plug := RawStep.plug pending .unit Execution.Examples.closed_unit (.ticket 9 3)
    (.push (.handler inner) (.spent 3 .unit .none outside))
  have bind := RawStep.bind 0 .unit (.perform (.user 2 []) 0 .unit) .none
    (.push (.handler inner) (.spent 3 .unit .none outside)) Execution.Examples.closed_unit
    (by simp [ClosedExcept, Expr.dependencies, instanceDependencies, Instance.resources])
    (by simp [ResourceFresh, Expr.dependencies])
  exact .next nested_capture_executes (.next resume (.next plug (.next bind (.refl _))))

def pureContract : ContinuationContract := ⟨.unit, .unit, [], []⟩
def pureTickets : EffectTickets := noTickets.insert 5 pureContract

/-- The matching handler is safely retained in a dormant capture, and can be
    reinstated by resume. It still does not interpret the active clause. -/
theorem matching_dormant_handler_is_inhabited :
    EffectConfigurationTyped twoRequests pureTickets
      ⟨.resume 11 .unit, .ticket 11 5, .live 5 .unit .unit outside .none .nil⟩ .unit [] := by
  have known : pureTickets 5 = some pureContract := rfl
  exact ⟨.unit, [], .checked (.bound known) (.resume .unit (fun _ used => used)),
    .live (by simp [EffectTickets.types, known, pureContract]) ⟨_, .none⟩ outside_types .nil,
    .live known ⟨_, .none⟩ outside_effects (.nil (fun _ used => used))
      (fun _ used => used) (fun _ used => used) (fun _ used => used)⟩

theorem dormant_handler_does_not_supply_active_request :
    ¬ EffectStack twoRequests pureTickets (.live 5 .unit .unit outside .none .nil) [.user 2 []] [] := by
  intro typed
  rcases effect_stack_provides_or_exports typed (request := .user 2 []) (by simp) with ⟨target, found⟩ | impossible
  · simp [Stack.erase, Control.resolve] at found
  · cases impossible

theorem cell_close_plan_retains_builtin :
    EffectStack RetainedExamples.userAndCells tickets
      (closeControl .none Execution.Examples.closePlan) [.cell 4] [] := by
  apply close_plan_has_effect_interface (scope := ⟨_, .none⟩)
  · exact make_plan_retains_types (RetainedExamples.abandoned_cell_stack_has_typed_code (tickets := tickets.types)) rfl
  · exact .invoke RetainedExamples.read_callback_retained_type
      (by simp [Execution.Examples.readAction, planProvides]) (.release .nil)

end EffectExamples

end Ash.OneShot.Typing

#print axioms Ash.OneShot.Typing.effect_stack_append
#print axioms Ash.OneShot.Typing.handler_cut_effect_decomposition
#print axioms Ash.OneShot.Typing.resume_effect_recomposition
#print axioms Ash.OneShot.Typing.effect_stack_provides_or_exports
#print axioms Ash.OneShot.Typing.current_request_has_interpretation
#print axioms Ash.OneShot.Typing.resume_preserves_effect_configuration
#print axioms Ash.OneShot.Typing.capture_constructs_effect_configuration
#print axioms Ash.OneShot.Typing.close_plan_has_effect_interface
#print axioms Ash.OneShot.Typing.discard_preserves_effect_configuration
#print axioms Ash.OneShot.Typing.raw_value_step_preserves_effect_configuration
#print axioms Ash.OneShot.Typing.EffectExamples.nested_capture_typed
#print axioms Ash.OneShot.Typing.EffectExamples.nested_resume_reaches_outer_effect
#print axioms Ash.OneShot.Typing.focus_constructs_effect_configuration
#print axioms Ash.OneShot.Typing.handler_entry_constructs_effect_configuration
#print axioms Ash.OneShot.Typing.cleanup_entry_constructs_effect_configuration
#print axioms Ash.OneShot.Typing.cell_read_preserves_effect_configuration
#print axioms Ash.OneShot.Typing.cell_write_preserves_effect_configuration
#print axioms Ash.OneShot.Typing.EffectExamples.cell_close_plan_retains_builtin
#print axioms Ash.OneShot.Typing.EffectExamples.nested_capture_resume_trace
#print axioms Ash.OneShot.Typing.EffectExamples.matching_dormant_handler_is_inhabited
