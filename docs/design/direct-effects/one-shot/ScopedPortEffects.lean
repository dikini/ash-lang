import ScopedPortRetained

/-!
Ordered effect interfaces using declared ports. Historical contracts retain
resume and closing effect rows independently of resource support and usage
permissions. EffectStack checks effect connections; the separate StackTyped
projection compares actual runtime metadata with the same record's ports.
-/

namespace Ash.OneShot.ScopedPorts
open Syntax Instantiation ScopedExpressions ScopedExecution
open ScopedTyping (World clauseKeys)

structure ContinuationContract where
  input : Port
  answer : Port
  resumeEffects : List Instance
  closeEffects : List Instance
  deriving DecidableEq, Repr

abbrev EffectTickets := Nat → Option ContinuationContract

def EffectTickets.types (tickets : EffectTickets) : TicketSignatures :=
  fun owner => (tickets owner).map fun contract => (contract.input, contract.answer)

inductive EffectScope (tickets : EffectTickets) : Scope → Ticket → Prop where
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

inductive EffectFrame (signature : Signature) (tickets : EffectTickets) (world : World) :
    ExecFrame → List Instance → List Instance → Prop where
  | plain (scope : EffectScope tickets data.scope ticket)
      (code : ContextTyped signature world TypeEnv.empty ticket effects data.context (eraseType data.input) (eraseType data.output)) :
      EffectFrame signature tickets world (.plain data) effects effects
  | handler (scope : EffectScopeKnown tickets handler.scope)
      (clauses : ClausesTyped signature world TypeEnv.empty handler.effectInst (eraseType handler.answer) residual handler.clauses)
      (coverage : Covers signature handler.effectInst handler.clauses)
      (unique : (clauseKeys handler.clauses).Nodup) :
      EffectFrame signature tickets world (.handler handler) (handler.effectInst :: residual) residual
  | cell (scope : EffectScopeKnown tickets runtimeScope) (noEscape : identity ∉ (eraseType answer).resources) :
      EffectFrame signature tickets world (.cell identity payload runtimeScope answer) (.cell identity :: residual) residual
  | armed (scope : EffectScopeKnown tickets action.scope)
      (callable : Typed signature world TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests)) (requests : action.requests ⊆ effects) :
      EffectFrame signature tickets world (.armed action) effects effects
  | running (scope : EffectScopeKnown tickets action.scope)
      (callable : Typed signature world TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests))
      (result : Typed signature world TypeEnv.empty .none [] saved (eraseType action.answer))
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
      EffectStack signature tickets world (.live owner input answer capture callerScope tail) incoming outgoing
  | spent (known : tickets owner = some contract) (scope : EffectScopeKnown tickets callerScope)
      (rest : EffectStack signature tickets world tail boundary outgoing) (bound : incoming ⊆ boundary) :
      EffectStack signature tickets world (.spent owner answer callerScope tail) incoming outgoing

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
    Scope → Code → Port → List Instance → Prop where
  | checked (scope : EffectScope tickets runtimeScope ticket)
      (typed : Typed signature world TypeEnv.empty ticket effects expression type) :
      EffectAtType signature tickets world runtimeScope expression type effects

def EffectConfigurationTyped (signature : Signature) (tickets : EffectTickets) (world : World)
    (configuration : Configuration) (result : Port) (outgoing : List Instance) : Prop :=
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



/-- Outward observation requires an actual failed lookup, in addition to
    membership in the declared outgoing row. -/
theorem unhandled_current_request_is_exported
    (typed : EffectConfigurationTyped signature tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ result outgoing)
    (unhandled : stack.erase.resolve requested = none) : requested ∈ outgoing := by
  rcases current_request_is_interpreted_or_exported typed with ⟨target, found⟩ | exported
  · rw [unhandled] at found
    cases found
  · exact exported

/-- The effect contract and the port projection refer to the same owner.
    Only erased metadata equality is used when rebuilding the saved stack. -/
theorem resume_preserves_effect_configuration {front cap tail : Stack}
    (resolved : scope.resolve binder = some owner)
    (typed : EffectConfigurationTyped signature tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩ result outgoing)
    (isValue : value.IsValue) :
    EffectConfigurationTyped signature tickets world
      ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩ result outgoing := by
  obtain ⟨expressionType, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | resume operand resumeEffects formed => cases scopeTyped with
          | bound known =>
              simp [Execution.Scope.resolve] at resolved
              subst owner
              obtain ⟨middle, frontTyped, outside⟩ := stack_typed_decompose front stack
              cases outside with
              | live actual caller saved rest =>
                  have projected := actual
                  simp only [EffectTickets.types, known, Option.map_some] at projected
                  obtain ⟨inputPort, answerPort⟩ := Prod.mk.inj (Option.some.inj projected)
                  rw [answerPort] at frontTyped
                  refine ⟨_, [], .checked (.bound known) (typed_value_transport operand isValue _ []), ?_,
                    resume_effect_recomposition known effectStack resumeEffects⟩
                  rw [inputPort]
                  exact stack_typed_append saved (stack_typed_append frontTyped (.spent actual caller rest))

/-- The same concrete resume event preserves connected port/effect typing,
    ledger conservation and independently checked support. -/
theorem resume_preserves_effects_ledger_support {front cap tail : Stack}
    (typed : EffectConfigurationTyped signature tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩ result outgoing)
    (isValue : value.IsValue) (resolved : scope.resolve binder = some owner)
    (ledger : Ledger (RunState.erase
      ⟨⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩, issued, completed⟩))
    (support : AccessValid ⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩ ambient) :
    let after : Configuration := ⟨value, scope, cap.append (front.append (.spent owner answer caller tail))⟩
    RunStep ⟨⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩, issued, completed⟩
      ⟨after, issued, .ticket owner :: completed⟩ ∧
    EffectConfigurationTyped signature tickets world after result outgoing ∧
    Ledger (RunState.erase ⟨after, issued, .ticket owner :: completed⟩) ∧ AccessValid after ambient := by
  obtain ⟨step, _, conserved, retained⟩ := resume_preserves_ports_ledger_support
    (effect_configuration_has_types typed) isValue resolved ledger support
  exact ⟨step, resume_preserves_effect_configuration resolved typed isValue, conserved, retained⟩

namespace EffectExamples
open ScopedSignatureGap.Examples
open Ash.OneShot.ScopedPorts.Examples (signature callbackPort payload_typed clauses_typed coverage)
open RetainedExamples (beforeRequest afterCapture afterResume)

def records : EffectTickets := EffectTickets.insert (fun _ => none) 7 ⟨.unit, .unit, [], []⟩

theorem outside_effects : EffectStack signature tickets [0] outside [] [] :=
  .push (.cell ⟨_, .none⟩ (by simp [eraseType, Port.resources])) (.nil (List.nil_subset _)) (List.nil_subset _)

theorem handler_effects : EffectFrame signature tickets [0] (.handler handler) [send] [] :=
  .handler ⟨_, .none⟩ (clauses_typed (residual := [])) coverage (by decide)

theorem source_entries_connected :
    EffectConfigurationTyped signature (fun _ => none) [] ⟨program, .none, .nil⟩ .unit [] ∧
    EffectConfigurationTyped signature (fun _ => none) [0] ⟨openedBody 0, .none, outside⟩ .unit [] :=
  ⟨⟨.unit, [], .checked .none Ash.OneShot.ScopedPorts.Examples.generative_source_port_typed,
      .nil, .nil (List.nil_subset _)⟩,
    ⟨.unit, [], .checked .none (Ash.OneShot.ScopedPorts.Examples.opened_body_typed
      (allowed := []) (by simp)), RetainedExamples.outside_typed, outside_effects⟩⟩

theorem request_connected : EffectConfigurationTyped signature (fun _ => none) [0] beforeRequest .unit [] :=
  ⟨.unit, [send], .checked .none (.perform (by simp [Ash.OneShot.ScopedPorts.Examples.signature]) (by simp)
    (payload_typed (by simp)) (List.nil_subset _)),
    .push RetainedExamples.handler_typed RetainedExamples.outside_typed,
    .push handler_effects outside_effects (fun _ used => used)⟩

theorem request_has_actual_interpretation :
    ∃ target, beforeRequest.stack.erase.resolve send = some target :=
  current_request_has_interpretation request_connected

theorem captured_connected : EffectConfigurationTyped signature records [0] afterCapture .unit [] :=
  ⟨.unit, [], .checked (.bound rfl) (.resume .unit (List.nil_subset _) (List.nil_subset _)),
    .live rfl ⟨_, .none⟩ (.push RetainedExamples.handler_typed .nil) RetainedExamples.outside_typed,
    .live rfl ⟨_, .none⟩ (.push handler_effects (.nil (List.nil_subset _)) (List.nil_subset _))
      outside_effects (List.nil_subset _) (List.nil_subset _) (List.nil_subset _)⟩

theorem resumed_connected : EffectConfigurationTyped signature records [0] afterResume .unit [] :=
  resume_preserves_effect_configuration (front := .nil) rfl captured_connected trivial

/-- A declared callback port without retained resources cannot justify release,
    even when every immediate request has an effect interface. -/
theorem connected_typing_does_not_imply_release :
    EffectConfigurationTyped signature (fun _ => none) [0] RetainedExamples.escapingReturn callbackPort [] ∧
    ¬ AccessChecks RetainedExamples.escapingReturn [] :=
  ⟨⟨callbackPort, [], .checked .none (payload_typed (allowed := []) (by simp)),
      .push (.cell ⟨_, .none⟩ (by simp [callbackPort, eraseType, embedPort, Port.resources])) .nil,
      .push (.cell ⟨_, .none⟩ (by simp [callbackPort, eraseType, embedPort, Port.resources]))
        (.nil (List.nil_subset _)) (List.nil_subset _)⟩,
    RetainedExamples.escaping_return_access_rejected⟩

end EffectExamples

end Ash.OneShot.ScopedPorts

#print axioms Ash.OneShot.ScopedPorts.effect_scope_has_types
#print axioms Ash.OneShot.ScopedPorts.effect_scope_known_has_types
#print axioms Ash.OneShot.ScopedPorts.effect_frame_has_types
#print axioms Ash.OneShot.ScopedPorts.effect_stack_input_weaken
#print axioms Ash.OneShot.ScopedPorts.effect_stack_output_weaken
#print axioms Ash.OneShot.ScopedPorts.effect_stack_append
#print axioms Ash.OneShot.ScopedPorts.effect_stack_decompose
#print axioms Ash.OneShot.ScopedPorts.handler_cut_effect_decomposition
#print axioms Ash.OneShot.ScopedPorts.resume_effect_recomposition
#print axioms Ash.OneShot.ScopedPorts.effect_frame_forwards
#print axioms Ash.OneShot.ScopedPorts.effect_stack_provides_or_exports
#print axioms Ash.OneShot.ScopedPorts.effect_configuration_has_types
#print axioms Ash.OneShot.ScopedPorts.current_request_is_interpreted_or_exported
#print axioms Ash.OneShot.ScopedPorts.current_request_has_interpretation
#print axioms Ash.OneShot.ScopedPorts.effect_ticket_insertion_extends
#print axioms Ash.OneShot.ScopedPorts.effect_extension_has_type_extension
#print axioms Ash.OneShot.ScopedPorts.effect_scope_extension
#print axioms Ash.OneShot.ScopedPorts.effect_scope_known_extension
#print axioms Ash.OneShot.ScopedPorts.effect_frame_extension
#print axioms Ash.OneShot.ScopedPorts.effect_stack_extension
#print axioms Ash.OneShot.ScopedPorts.unhandled_current_request_is_exported
#print axioms Ash.OneShot.ScopedPorts.resume_preserves_effect_configuration
#print axioms Ash.OneShot.ScopedPorts.resume_preserves_effects_ledger_support
#print axioms Ash.OneShot.ScopedPorts.EffectExamples.outside_effects
#print axioms Ash.OneShot.ScopedPorts.EffectExamples.handler_effects
#print axioms Ash.OneShot.ScopedPorts.EffectExamples.source_entries_connected
#print axioms Ash.OneShot.ScopedPorts.EffectExamples.request_connected
#print axioms Ash.OneShot.ScopedPorts.EffectExamples.request_has_actual_interpretation
#print axioms Ash.OneShot.ScopedPorts.EffectExamples.captured_connected
#print axioms Ash.OneShot.ScopedPorts.EffectExamples.resumed_connected
#print axioms Ash.OneShot.ScopedPorts.EffectExamples.connected_typing_does_not_imply_release
