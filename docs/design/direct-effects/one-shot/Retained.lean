import Names

/-!
Type derivations for actual retained expressions, cleanup values, saved results,
and recursively captured stacks. This is a value-type layer: each expression
retains a Typed derivation, but immediate effect bounds are not yet connected
across all frames. The historical ticket signature table records input/answer
types, not ownership, availability, or permission to resume/dispose.
-/

namespace Ash.OneShot.Typing
open Syntax Execution

abbrev TicketSignatures := Nat → Option (Ty × Ty)

inductive ScopeTyped (tickets : TicketSignatures) : Scope → TicketType → Prop where
  | none : ScopeTyped tickets .none .none
  | bound (known : tickets owner = some (input, answer)) :
      ScopeTyped tickets (.ticket binder owner) (.bound binder input answer residual closing)

def ScopeKnown (tickets : TicketSignatures) (scope : Scope) : Prop :=
  ∃ ticket, ScopeTyped tickets scope ticket

/-- Immediate effect bounds are retained existentially. This judgment alone
    makes no claim that surrounding interpretations provide those effects. -/
inductive AtType (signature : Signature) (tickets : TicketSignatures) : Scope → Expr → Ty → Prop where
  | checked (scope : ScopeTyped tickets runtimeScope ticket)
      (typed : Typed signature TypeEnv.empty ticket allowed expression type) :
      AtType signature tickets runtimeScope expression type

theorem at_type_scope_known (typed : AtType signature tickets scope expression type) :
    ScopeKnown tickets scope := by
  cases typed with
  | checked scope typed => exact ⟨_, scope⟩

theorem at_type_value_transport (typed : AtType signature tickets scope value type)
    (closed : ClosedValue value) (destination : ScopeKnown tickets otherScope) :
    AtType signature tickets otherScope value type := by
  obtain ⟨ticket, scopeTyped⟩ := destination
  cases typed with
  | checked scope valueTyped => exact .checked scopeTyped (typed_value_transport valueTyped closed.1 ticket [])

theorem at_type_closed_value (typed : AtType signature tickets scope value type)
    (closed : ClosedValue value) : Typed signature TypeEnv.empty .none [] value type := by
  cases typed with
  | checked scope valueTyped => exact typed_value_transport valueTyped closed.1 .none []

/-- Every actual payload is checked. Cell results exclude the local identity;
    running cleanup also retains a typed saved result. -/
inductive FrameTyped (signature : Signature) (tickets : TicketSignatures) : ExecFrame → Prop where
  | plain (scope : ScopeTyped tickets data.scope ticket)
      (context : ContextTyped signature TypeEnv.empty ticket allowed data.context data.input data.output) :
      FrameTyped signature tickets (.plain data)
  | handler (scope : ScopeKnown tickets handler.scope)
      (clauses : ClausesTyped signature TypeEnv.empty handler.effectInst handler.answer residual handler.clauses)
      (coverage : Covers signature handler.effectInst handler.clauses)
      (unique : (clauseKeys handler.clauses).Nodup) : FrameTyped signature tickets (.handler handler)
  | cell (scope : ScopeKnown tickets runtimeScope) (noEscape : identity ∉ answer.resources) :
      FrameTyped signature tickets (.cell identity payload runtimeScope answer)
  | armed (scope : ScopeKnown tickets action.scope)
      (callable : Typed signature TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests retained)) : FrameTyped signature tickets (.armed action)
  | running (scope : ScopeKnown tickets action.scope)
      (callable : Typed signature TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests retained))
      (result : Typed signature TypeEnv.empty .none [] saved action.answer) :
      FrameTyped signature tickets (.running action saved closed)
  | closing (scope : ScopeKnown tickets runtimeScope) : FrameTyped signature tickets (.closing identity runtimeScope)
  | retiring (known : tickets owner = some (input, answer)) : FrameTyped signature tickets (.retiring owner)

/-- Port composition now requires typing the stored code and all dormant
    captures, in addition to agreeing on annotated input/answer types. -/
inductive StackTyped (signature : Signature) (tickets : TicketSignatures) : Stack → Ty → Ty → Prop where
  | nil : StackTyped signature tickets .nil type type
  | push (frame : FrameTyped signature tickets entry)
      (rest : StackTyped signature tickets tail entry.erase.output result) :
      StackTyped signature tickets (.push entry tail) entry.erase.input result
  | live (known : tickets owner = some (input, answer)) (scope : ScopeKnown tickets callerScope)
      (saved : StackTyped signature tickets capture input answer)
      (rest : StackTyped signature tickets tail answer result) :
      StackTyped signature tickets (.live owner input answer capture callerScope tail) answer result
  | spent (known : tickets owner = some (input, answer)) (scope : ScopeKnown tickets callerScope)
      (rest : StackTyped signature tickets tail answer result) :
      StackTyped signature tickets (.spent owner answer callerScope tail) answer result

def ConfigurationTyped (signature : Signature) (tickets : TicketSignatures)
    (configuration : Configuration) (result : Ty) : Prop :=
  ∃ input, AtType signature tickets configuration.scope configuration.expression input ∧
    StackTyped signature tickets configuration.stack input result

theorem stack_typing_gives_ports (typed : StackTyped signature tickets stack input result) :
    Fits stack.erase input result := by
  induction typed with
  | nil => exact .nil _
  | push frame rest ih => exact .push _ _ _ ih
  | live known scope saved rest ihSaved ihRest => exact .live _ _ _ _ _ _ ihSaved ihRest
  | spent known scope rest ih => exact .spent _ _ _ _ ih

theorem stack_typed_append
    (front : StackTyped signature tickets left input middle)
    (tail : StackTyped signature tickets right middle result) :
    StackTyped signature tickets (left.append right) input result := by
  induction front with
  | nil => exact tail
  | push frame rest ih => exact .push frame (ih tail)
  | live known scope saved rest ihSaved ihRest => exact .live known scope saved (ihRest tail)
  | spent known scope rest ih => exact .spent known scope (ih tail)

theorem stack_typed_decompose (front : Stack)
    (typed : StackTyped signature tickets (front.append tail) input result) :
    ∃ middle, StackTyped signature tickets front input middle ∧
      StackTyped signature tickets tail middle result := by
  induction front generalizing input with
  | nil => exact ⟨_, .nil, typed⟩
  | push entry rest ih => cases typed with
      | push frame tail =>
          obtain ⟨middle, frontTyped, outside⟩ := ih tail
          exact ⟨middle, .push frame frontTyped, outside⟩
  | live owner q a saved scope rest ihSaved ihRest => cases typed with
      | live known scope saved tail =>
          obtain ⟨middle, frontTyped, outside⟩ := ihRest tail
          exact ⟨middle, .live known scope saved frontTyped, outside⟩
  | spent owner a scope rest ih => cases typed with
      | spent known scope tail =>
          obtain ⟨middle, frontTyped, outside⟩ := ih tail
          exact ⟨middle, .spent known scope frontTyped, outside⟩

/-- Exact executable selection preserves typing of the actual captured code,
    selected clauses, and outside stack, rather than only their port erasure. -/
theorem handler_cut_retains_typing
    (cut : HandlerCut requested whole cap tail handler)
    (typed : StackTyped signature tickets whole input result) :
    StackTyped signature tickets cap input handler.answer ∧
      StackTyped signature tickets tail handler.answer result ∧
      FrameTyped signature tickets (.handler handler) := by
  induction cut generalizing input result with
  | hit handler tail same => cases typed with
      | push frame rest => exact ⟨.push frame .nil, rest, frame⟩
  | push entry rest cap tail handler miss next ih => cases typed with
      | push frame rest =>
          obtain ⟨saved, outside, handlerTyped⟩ := ih rest
          exact ⟨.push frame saved, outside, handlerTyped⟩
  | live owner q a saved scope rest cap tail handler next ih => cases typed with
      | live known scope saved rest =>
          obtain ⟨inside, outside, handlerTyped⟩ := ih rest
          exact ⟨.live known scope saved inside, outside, handlerTyped⟩
  | spent owner a scope rest cap tail handler next ih => cases typed with
      | spent known scope rest =>
          obtain ⟨inside, outside, handlerTyped⟩ := ih rest
          exact ⟨.spent known scope inside, outside, handlerTyped⟩

theorem resume_retains_stack_typing {front cap tail : Stack}
    (typed : StackTyped signature tickets
      (front.append (.live owner input answer cap callerScope tail)) answer result) :
    StackTyped signature tickets
      (cap.append (front.append (.spent owner answer callerScope tail))) input result := by
  obtain ⟨middle, frontTyped, outside⟩ := stack_typed_decompose front typed
  cases outside with
  | live known scope saved rest =>
      exact stack_typed_append saved (stack_typed_append frontTyped (.spent known scope rest))

theorem focus_is_not_value (focus : Focus whole child context) : ¬ whole.IsValue := by
  cases focus <;> simp_all [Expr.IsValue]

/-- Every raw transition whose current expression is a closed value preserves
    the retained-code type judgment. This covers plugging, scope exit, cleanup
    application/completion, clause exit, close completion and ticket retirement.
    It does not assert preservation of a common immediate effect bound. -/
theorem raw_value_step_preserves_typing
    (step : RawStep before after created discharged)
    (closed : ClosedValue before.expression)
    (typed : ConfigurationTyped signature tickets before result) :
    ConfigurationTyped signature tickets after result := by
  obtain ⟨input, expression, stack⟩ := typed
  cases step with
  | focus plain focus tail => exact False.elim (focus_is_not_value focus closed.1)
  | bind | beta | ifTrue | ifFalse | enterHandler | enterCell | enterCleanup
  | capture | resume | discard | readCell | writeCell => cases closed.1
  | plug plain value valueClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | plain scopeTyped context =>
              have valueTyped := at_type_closed_value expression valueClosed
              exact ⟨_, .checked scopeTyped (context_plug_typed context
                (typed_value_transport valueTyped valueClosed.1 _ _)), rest⟩
  | leaveHandler handler value valueClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | handler caller clauses coverage unique =>
              exact ⟨_, at_type_value_transport expression valueClosed caller, rest⟩
  | leaveCell identity payload answer savedScope scope value valueClosed tail => cases stack with
      | push frame rest => cases frame with
          | cell caller noEscape => exact ⟨_, at_type_value_transport expression valueClosed caller, rest⟩
  | startCleanup action saved savedClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | armed caller callable =>
              exact ⟨.unit, .checked .none (.app
                (typed_value_transport callable action.closed.1 .none action.requests) .unit (fun _ used => used)),
                .push (.running caller callable (at_type_closed_value expression savedClosed)) rest⟩
  | finishCleanup action saved savedClosed scope tail => cases stack with
      | push frame rest => cases frame with
          | running caller callable savedTyped =>
              obtain ⟨ticket, scopeTyped⟩ := caller
              exact ⟨_, .checked scopeTyped (typed_value_transport savedTyped savedClosed.1 ticket []), rest⟩
  | leaveClause owner answer value valueClosed scope callerScope tail => cases stack with
      | spent known caller rest => exact ⟨_, at_type_value_transport expression valueClosed caller, rest⟩
  | finishClose identity scope callerScope tail => cases stack with
      | push frame rest => cases frame with
          | closing caller => exact ⟨_, at_type_value_transport expression closed caller, rest⟩
  | retire owner scope tail => cases stack with
      | push frame rest => exact ⟨_, expression, rest⟩

/-- Static ticket types and the actual saved input/answer agree through the
    historical owner signature. This is value-type preservation, independent
    of the usage/ownership proofs for consuming the live owner. -/
theorem resume_preserves_configuration_typing {front cap tail : Stack}
    (resolved : scope.resolve binder = some owner)
    (typed : ConfigurationTyped signature tickets
      ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩ result) :
    ConfigurationTyped signature tickets
      ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩ result := by
  obtain ⟨expressionType, expression, stack⟩ := typed
  cases expression with
  | checked scopeType expression =>
      cases expression with
      | resume operand effects =>
          cases scopeType with
          | bound known =>
              simp [Scope.resolve] at resolved
              subst owner
              obtain ⟨middle, frontTyped, outside⟩ := stack_typed_decompose front stack
              cases outside with
              | live actual caller saved rest =>
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans actual))
                  exact ⟨_, .checked (.bound known) operand,
                    stack_typed_append saved (stack_typed_append frontTyped (.spent known caller rest))⟩

/-- Adding a fresh ticket signature preserves existing scope interpretations.
    The table records historical types; it does not grant a live capability. -/
def TicketExtension (before after : TicketSignatures) : Prop :=
  ∀ owner input answer, before owner = some (input, answer) → after owner = some (input, answer)

theorem scope_typed_extension (scope : ScopeTyped before runtimeScope ticket)
    (extension : TicketExtension before after) : ScopeTyped after runtimeScope ticket := by
  cases scope with
  | none => exact .none
  | bound known => exact .bound (extension _ _ _ known)

theorem scope_known_extension (scope : ScopeKnown before runtimeScope)
    (extension : TicketExtension before after) : ScopeKnown after runtimeScope := by
  obtain ⟨ticket, scope⟩ := scope
  exact ⟨ticket, scope_typed_extension scope extension⟩

theorem at_type_extension (typed : AtType signature before scope expression type)
    (extension : TicketExtension before after) : AtType signature after scope expression type := by
  cases typed with
  | checked scope expression => exact .checked (scope_typed_extension scope extension) expression

theorem frame_typed_extension (typed : FrameTyped signature before frame)
    (extension : TicketExtension before after) : FrameTyped signature after frame := by
  cases typed with
  | plain scope context => exact .plain (scope_typed_extension scope extension) context
  | handler scope clauses coverage unique =>
      exact .handler (scope_known_extension scope extension) clauses coverage unique
  | cell scope noEscape => exact .cell (scope_known_extension scope extension) noEscape
  | armed scope callable => exact .armed (scope_known_extension scope extension) callable
  | running scope callable saved => exact .running (scope_known_extension scope extension) callable saved
  | closing scope => exact .closing (scope_known_extension scope extension)
  | retiring known => exact .retiring (extension _ _ _ known)

theorem stack_typed_extension (typed : StackTyped signature before stack input result)
    (extension : TicketExtension before after) : StackTyped signature after stack input result := by
  induction typed with
  | nil => exact .nil
  | push frame rest ih => exact .push (frame_typed_extension frame extension) ih
  | live known scope saved rest ihSaved ihRest =>
      exact .live (extension _ _ _ known) (scope_known_extension scope extension) ihSaved ihRest
  | spent known scope rest ih => exact .spent (extension _ _ _ known) (scope_known_extension scope extension) ih

def TicketSignatures.insert (tickets : TicketSignatures) (owner : Nat) (input answer : Ty) : TicketSignatures :=
  fun name => if name = owner then some (input, answer) else tickets name

theorem fresh_ticket_signature_extension (fresh : tickets owner = none) :
    TicketExtension tickets (tickets.insert owner input answer) := by
  intro name oldInput oldAnswer known
  by_cases same : name = owner
  · subst name
    simp [fresh] at known
  · simp [TicketSignatures.insert, same, known]

theorem scope_typed_resolves
    (scopeTyped : ScopeTyped tickets scope (.bound binder input answer residual closing))
    (resolved : scope.resolve binder = some owner) : tickets owner = some (input, answer) := by
  cases scopeTyped with
  | bound known =>
      simp [Scope.resolve] at resolved
      subst owner
      exact known

/-- A typed request and the actual retained handler derive a typed capture
    configuration. The new historical ticket entry preserves all old stored
    code. Name freshness, resource support and continuation usage remain
    independent judgments to compose with this construction. -/
theorem capture_constructs_typed_configuration
    (cut : HandlerCut requested whole cap tail handler)
    (typed : ConfigurationTyped signature tickets ⟨.perform requested operation operand, scope, whole⟩ result)
    (closed : ClosedValue operand)
    (hygiene : ∀ parameter binder body, ClauseAt operation handler.clauses parameter binder body →
      ClosedExcept parameter body ∧ ResourceFresh operand body)
    (fresh : tickets owner = none) :
    ∃ (parameter binder : Nat) (body : Expr) (output : Ty),
      let extended := tickets.insert owner output handler.answer
      RawStep ⟨.perform requested operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner output handler.answer cap handler.scope tail⟩ [.ticket owner] [] ∧
      TicketExtension tickets extended ∧
      ConfigurationTyped signature extended
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner output handler.answer cap handler.scope tail⟩ result := by
  obtain ⟨output, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | perform operationType available operandTyped =>
          obtain ⟨saved, outside, handlerTyped⟩ := handler_cut_retains_typing cut stack
          cases handlerTyped with
          | handler caller clauses coverage unique =>
              have known := operationType
              rw [← handler_cut_instance cut] at known
              obtain ⟨parameter, binder, body, selected⟩ := covered_operation_selects_clause coverage known
              obtain ⟨ready, resourceFresh⟩ := hygiene parameter binder body selected
              have extension := fresh_ticket_signature_extension (input := output) (answer := handler.answer) fresh
              have newTicket : (tickets.insert owner output handler.answer) owner = some (output, handler.answer) := by
                simp [TicketSignatures.insert]
              exact ⟨parameter, binder, body, output,
                .capture requested operation parameter binder owner operand body scope whole cap tail handler output
                  cut selected closed ready resourceFresh,
                extension, handler.answer,
                .checked (.bound newTicket)
                  (selected_clause_substitution_typed selected clauses known operandTyped closed),
                .live newTicket (scope_known_extension caller extension)
                  (stack_typed_extension saved extension) (stack_typed_extension outside extension)⟩

def TicketSignaturesBacked (tickets : TicketSignatures) (issued : List Owner) : Prop :=
  ∀ owner input answer, tickets owner = some (input, answer) → Owner.ticket owner ∈ issued

theorem fresh_owner_has_no_ticket_signature
    (backed : TicketSignaturesBacked tickets issued) (fresh : Owner.ticket owner ∉ issued) :
    tickets owner = none := by
  cases known : tickets owner with
  | none => rfl
  | some pair => exact False.elim (fresh (backed owner pair.1 pair.2 known))

theorem inserted_ticket_signature_is_backed
    (backed : TicketSignaturesBacked tickets issued) :
    TicketSignaturesBacked (tickets.insert owner input answer) (issued ++ [Owner.ticket owner]) := by
  intro name oldInput oldAnswer known
  by_cases same : name = owner
  · subst name
    exact List.mem_append_right _ (by simp)
  · exact List.mem_append_left _ (backed name oldInput oldAnswer
      (by simpa [TicketSignatures.insert, same] using known))

/-- A value returning through a typed cell frame satisfies the resource
    release check. This premise is derived from actual code and result typing. -/
theorem typed_cell_return_excludes_identity
    (typed : ConfigurationTyped signature tickets
      ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ result)
    (closed : ClosedValue value) : identity ∉ resourceDependencies value.dependencies := by
  obtain ⟨input, expression, stack⟩ := typed
  cases stack with
  | push frame rest => cases frame with
      | cell known noEscape =>
          exact typed_return_excludes_resource (at_type_closed_value expression closed) closed noEscape

/-- Retained executable contents of a generated plan. Outward effect bounds,
    callback usage, resource support and exact interpretation remain separate. -/
inductive PlanContentsTyped (signature : Signature) (tickets : TicketSignatures) : List CloseEntry → Prop where
  | nil : PlanContentsTyped signature tickets []
  | release (rest : PlanContentsTyped signature tickets tail) :
      PlanContentsTyped signature tickets (.release identity payload :: tail)
  | invoke (callable : Typed signature TypeEnv.empty .none [] action.action
      (.function .unit .unit action.requests retained)) (rest : PlanContentsTyped signature tickets tail) :
      PlanContentsTyped signature tickets (.invoke action :: tail)
  | retire (known : tickets owner = some (input, answer)) (rest : PlanContentsTyped signature tickets tail) :
      PlanContentsTyped signature tickets (.retire owner :: tail)

theorem plan_contents_append (left : PlanContentsTyped signature tickets front)
    (right : PlanContentsTyped signature tickets tail) : PlanContentsTyped signature tickets (front ++ tail) := by
  induction left with
  | nil => exact right
  | release rest ih => exact .release ih
  | invoke callable rest ih => exact .invoke callable ih
  | retire known rest ih => exact .retire known ih

theorem make_plan_retains_types (typed : StackTyped signature tickets stack input result)
    (built : makePlan stack = some plan) : PlanContentsTyped signature tickets plan := by
  induction typed generalizing plan with
  | nil => cases built; exact .nil
  | @push entry tail result frame rest ih =>
      cases frame with
      | plain scope context | handler scope clauses coverage unique => exact ih built
      | cell scope noEscape =>
          cases tailPlan : makePlan tail with
          | none => simp [makePlan, tailPlan] at built
          | some remaining =>
              simp only [makePlan, tailPlan, Option.some.injEq] at built
              subst plan
              exact .release (ih tailPlan)
      | armed scope callable =>
          cases tailPlan : makePlan tail with
          | none => simp [makePlan, tailPlan] at built
          | some remaining =>
              simp only [makePlan, tailPlan, Option.some.injEq] at built
              subst plan
              exact .invoke callable (ih tailPlan)
      | running | closing | retiring => simp [makePlan] at built
  | @live owner input answer callerScope capture tail result known scope saved rest ihSaved ihRest =>
      cases savedPlan : makePlan capture <;> cases tailPlan : makePlan tail <;>
        simp [makePlan, savedPlan, tailPlan] at built
      case some.some inside outside =>
        subst plan
        exact plan_contents_append (ihSaved savedPlan) (.retire known (ihRest tailPlan))
  | spent known scope rest ih => exact ih built

theorem close_control_retains_types (plan : PlanContentsTyped signature tickets entries)
    (scope : ScopeKnown tickets runtimeScope) :
    StackTyped signature tickets (closeControl runtimeScope entries) .unit .unit := by
  induction plan with
  | nil => exact .nil
  | release rest ih => exact .push (.cell scope (by simp [Ty.resources])) ih
  | invoke callable rest ih => exact .push (.armed scope callable) ih
  | retire known rest ih => exact .push (.retiring known) ih

/-- Disposal materializes typed callback contents and retirement frames from
    the actual captured stack. This is independent of whether the plan's
    resource access, interpretation, usage, and outward effects are admitted. -/
theorem discard_preserves_configuration_typing {front cap tail : Stack}
    (_resolved : scope.resolve binder = some owner)
    (built : makePlan cap = some plan)
    (typed : ConfigurationTyped signature tickets
      ⟨.discard binder, scope, front.append (.live owner input answer cap callerScope tail)⟩ result) :
    ConfigurationTyped signature tickets
      ⟨.unit, scope, (closeControl scope plan).append
        (.push (.closing closeId scope) (front.append (.spent owner answer callerScope tail)))⟩ result := by
  obtain ⟨expressionType, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | discard effects =>
          obtain ⟨middle, frontTyped, outside⟩ := stack_typed_decompose front stack
          cases outside with
          | live known caller saved rest =>
              exact ⟨.unit, .checked scopeTyped (Typed.unit (allowed := [])),
                stack_typed_append (close_control_retains_types (make_plan_retains_types saved built) ⟨_, scopeTyped⟩)
                  (.push (.closing ⟨_, scopeTyped⟩) (stack_typed_append frontTyped (.spent known caller rest)))⟩

namespace RetainedExamples
open Ash.OneShot.Execution.Examples

def noTickets : TicketSignatures := fun _ => none
def withCapturedTicket : TicketSignatures := noTickets.insert 3 .unit .integer

theorem callback_has_type : Typed Examples.unitRequestSignature TypeEnv.empty .none [] callback
    (.function .unit .unit action.requests []) := by
  apply Typed.lambda
  · apply Typed.perform (input := .unit)
    · simp [Examples.unitRequestSignature]
    · simp [action]
    · exact .unit
  · simp [callbackBody, retainedSupport, Expr.dependencies, without,
      instanceDependencies, Instance.resources]

theorem running_capture_has_typed_code :
    StackTyped Examples.unitRequestSignature tickets captureStack .unit .integer := by
  apply StackTyped.push
    (FrameTyped.running ⟨_, .none⟩ callback_has_type (.integer))
  exact .push (.handler ⟨_, .none⟩ DispatchExamples.cleanup_clauses_typed
    (by
      intro operation input output known
      simp only [Examples.unitRequestSignature, handler] at known
      split at known
      · rename_i equal
        simp [handler, clauseKeys, clauses, equal.2]
      · cases known)
    (by decide)) .nil

theorem captured_clause_has_typed_configuration :
    ConfigurationTyped Examples.unitRequestSignature withCapturedTicket capturedState .integer := by
  have known : withCapturedTicket 3 = some (.unit, .integer) := rfl
  exact ⟨.integer, .checked (.bound (residual := []) (closing := []) known)
    (.resume .unit (fun _ used => used)),
    .live known ⟨_, .none⟩ running_capture_has_typed_code .nil⟩

/-- Capture is constructed from a typed request and actual retained stack,
    starting with an empty historical ticket table. -/
theorem cleanup_request_constructs_typed_capture :
    ∃ (parameter binder : Nat) (body : Expr) (output : Ty),
      RawStep ⟨.perform (.user 1 []) 0 .unit, .none, captureStack⟩
        ⟨body.subst parameter .unit, .ticket binder 3,
          .live 3 output handler.answer captureStack handler.scope .nil⟩ [.ticket 3] [] ∧
      TicketExtension noTickets (noTickets.insert 3 output handler.answer) ∧
      ConfigurationTyped Examples.unitRequestSignature (noTickets.insert 3 output handler.answer)
        ⟨body.subst parameter .unit, .ticket binder 3,
          .live 3 output handler.answer captureStack handler.scope .nil⟩ .integer := by
  apply capture_constructs_typed_configuration
    (HandlerCut.push _ _ _ _ _ (by simp [ExecFrame.erase, Frame.target]) (.hit handler .nil rfl))
  · exact ⟨.unit, .checked ScopeTyped.none
      (.perform (allowed := [.user 1 []]) (by simp [Examples.unitRequestSignature, handler])
        (by simp [handler]) Typed.unit),
      running_capture_has_typed_code⟩
  · exact closed_unit
  · intro parameter binder body selected
    cases selected with
    | hit => simp [ClosedExcept, Expr.dependencies, ResourceFresh]
    | pass different next => exact False.elim (different rfl)
  · rfl

theorem cleanup_resumption_and_completion_typed :
    ConfigurationTyped Examples.unitRequestSignature withCapturedTicket ⟨.integer 42, .none, .nil⟩ .integer := by
  have resumed := resume_preserves_configuration_typing
    (front := .nil) (by rfl) captured_clause_has_typed_configuration
  have completed := raw_value_step_preserves_typing
    (RawStep.finishCleanup action (.integer 42) (closed_integer 42) (.ticket 9 3)
      (.push (.handler handler) spentStack)) closed_unit resumed
  have returned := raw_value_step_preserves_typing
    (RawStep.leaveHandler handler (.integer 42) (closed_integer 42) .none spentStack)
    (closed_integer 42) completed
  exact raw_value_step_preserves_typing
    (RawStep.leaveClause 3 .integer (.integer 42) (closed_integer 42) .none .none .nil)
    (closed_integer 42) returned

def invalidAction : ActionData := ⟨7, .integer 0, closed_integer 0, .none, .integer, []⟩

theorem ports_do_not_establish_callable_cleanup :
    Fits (Stack.push (.armed invalidAction) .nil).erase .integer .integer ∧
      ¬ FrameTyped Examples.unitRequestSignature noTickets (.armed invalidAction) := by
  refine ⟨.push _ _ _ (.nil _), ?_⟩
  intro frame
  cases frame with
  | armed scope callable => cases callable

theorem ports_do_not_type_saved_results :
    Fits (Stack.push (.running action (.boolean true)
      (by simp [ClosedValue, Expr.IsValue, Expr.dependencies])) .nil).erase .unit .integer ∧
    ¬ FrameTyped Examples.unitRequestSignature noTickets (.running action (.boolean true)
      (by simp [ClosedValue, Expr.IsValue, Expr.dependencies])) := by
  refine ⟨.push _ _ _ (.nil _), ?_⟩
  intro frame
  cases frame with
  | running scope callable saved => cases saved

theorem typed_cell_frame_rejects_escaping_answer :
    ¬ FrameTyped Examples.unitRequestSignature noTickets (.cell 4 0 .none (.reference 4)) := by
  intro frame
  cases frame with
  | cell scope noEscape => simp [Ty.resources] at noEscape

def userAndCells : Signature := withCellSignatures Examples.unitRequestSignature
def withDiscardTicket : TicketSignatures := noTickets.insert 3 .unit .unit

theorem read_callback_retained_type : Typed userAndCells TypeEnv.empty .none [] readCallback
    (.function .unit .unit readAction.requests [4]) := by
  apply Typed.lambda
  · apply Typed.bind (input := .integer)
    · exact .perform rfl (by simp [readAction]) .reference
    · exact .unit
  · simp [readBody, retainedSupport, Expr.dependencies, without, instanceDependencies, Instance.resources]

theorem abandoned_cell_stack_has_typed_code :
    StackTyped userAndCells tickets abandoned .unit .unit := by
  apply StackTyped.push (.armed ⟨_, .none⟩ read_callback_retained_type)
  apply StackTyped.push (.cell ⟨_, .none⟩ (by simp [Ty.resources]))
  apply StackTyped.push
  · apply FrameTyped.handler ⟨_, .none⟩
    · apply ClausesTyped.cons (input := .unit) (output := .unit) (residual := [])
      · rfl
      · exact .discard (fun _ used => used)
      · exact .nil
    · intro operation input output known
      simp only [userAndCells, withCellSignatures, discardHandler, Examples.unitRequestSignature] at known
      split at known
      · rename_i equal
        simp [discardHandler, clauseKeys, equal.2]
      · cases known
    · decide
  · exact .nil

/-- The resource-reading disposal plan retains checked callback code and
    correctly typed cell/close frames when it is materialized. -/
theorem cell_disposal_materializes_typed_code :
    ConfigurationTyped userAndCells withDiscardTicket
      ⟨.unit, closeScope, (closeControl closeScope closePlan).append closeTail⟩ .unit := by
  have known : withDiscardTicket 3 = some (.unit, .unit) := rfl
  have before : ConfigurationTyped userAndCells withDiscardTicket
      ⟨.discard 9, closeScope, .live 3 .unit .unit abandoned .none .nil⟩ .unit :=
    ⟨.unit, .checked (.bound (residual := []) (closing := []) known)
      (.discard (allowed := []) (fun _ used => used)),
      .live known ⟨_, .none⟩ abandoned_cell_stack_has_typed_code .nil⟩
  exact discard_preserves_configuration_typing (front := .nil) rfl rfl before

end RetainedExamples

end Ash.OneShot.Typing

#print axioms Ash.OneShot.Typing.handler_cut_retains_typing
#print axioms Ash.OneShot.Typing.resume_retains_stack_typing
#print axioms Ash.OneShot.Typing.raw_value_step_preserves_typing
#print axioms Ash.OneShot.Typing.resume_preserves_configuration_typing
#print axioms Ash.OneShot.Typing.stack_typed_extension
#print axioms Ash.OneShot.Typing.capture_constructs_typed_configuration
#print axioms Ash.OneShot.Typing.typed_cell_return_excludes_identity
#print axioms Ash.OneShot.Typing.RetainedExamples.cleanup_request_constructs_typed_capture
#print axioms Ash.OneShot.Typing.RetainedExamples.cleanup_resumption_and_completion_typed
#print axioms Ash.OneShot.Typing.make_plan_retains_types
#print axioms Ash.OneShot.Typing.discard_preserves_configuration_typing
#print axioms Ash.OneShot.Typing.RetainedExamples.cell_disposal_materializes_typed_code
