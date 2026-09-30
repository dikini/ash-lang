import ScopedReadiness

/-!
Typing of actual scoped retained code and captured stacks. Historical ticket
ports are reused from the administrative model because runtime ticket scopes
have the same representation. Expression syntax and retained frames are the
scoped machine's actual objects. This layer checks value-type composition;
connected effect, ownership, access, and usage invariants remain separate.
-/

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (Signature TypeEnv TicketType TicketSignatures ScopeTyped ScopeKnown TicketExtension
  scope_typed_extension scope_known_extension fresh_ticket_signature_extension)

theorem scope_typed_names_match (typed : ScopeTyped tickets scope ticket) : ScopeNamesMatch ticket scope := by
  cases typed with
  | none => exact .none
  | bound => exact .bound

/-- Immediate effect bounds are retained existentially. This judgment alone
    makes no claim that surrounding interpretations provide those effects. -/
inductive AtType (signature : Signature) (tickets : TicketSignatures) (world : World) : Scope → Code → Ty → Prop where
  | checked (scope : ScopeTyped tickets runtimeScope ticket)
      (typed : Typed signature world TypeEnv.empty ticket allowed expression type) :
      AtType signature tickets world runtimeScope expression type

theorem at_type_scope_known (typed : AtType signature tickets world scope expression type) :
    ScopeKnown tickets scope := by
  cases typed with
  | checked scope typed => exact ⟨_, scope⟩

theorem at_type_value_transport (typed : AtType signature tickets world scope value type)
    (closed : ScopedExpressions.ClosedValue value) (destination : ScopeKnown tickets otherScope) :
    AtType signature tickets world otherScope value type := by
  obtain ⟨ticket, scopeTyped⟩ := destination
  cases typed with
  | checked scope valueTyped => exact .checked scopeTyped (typed_value_transport valueTyped closed.1 ticket [])

theorem at_type_closed_value (typed : AtType signature tickets world scope value type)
    (closed : ScopedExpressions.ClosedValue value) : Typed signature world TypeEnv.empty .none [] value type := by
  cases typed with
  | checked scope valueTyped => exact typed_value_transport valueTyped closed.1 .none []

/-- Every actual payload is checked. Cell results exclude the local identity;
    running cleanup also retains a typed saved result. -/
inductive FrameTyped (signature : Signature) (tickets : TicketSignatures) (world : World) : ExecFrame → Prop where
  | plain (scope : ScopeTyped tickets data.scope ticket)
      (context : ContextTyped signature world TypeEnv.empty ticket allowed data.context data.input data.output) :
      FrameTyped signature tickets world (.plain data)
  | handler (scope : ScopeKnown tickets handler.scope)
      (clauses : ClausesTyped signature world TypeEnv.empty handler.effectInst handler.answer residual handler.clauses)
      (coverage : Covers signature handler.effectInst handler.clauses)
      (unique : (clauseKeys handler.clauses).Nodup) : FrameTyped signature tickets world (.handler handler)
  | cell (scope : ScopeKnown tickets runtimeScope) (noEscape : identity ∉ answer.resources) :
      FrameTyped signature tickets world (.cell identity payload runtimeScope answer)
  | armed (scope : ScopeKnown tickets action.scope)
      (callable : Typed signature world TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests retained)) : FrameTyped signature tickets world (.armed action)
  | running (scope : ScopeKnown tickets action.scope)
      (callable : Typed signature world TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests retained))
      (result : Typed signature world TypeEnv.empty .none [] saved action.answer) :
      FrameTyped signature tickets world (.running action saved closed)
  | closing (scope : ScopeKnown tickets runtimeScope) : FrameTyped signature tickets world (.closing identity runtimeScope)
  | retiring (known : tickets owner = some (input, answer)) : FrameTyped signature tickets world (.retiring owner)

/-- Port composition now requires typing the stored code and all dormant
    captures, in addition to agreeing on annotated input/answer types. -/
inductive StackTyped (signature : Signature) (tickets : TicketSignatures) (world : World) : Stack → Ty → Ty → Prop where
  | nil : StackTyped signature tickets world .nil type type
  | push (frame : FrameTyped signature tickets world entry)
      (rest : StackTyped signature tickets world tail entry.erase.output result) :
      StackTyped signature tickets world (.push entry tail) entry.erase.input result
  | live (known : tickets owner = some (input, answer)) (scope : ScopeKnown tickets callerScope)
      (saved : StackTyped signature tickets world capture input answer)
      (rest : StackTyped signature tickets world tail answer result) :
      StackTyped signature tickets world (.live owner input answer capture callerScope tail) answer result
  | spent (known : tickets owner = some (input, answer)) (scope : ScopeKnown tickets callerScope)
      (rest : StackTyped signature tickets world tail answer result) :
      StackTyped signature tickets world (.spent owner answer callerScope tail) answer result

def ConfigurationTyped (signature : Signature) (tickets : TicketSignatures) (world : World)
    (configuration : Configuration) (result : Ty) : Prop :=
  ∃ input, AtType signature tickets world configuration.scope configuration.expression input ∧
    StackTyped signature tickets world configuration.stack input result

theorem stack_typing_gives_ports (typed : StackTyped signature tickets world stack input result) :
    Fits stack.erase input result := by
  induction typed with
  | nil => exact .nil _
  | push frame rest ih => exact .push _ _ _ ih
  | live known scope saved rest ihSaved ihRest => exact .live _ _ _ _ _ _ ihSaved ihRest
  | spent known scope rest ih => exact .spent _ _ _ _ ih

theorem stack_typed_append
    (front : StackTyped signature tickets world left input middle)
    (tail : StackTyped signature tickets world right middle result) :
    StackTyped signature tickets world (left.append right) input result := by
  induction front with
  | nil => exact tail
  | push frame rest ih => exact .push frame (ih tail)
  | live known scope saved rest ihSaved ihRest => exact .live known scope saved (ihRest tail)
  | spent known scope rest ih => exact .spent known scope (ih tail)

theorem stack_typed_decompose (front : Stack)
    (typed : StackTyped signature tickets world (front.append tail) input result) :
    ∃ middle, StackTyped signature tickets world front input middle ∧
      StackTyped signature tickets world tail middle result := by
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
    (typed : StackTyped signature tickets world whole input result) :
    StackTyped signature tickets world cap input handler.answer ∧
      StackTyped signature tickets world tail handler.answer result ∧
      FrameTyped signature tickets world (.handler handler) := by
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
    (typed : StackTyped signature tickets world
      (front.append (.live owner input answer cap callerScope tail)) answer result) :
    StackTyped signature tickets world
      (cap.append (front.append (.spent owner answer callerScope tail))) input result := by
  obtain ⟨middle, frontTyped, outside⟩ := stack_typed_decompose front typed
  cases outside with
  | live known scope saved rest =>
      exact stack_typed_append saved (stack_typed_append frontTyped (.spent known scope rest))

theorem focus_is_not_value (focus : Focus whole child context) : ¬ whole.IsValue := by
  cases focus <;> simp_all [Code.IsValue]

/-- Every raw transition whose current expression is a closed value preserves
    the retained-code type judgment. This covers plugging, scope exit, cleanup
    application/completion, clause exit, close completion and ticket retirement.
    It does not assert preservation of a common immediate effect bound. -/
theorem raw_value_step_preserves_typing
    (step : RawStep before after created discharged)
    (closed : ScopedExpressions.ClosedValue before.expression)
    (typed : ConfigurationTyped signature tickets world before result) :
    ConfigurationTyped signature tickets world after result := by
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
    (typed : ConfigurationTyped signature tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩ result) :
    ConfigurationTyped signature tickets world
      ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩ result := by
  obtain ⟨expressionType, expression, stack⟩ := typed
  cases expression with
  | checked scopeType expression =>
      cases expression with
      | resume operand effects formed =>
          cases scopeType with
          | bound known =>
              simp [Execution.Scope.resolve] at resolved
              subst owner
              obtain ⟨middle, frontTyped, outside⟩ := stack_typed_decompose front stack
              cases outside with
              | live actual caller saved rest =>
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans actual))
                  exact ⟨_, .checked (.bound known) operand,
                    stack_typed_append saved (stack_typed_append frontTyped (.spent known caller rest))⟩

theorem at_type_extension (typed : AtType signature before world scope expression type)
    (extension : TicketExtension before after) : AtType signature after world scope expression type := by
  cases typed with
  | checked scope expression => exact .checked (scope_typed_extension scope extension) expression

theorem frame_typed_extension (typed : FrameTyped signature before world frame)
    (extension : TicketExtension before after) : FrameTyped signature after world frame := by
  cases typed with
  | plain scope context => exact .plain (scope_typed_extension scope extension) context
  | handler scope clauses coverage unique =>
      exact .handler (scope_known_extension scope extension) clauses coverage unique
  | cell scope noEscape => exact .cell (scope_known_extension scope extension) noEscape
  | armed scope callable => exact .armed (scope_known_extension scope extension) callable
  | running scope callable saved => exact .running (scope_known_extension scope extension) callable saved
  | closing scope => exact .closing (scope_known_extension scope extension)
  | retiring known => exact .retiring (extension _ _ _ known)

theorem stack_typed_extension (typed : StackTyped signature before world stack input result)
    (extension : TicketExtension before after) : StackTyped signature after world stack input result := by
  induction typed with
  | nil => exact .nil
  | push frame rest ih => exact .push (frame_typed_extension frame extension) ih
  | live known scope saved rest ihSaved ihRest =>
      exact .live (extension _ _ _ known) (scope_known_extension scope extension) ihSaved ihRest
  | spent known scope rest ih => exact .spent (extension _ _ _ known) (scope_known_extension scope extension) ih

/-- Retained executable contents of a generated plan. Outward effect bounds,
    callback usage, resource support and exact interpretation remain separate. -/
inductive PlanContentsTyped (signature : Signature) (tickets : TicketSignatures) (world : World) : List CloseEntry → Prop where
  | nil : PlanContentsTyped signature tickets world []
  | release (rest : PlanContentsTyped signature tickets world tail) :
      PlanContentsTyped signature tickets world (.release identity payload :: tail)
  | invoke (callable : Typed signature world TypeEnv.empty .none [] action.action
      (.function .unit .unit action.requests retained)) (rest : PlanContentsTyped signature tickets world tail) :
      PlanContentsTyped signature tickets world (.invoke action :: tail)
  | retire (known : tickets owner = some (input, answer)) (rest : PlanContentsTyped signature tickets world tail) :
      PlanContentsTyped signature tickets world (.retire owner :: tail)

theorem plan_contents_append (left : PlanContentsTyped signature tickets world front)
    (right : PlanContentsTyped signature tickets world tail) : PlanContentsTyped signature tickets world (front ++ tail) := by
  induction left with
  | nil => exact right
  | release rest ih => exact .release ih
  | invoke callable rest ih => exact .invoke callable ih
  | retire known rest ih => exact .retire known ih

theorem make_plan_retains_types (typed : StackTyped signature tickets world stack input result)
    (built : makePlan stack = some plan) : PlanContentsTyped signature tickets world plan := by
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

theorem close_control_retains_types (plan : PlanContentsTyped signature tickets world entries)
    (scope : ScopeKnown tickets runtimeScope) :
    StackTyped signature tickets world (closeControl runtimeScope entries) .unit .unit := by
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
    (typed : ConfigurationTyped signature tickets world
      ⟨.discard binder, scope, front.append (.live owner input answer cap callerScope tail)⟩ result) :
    ConfigurationTyped signature tickets world
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


end Ash.OneShot.ScopedTyping

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (Signature TypeEnv TicketType TicketSignatures ScopeTyped ScopeKnown TicketExtension
  scope_known_extension fresh_ticket_signature_extension)

theorem clauses_world_weaken
    (typed : ClausesTyped signature world environment effect answer residual clauses) (larger : world ⊆ next) :
    ClausesTyped signature next environment effect answer residual clauses := by
  cases clauses with
  | nil => exact .nil
  | cons operation parameter binder body rest => cases typed with
      | cons operation body rest =>
          exact .cons operation (typed_world_weaken body next larger) (clauses_world_weaken rest larger)
termination_by sizeOf clauses

theorem context_world_weaken
    (typed : ContextTyped signature world environment ticket allowed context input output) (larger : world ⊆ next) :
    ContextTyped signature next environment ticket allowed context input output := by
  cases typed with
  | pairLeft right => exact .pairLeft (typed_world_weaken right next larger)
  | pairRight left => exact .pairRight (typed_world_weaken left next larger)
  | appFunction argument effects => exact .appFunction (typed_world_weaken argument next larger) effects
  | appArgument function effects => exact .appArgument (typed_world_weaken function next larger) effects
  | bind suffix => exact .bind (typed_world_weaken suffix next larger)
  | branch yes no => exact .branch (typed_world_weaken yes next larger) (typed_world_weaken no next larger)
  | perform operation available formed => exact .perform operation available (in_world_mono formed larger)
  | resume effects formed => exact .resume effects (in_world_mono formed larger)
  | resource body resultBound effectsBound effects =>
      refine .resource ?_ (in_world_mono resultBound larger) (List.Subset.trans effectsBound larger) effects
      intro identity fresh
      exact typed_world_weaken (body identity (fun member => fresh (larger member))) _
        (append_subset larger (List.Subset.refl _))
  | cleanup body effects => exact .cleanup (typed_world_weaken body next larger) effects

theorem at_type_world_weaken (typed : AtType signature tickets world scope expression type) (larger : world ⊆ next) :
    AtType signature tickets next scope expression type := by
  cases typed with
  | checked scope expression => exact .checked scope (typed_world_weaken expression next larger)

theorem frame_world_weaken (typed : FrameTyped signature tickets world frame) (larger : world ⊆ next) :
    FrameTyped signature tickets next frame := by
  cases typed with
  | plain scope context => exact .plain scope (context_world_weaken context larger)
  | handler scope clauses coverage unique => exact .handler scope (clauses_world_weaken clauses larger) coverage unique
  | cell scope noEscape => exact .cell scope noEscape
  | armed scope callable => exact .armed scope (typed_world_weaken callable next larger)
  | running scope callable saved => exact .running scope (typed_world_weaken callable next larger) (typed_world_weaken saved next larger)
  | closing scope => exact .closing scope
  | retiring known => exact .retiring known

theorem stack_world_weaken (typed : StackTyped signature tickets world stack input result) (larger : world ⊆ next) :
    StackTyped signature tickets next stack input result := by
  induction typed with
  | nil => exact .nil
  | push frame rest ih => exact .push (frame_world_weaken frame larger) ih
  | live known scope saved rest ihSaved ihRest => exact .live known scope ihSaved ihRest
  | spent known scope rest ih => exact .spent known scope ih

theorem configuration_world_weaken (typed : ConfigurationTyped signature tickets world configuration result)
    (larger : world ⊆ next) : ConfigurationTyped signature tickets next configuration result := by
  obtain ⟨input, expression, stack⟩ := typed
  exact ⟨input, at_type_world_weaken expression larger, stack_world_weaken stack larger⟩

theorem at_type_value_closed (typed : AtType signature tickets world scope value type) (isValue : value.IsValue) :
    ScopedExpressions.ClosedValue value := by
  cases typed with | checked scope expression => exact typed_value_closed expression isValue

theorem raw_value_step_typed
    (step : RawStep before after created discharged) (isValue : before.expression.IsValue)
    (typed : ConfigurationTyped signature tickets world before result) :
    ConfigurationTyped signature tickets world after result := by
  obtain ⟨input, expression, stack⟩ := typed
  exact raw_value_step_preserves_typing step (at_type_value_closed expression isValue) ⟨input, expression, stack⟩

theorem typed_cell_return_excludes_identity
    (typed : ConfigurationTyped signature tickets world
      ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ result)
    (isValue : value.IsValue) : identity ∉ resourceDependencies value.dependencies := by
  obtain ⟨input, expression, stack⟩ := typed
  cases stack with
  | push frame rest => cases frame with
      | cell known noEscape => cases expression with
          | checked scope typed => exact typed_return_excludes_resource typed isValue noEscape

theorem handler_cut_instance (cut : HandlerCut requested whole cap tail handler) : handler.effectInst = requested := by
  induction cut with
  | hit handler tail same => exact same
  | push frame rest cap tail handler miss next ih => exact ih
  | live ticket q a saved scope rest cap tail handler next ih => exact ih
  | spent ticket a scope rest cap tail handler next ih => exact ih

theorem clause_at_of_key {clauses : ScopedExpressions.Clauses} (member : operation ∈ clauseKeys clauses) :
    ∃ parameter binder body, ScopedExecution.ClauseAt operation clauses parameter binder body := by
  cases clauses with
  | nil => cases member
  | cons other parameter binder body rest =>
      by_cases same : operation = other
      · subst other
        exact ⟨parameter, binder, body, .hit⟩
      · have inRest : operation ∈ clauseKeys rest := (List.mem_cons.mp member).resolve_left same
        obtain ⟨p, k, e, next⟩ := clause_at_of_key inRest
        exact ⟨p, k, e, .pass same next⟩
termination_by sizeOf clauses

theorem typed_perform_inversion
    (typed : Typed signature world environment ticket allowed (.perform (freezeEffect requested) operation operand) output) :
    ∃ input, signature requested operation = some (input, output) ∧ requested ∈ allowed ∧
      Typed signature world environment ticket allowed operand input := by
  generalize eq : freezeEffect requested = source at typed
  cases typed with
  | perform known available operand formed =>
      have same := freeze_effect_injective eq
      cases same
      exact ⟨_, known, available, operand⟩

/-- The actual typed handler cut and a value operand suffice for lexical
    capture readiness. Allocation freshness, support, permissions and usage
    still require their independent machine invariants. -/
theorem capture_constructs_typed_configuration
    (cut : HandlerCut requested whole cap tail handler)
    (typed : ConfigurationTyped signature tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result)
    (isValue : operand.IsValue) (fresh : tickets owner = none) :
    ∃ (parameter binder : Nat) (body : Code) (output : Ty),
      let extended := tickets.insert owner output handler.answer
      RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner output handler.answer cap handler.scope tail⟩ [.ticket owner] [] ∧
      TicketExtension tickets extended ∧
      ConfigurationTyped signature extended world
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner output handler.answer cap handler.scope tail⟩ result := by
  obtain ⟨output, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, operationType, available, operandTyped⟩ := typed_perform_inversion expression
      have closed := typed_value_closed operandTyped isValue
      obtain ⟨saved, outside, handlerTyped⟩ := handler_cut_retains_typing cut stack
      cases handlerTyped with
      | handler caller clauses coverage unique =>
          have known := operationType
          rw [← handler_cut_instance cut] at known
          obtain ⟨parameter, binder, body, selected⟩ := clause_at_of_key (coverage _ _ _ known)
          obtain ⟨clauseInput, clauseOutput, clauseKnown, bodyTyped⟩ := selected_clause_typed selected clauses
          have ready := typed_suffix_ready bodyTyped
          have extension := fresh_ticket_signature_extension (input := output) (answer := handler.answer) fresh
          have newTicket : (tickets.insert owner output handler.answer) owner = some (output, handler.answer) := by
            simp [Typing.TicketSignatures.insert]
          exact ⟨parameter, binder, body, output,
            .capture requested operation parameter binder owner operand body scope whole cap tail handler output cut selected closed ready,
            extension, handler.answer,
            .checked (.bound newTicket) (selected_clause_substitution_typed selected clauses known operandTyped closed),
            .live newTicket (scope_known_extension caller extension)
              (stack_typed_extension saved extension) (stack_typed_extension outside extension)⟩

end Ash.OneShot.ScopedTyping

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (Signature TypeEnv TicketType TicketSignatures ScopeTyped ScopeKnown)

/-- A strict focus constructs a retained frame in the same typed configuration. -/
theorem configuration_focus_progress
    (focus : ScopedExecution.Focus whole child context)
    (typed : ConfigurationTyped signature tickets world ⟨whole, scope, tail⟩ result) :
    ∃ plain : PlainData,
      RawStep ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩ [] [] ∧
      ConfigurationTyped signature tickets world ⟨child, scope, .push (.plain plain) tail⟩ result := by
  obtain ⟨input, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨plain, step, childTyped, contextTyped, output, shape, savedScope⟩ :=
        typed_focus_progress focus expression (scope_typed_names_match scopeTyped) tail
      have frame : FrameTyped signature tickets world (.plain plain) :=
        .plain (by rw [savedScope]; exact scopeTyped) (by rw [output]; exact contextTyped)
      exact ⟨plain, step, plain.input, .checked scopeTyped childTyped,
        .push frame (by simpa only [ExecFrame.erase, PlainData.erase, output] using stack)⟩

theorem configuration_bind_value_progress
    (typed : ConfigurationTyped signature tickets world ⟨.bind parameter value suffix, scope, tail⟩ result)
    (isValue : value.IsValue) :
    RawStep ⟨.bind parameter value suffix, scope, tail⟩ ⟨suffix.subst parameter value, scope, tail⟩ [] [] ∧
      ConfigurationTyped signature tickets world ⟨suffix.subst parameter value, scope, tail⟩ result := by
  obtain ⟨input, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨step, afterTyped⟩ := typed_bind_value_progress expression isValue scope tail
      exact ⟨step, input, .checked scopeTyped afterTyped, stack⟩

theorem configuration_application_value_progress
    (typed : ConfigurationTyped signature tickets world ⟨.app function argument, scope, tail⟩ result)
    (functionValue : function.IsValue) (argumentValue : argument.IsValue) :
    ∃ after, RawStep ⟨.app function argument, scope, tail⟩ ⟨after, .none, tail⟩ [] [] ∧
      ConfigurationTyped signature tickets world ⟨after, .none, tail⟩ result := by
  obtain ⟨input, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨after, step, afterTyped⟩ := typed_application_value_progress expression functionValue argumentValue scope tail
      exact ⟨after, step, input, .checked .none afterTyped, stack⟩

theorem configuration_branch_value_progress
    (typed : ConfigurationTyped signature tickets world ⟨.branch condition yes no, scope, tail⟩ result)
    (isValue : condition.IsValue) :
    ∃ after, RawStep ⟨.branch condition yes no, scope, tail⟩ ⟨after, scope, tail⟩ [] [] ∧
      ConfigurationTyped signature tickets world ⟨after, scope, tail⟩ result := by
  obtain ⟨input, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨after, step, afterTyped⟩ := typed_branch_value_progress expression isValue scope tail
      exact ⟨after, step, input, .checked scopeTyped afterTyped, stack⟩

/-- Fresh entry grows the typing world for every retained payload and dormant
    capture, then installs the cell with a derived non-escaping answer port. -/
theorem configuration_resource_value_progress
    (typed : ConfigurationTyped signature tickets (resourceWorld issued)
      ⟨.resource binder initializer body, scope, tail⟩ result)
    (isValue : initializer.IsValue)
    (ledger : Ledger (RunState.erase ⟨⟨.resource binder initializer body, scope, tail⟩, issued, completed⟩)) :
    ∃ after,
      RunStep ⟨⟨.resource binder initializer body, scope, tail⟩, issued, completed⟩ after ∧
      ConfigurationTyped signature tickets (resourceWorld after.issued) after.configuration result ∧
      Ledger after.erase := by
  obtain ⟨input, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      rename_i ticket allowed
      have integerTyped : Typed signature (resourceWorld issued) TypeEnv.empty ticket allowed initializer .integer := by
        cases expression with | resource initializer _ _ _ _ => exact initializer
      obtain ⟨payload, rfl⟩ := typed_integer_value integerTyped isValue
      obtain ⟨identity, residual, fresh, step, bodyTyped, noEscape, noEffectEscape, effects, afterLedger⟩ :=
        typed_resource_entry_progress binder payload body scope input tail issued completed expression ledger
      have larger : resourceWorld issued ⊆ resourceWorld (issued ++ [.resource identity]) := by
        rw [resource_world_append]
        exact fun _ member => List.mem_append_left _ member
      exact ⟨_, step, ⟨input, .checked scopeTyped bodyTyped,
        .push (.cell ⟨_, scopeTyped⟩ noEscape) (stack_world_weaken stack larger)⟩, afterLedger⟩

end Ash.OneShot.ScopedTyping

namespace Ash.OneShot.ScopedTyping.RetainedExamples
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (Signature TypeEnv TicketSignatures)

abbrev handler := UsageExecutionExamples.handler
abbrev cap := UsageExecutionExamples.cap
abbrev request := UsageExecutionExamples.request

def signature : Signature := fun _ operation => if operation = 0 then some (.unit, .unit) else none

def noTickets : TicketSignatures := fun _ => none
def tickets : TicketSignatures := noTickets.insert 3 .unit .unit

theorem handler_typed : FrameTyped signature registry world (.handler handler) := by
  refine .handler ⟨.none, .none⟩ (.cons rfl (.resume .unit (List.nil_subset _) (List.nil_subset _)) .nil) ?_ (by decide)
  intro operation input output known
  by_cases zero : operation = 0
  · subst operation
    exact List.mem_cons_self
  · simp [signature, zero] at known

theorem cap_typed : StackTyped signature registry world cap .unit .unit :=
  .push handler_typed .nil

theorem request_configuration_typed : ConfigurationTyped signature registry world ⟨request, .none, cap⟩ .unit :=
  ⟨.unit, .checked .none (.perform (allowed := [handler.effectInst]) rfl List.mem_cons_self .unit (List.nil_subset _)), cap_typed⟩

/-- Capture construction is inhabited with an actual retained handler and a
    fresh historical owner; neither operand closure nor clause readiness is supplied. -/
theorem derived_capture_typed :
    ∃ afterTickets after, RawStep ⟨request, .none, cap⟩ after [.ticket 3] [] ∧
      ConfigurationTyped signature afterTickets [] after .unit := by
  obtain ⟨parameter, binder, body, output, step, extension, typed⟩ :=
    capture_constructs_typed_configuration (.hit handler .nil rfl)
      (request_configuration_typed (registry := noTickets) (world := [])) trivial (owner := 3) rfl
  exact ⟨_, _, step, typed⟩

def frontFrame : PlainData := ⟨.bind 2 .unit, .ticket 9 3, .unit, .unit, [], rfl⟩
def front : Stack := .push (.plain frontFrame) .nil

theorem front_typed : StackTyped signature tickets world front .unit .unit :=
  .push (.plain (ticket := .bound 9 .unit .unit [] []) (allowed := []) (.bound rfl) (.bind .unit)) .nil

theorem resume_configuration_typed :
    ConfigurationTyped signature tickets world
      ⟨.resume 9 .unit, .ticket 9 3, front.append (.live 3 .unit .unit cap .none .nil)⟩ .unit :=
  ⟨.unit, .checked (ticket := .bound 9 .unit .unit [] []) (allowed := []) (.bound rfl)
    (.resume .unit (List.nil_subset _) (List.nil_subset _)),
    stack_typed_append front_typed (.live rfl ⟨.none, .none⟩ cap_typed .nil)⟩

theorem nonempty_prefix_resumption_typed :
    RawStep
      ⟨.resume 9 .unit, .ticket 9 3, front.append (.live 3 .unit .unit cap .none .nil)⟩
      ⟨.unit, .ticket 9 3, cap.append (front.append (.spent 3 .unit .none .nil))⟩ [] [.ticket 3] ∧
      ConfigurationTyped signature tickets []
        ⟨.unit, .ticket 9 3, cap.append (front.append (.spent 3 .unit .none .nil))⟩ .unit :=
  ⟨.resume 9 3 (.ticket 9 3) .none .unit .unit front cap .nil .unit ScopedExecution.Examples.unit_closed rfl,
    resume_preserves_configuration_typing rfl resume_configuration_typed⟩

theorem resource_entry_preserves_retained_configuration :
    ∃ after, RunStep
      ⟨⟨.resource 4 (.integer 17) (ScopedExecution.Examples.readBody 4), .none, .nil⟩, [], []⟩ after ∧
      ConfigurationTyped (Typing.withCellSignatures (fun _ _ => none)) noTickets
        (resourceWorld after.issued) after.configuration .integer ∧ Ledger after.erase :=
  configuration_resource_value_progress
    ⟨.integer, .checked .none (TypingExamples.resource_read_typed (allowed := []) [] 4 17), .nil⟩
    trivial ⟨.refl _, by decide⟩

def action : ActionData :=
  ⟨7, .lambda 0 .unit, ⟨trivial, rfl, by intro dependency member; cases member⟩, .none, .integer, []⟩

theorem action_typed : FrameTyped signature noTickets [] (.armed action) :=
  .armed ⟨.none, .none⟩ (.lambda .unit (List.nil_subset _) (List.nil_subset _))

theorem saved_integer_closed : ScopedExpressions.ClosedValue (.integer 17) :=
  ⟨trivial, rfl, by intro dependency member; cases member⟩

theorem callback_application_and_saved_result_typed :
    RawStep ⟨.integer 17, .none, .push (.armed action) .nil⟩
      ⟨.app action.action .unit, .none, .push (.running action (.integer 17) saved_integer_closed) .nil⟩ [] [] ∧
      ConfigurationTyped signature noTickets []
        ⟨.app action.action .unit, .none, .push (.running action (.integer 17) saved_integer_closed) .nil⟩ .integer := by
  have step := RawStep.startCleanup action (.integer 17) saved_integer_closed .none .nil
  exact ⟨step, raw_value_step_typed step trivial ⟨.integer, .checked .none (.integer (allowed := [])), .push action_typed .nil⟩⟩

theorem callback_completion_restores_integer :
    RawStep ⟨.unit, .none, .push (.running action (.integer 17) saved_integer_closed) .nil⟩
      ⟨.integer 17, .none, .nil⟩ [] [.cleanup 7] ∧
      ConfigurationTyped signature noTickets [] ⟨.integer 17, .none, .nil⟩ .integer := by
  have running : FrameTyped signature noTickets [] (.running action (.integer 17) saved_integer_closed) :=
    .running ⟨.none, .none⟩ (.lambda .unit (List.nil_subset _) (List.nil_subset _)) .integer
  have step := RawStep.finishCleanup action (.integer 17) saved_integer_closed .none .nil
  exact ⟨step, raw_value_step_typed step trivial ⟨.unit, .checked .none (.unit (allowed := [])), .push running .nil⟩⟩

end Ash.OneShot.ScopedTyping.RetainedExamples

#print axioms Ash.OneShot.ScopedTyping.stack_typing_gives_ports
#print axioms Ash.OneShot.ScopedTyping.handler_cut_retains_typing
#print axioms Ash.OneShot.ScopedTyping.resume_retains_stack_typing
#print axioms Ash.OneShot.ScopedTyping.raw_value_step_typed
#print axioms Ash.OneShot.ScopedTyping.resume_preserves_configuration_typing
#print axioms Ash.OneShot.ScopedTyping.capture_constructs_typed_configuration
#print axioms Ash.OneShot.ScopedTyping.make_plan_retains_types
#print axioms Ash.OneShot.ScopedTyping.discard_preserves_configuration_typing
#print axioms Ash.OneShot.ScopedTyping.configuration_world_weaken
#print axioms Ash.OneShot.ScopedTyping.typed_cell_return_excludes_identity
#print axioms Ash.OneShot.ScopedTyping.configuration_focus_progress
#print axioms Ash.OneShot.ScopedTyping.configuration_bind_value_progress
#print axioms Ash.OneShot.ScopedTyping.configuration_application_value_progress
#print axioms Ash.OneShot.ScopedTyping.configuration_branch_value_progress
#print axioms Ash.OneShot.ScopedTyping.configuration_resource_value_progress
#print axioms Ash.OneShot.ScopedTyping.RetainedExamples.derived_capture_typed
#print axioms Ash.OneShot.ScopedTyping.RetainedExamples.nonempty_prefix_resumption_typed
#print axioms Ash.OneShot.ScopedTyping.RetainedExamples.resource_entry_preserves_retained_configuration
#print axioms Ash.OneShot.ScopedTyping.RetainedExamples.callback_application_and_saved_result_typed
#print axioms Ash.OneShot.ScopedTyping.RetainedExamples.callback_completion_restores_integer

namespace Ash.OneShot.ScopedTyping.RetainedExamples
open Syntax Instantiation ScopedExpressions ScopedExecution

/-- Value-type composition alone does not supply an interpretation for a row. -/
theorem unhandled_request_is_value_typed :
    ConfigurationTyped signature noTickets [] ⟨request, .none, .nil⟩ .unit :=
  ⟨.unit, .checked .none (.perform (allowed := [handler.effectInst]) rfl List.mem_cons_self .unit (List.nil_subset _)), .nil⟩

theorem perform_value_has_no_focus
    (focus : ScopedExecution.Focus (.perform effect operation operand) child context) (isValue : operand.IsValue) : False := by
  cases focus with
  | perform notValue => exact notValue isValue

theorem unhandled_request_has_no_step :
    ¬ RawStep ⟨request, scope, .nil⟩ after created discharged := by
  intro step
  generalize beforeEq : (⟨request, scope, .nil⟩ : Configuration) = before at step
  have expressionEq := (congrArg Configuration.expression beforeEq).symm
  have empty := (congrArg Configuration.stack beforeEq).symm
  clear beforeEq
  cases step
  all_goals simp_all [request, UsageExecutionExamples.request, UsageExecutionExamples.handler,
    freezeEffect, Code.IsValue, ScopedExpressions.ClosedValue]
  all_goals first
    | exact perform_value_has_no_focus (effect := .user 1 []) (operation := 0) (operand := .unit) (by assumption) trivial
    | cases ‹HandlerCut _ .nil _ _ _›

def callbackInitial : RunState := ⟨⟨.integer 17, .none, .push (.armed action) .nil⟩, [.cleanup 7], []⟩
def callbackTerminal : RunState := ⟨⟨.integer 17, .none, .nil⟩, [.cleanup 7], [.cleanup 7]⟩

theorem callback_trace : RawTrace callbackInitial.configuration callbackTerminal.configuration [] [.cleanup 7] := by
  have start := RawStep.startCleanup action (.integer 17) saved_integer_closed .none .nil
  have invoke := RawStep.beta 0 .unit .unit .none (.push (.running action (.integer 17) saved_integer_closed) .nil)
    ScopedExecution.Examples.unit_closed action.closed
  have finish := RawStep.finishCleanup action (.integer 17) saved_integer_closed .none .nil
  exact .next start (.next invoke (.next finish (.refl _)))

theorem callback_execution_and_ledger :
    RunSteps callbackInitial callbackTerminal ∧ Ledger callbackTerminal.erase := by
  have steps : RunSteps callbackInitial callbackTerminal := raw_trace_enacts callback_trace (issued := [.cleanup 7]) (completed := []) (by decide)
  exact ⟨steps, run_steps_preserve_ledger steps ⟨.refl _, by decide⟩⟩

/-- All four configurations on that actual trace have typed code and stack. -/
theorem callback_trace_configurations_typed :
    ConfigurationTyped signature noTickets [] callbackInitial.configuration .integer ∧
    ConfigurationTyped signature noTickets []
      ⟨.app action.action .unit, .none, .push (.running action (.integer 17) saved_integer_closed) .nil⟩ .integer ∧
    ConfigurationTyped signature noTickets []
      ⟨.unit, .none, .push (.running action (.integer 17) saved_integer_closed) .nil⟩ .integer ∧
    ConfigurationTyped signature noTickets [] callbackTerminal.configuration .integer := by
  have running : FrameTyped signature noTickets [] (.running action (.integer 17) saved_integer_closed) :=
    .running ⟨.none, .none⟩ (.lambda .unit (List.nil_subset _) (List.nil_subset _)) .integer
  exact ⟨⟨.integer, .checked .none (.integer (allowed := [])), .push action_typed .nil⟩,
    callback_application_and_saved_result_typed.2,
    ⟨.unit, .checked .none (.unit (allowed := [])), .push running .nil⟩,
    callback_completion_restores_integer.2⟩

end Ash.OneShot.ScopedTyping.RetainedExamples

#print axioms Ash.OneShot.ScopedTyping.RetainedExamples.unhandled_request_is_value_typed
#print axioms Ash.OneShot.ScopedTyping.RetainedExamples.unhandled_request_has_no_step
#print axioms Ash.OneShot.ScopedTyping.RetainedExamples.callback_execution_and_ledger
#print axioms Ash.OneShot.ScopedTyping.RetainedExamples.callback_trace_configurations_typed
