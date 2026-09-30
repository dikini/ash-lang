import ScopedPortReadiness

/-!
Declared port typing for actual runtime frames, historical ticket records and
saved captures. The machine's existing Ty metadata is read through eraseType;
new inferred annotations are supplied through embedPort. Stored resource access
is independent. This does not migrate connected effect or joint readiness yet.
-/

namespace Ash.OneShot.ScopedPorts
open Instantiation ScopedExpressions ScopedExecution
open ScopedTyping (World clauseKeys focus_is_not_value handler_cut_instance clause_at_of_key)

abbrev TicketSignatures := Nat → Option (Port × Port)

inductive ScopeTyped (tickets : TicketSignatures) : Scope → Ticket → Prop where
  | none : ScopeTyped tickets .none .none
  | bound (known : tickets owner = some (input, answer)) :
      ScopeTyped tickets (.ticket binder owner) (.bound binder input answer residual closing)

def ScopeKnown (tickets : TicketSignatures) (scope : Scope) : Prop :=
  ∃ ticket, ScopeTyped tickets scope ticket

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

def TicketSignatures.insert (tickets : TicketSignatures) (owner : Nat) (input answer : Port) : TicketSignatures :=
  fun name => if name = owner then some (input, answer) else tickets name

theorem fresh_ticket_signature_extension (fresh : tickets owner = none) :
    TicketExtension tickets (tickets.insert owner input answer) := by
  intro name oldInput oldAnswer known
  by_cases same : name = owner
  · subst name
    simp [fresh] at known
  · simp [TicketSignatures.insert, same, known]

theorem scope_typed_names_match (typed : ScopeTyped tickets scope ticket) : ScopeNamesMatch ticket scope := by
  cases typed with
  | none => exact .none
  | bound => exact .bound

/-- Immediate effect bounds are retained existentially. This judgment alone
    makes no claim that surrounding interpretations provide those effects. -/
inductive AtType (signature : Signature) (tickets : TicketSignatures) (world : World) : Scope → Code → Port → Prop where
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

/-- Every actual payload is checked. Declared cell result ports exclude the
    local identity; running cleanup also retains a typed saved result.
    Stored resource support is an independent obligation. -/
inductive FrameTyped (signature : Signature) (tickets : TicketSignatures) (world : World) : ExecFrame → Prop where
  | plain (scope : ScopeTyped tickets data.scope ticket)
      (context : ContextTyped signature world TypeEnv.empty ticket allowed data.context (eraseType data.input) (eraseType data.output)) :
      FrameTyped signature tickets world (.plain data)
  | handler (scope : ScopeKnown tickets handler.scope)
      (clauses : ClausesTyped signature world TypeEnv.empty handler.effectInst (eraseType handler.answer) residual handler.clauses)
      (coverage : Covers signature handler.effectInst handler.clauses)
      (unique : (clauseKeys handler.clauses).Nodup) : FrameTyped signature tickets world (.handler handler)
  | cell (scope : ScopeKnown tickets runtimeScope) (noEscape : identity ∉ (eraseType answer).resources) :
      FrameTyped signature tickets world (.cell identity payload runtimeScope answer)
  | armed (scope : ScopeKnown tickets action.scope)
      (callable : Typed signature world TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests)) : FrameTyped signature tickets world (.armed action)
  | running (scope : ScopeKnown tickets action.scope)
      (callable : Typed signature world TypeEnv.empty .none [] action.action
        (.function .unit .unit action.requests))
      (result : Typed signature world TypeEnv.empty .none [] saved (eraseType action.answer)) :
      FrameTyped signature tickets world (.running action saved closed)
  | closing (scope : ScopeKnown tickets runtimeScope) : FrameTyped signature tickets world (.closing identity runtimeScope)
  | retiring (known : tickets owner = some (input, answer)) : FrameTyped signature tickets world (.retiring owner)

/-- Port composition now requires typing the stored code and all dormant
    captures, in addition to agreeing on annotated input/answer types. -/
inductive StackTyped (signature : Signature) (tickets : TicketSignatures) (world : World) : Stack → Port → Port → Prop where
  | nil : StackTyped signature tickets world .nil type type
  | push (frame : FrameTyped signature tickets world entry)
      (rest : StackTyped signature tickets world tail (eraseType entry.erase.output) result) :
      StackTyped signature tickets world (.push entry tail) (eraseType entry.erase.input) result
  | live (known : tickets owner = some (eraseType input, eraseType answer)) (scope : ScopeKnown tickets callerScope)
      (saved : StackTyped signature tickets world capture (eraseType input) (eraseType answer))
      (rest : StackTyped signature tickets world tail (eraseType answer) result) :
      StackTyped signature tickets world (.live owner input answer capture callerScope tail) (eraseType answer) result
  | spent (known : tickets owner = some (input, eraseType answer)) (scope : ScopeKnown tickets callerScope)
      (rest : StackTyped signature tickets world tail (eraseType answer) result) :
      StackTyped signature tickets world (.spent owner answer callerScope tail) (eraseType answer) result

def ConfigurationTyped (signature : Signature) (tickets : TicketSignatures) (world : World)
    (configuration : Configuration) (result : Port) : Prop :=
  ∃ input, AtType signature tickets world configuration.scope configuration.expression input ∧
    StackTyped signature tickets world configuration.stack input result

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
    StackTyped signature tickets world cap input (eraseType handler.answer) ∧
      StackTyped signature tickets world tail (eraseType handler.answer) result ∧
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
      (front.append (.live owner input answer cap callerScope tail)) (eraseType answer) result) :
    StackTyped signature tickets world
      (cap.append (front.append (.spent owner answer callerScope tail))) (eraseType input) result := by
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
      (.function .unit .unit action.requests)) (rest : PlanContentsTyped signature tickets world tail) :
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
  | release rest ih => exact .push (.cell scope (by simp [eraseType, Port.resources])) ih
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
    ∃ (parameter binder : Nat) (body : Code) (output : Port),
      let extended := tickets.insert owner output (eraseType handler.answer)
      RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer cap handler.scope tail⟩ [.ticket owner] [] ∧
      TicketExtension tickets extended ∧
      ConfigurationTyped signature extended world
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner (embedPort output) handler.answer cap handler.scope tail⟩ result := by
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
          have extension := fresh_ticket_signature_extension (input := output) (answer := eraseType handler.answer) fresh
          have newTicket : (tickets.insert owner output (eraseType handler.answer)) owner = some (output, eraseType handler.answer) := by
            simp [TicketSignatures.insert]
          exact ⟨parameter, binder, body, output,
            .capture requested operation parameter binder owner operand body scope whole cap tail handler (embedPort output) cut selected closed ready,
            extension, eraseType handler.answer,
            .checked (.bound newTicket) (selected_clause_substitution_typed selected clauses known operandTyped closed),
            .live (by simpa using newTicket) (scope_known_extension caller extension)
              (by simpa using stack_typed_extension saved extension) (stack_typed_extension outside extension)⟩



/-- One actual capture event preserves declared ports, the ownership ledger,
    and independently checked live support. These are three facets, not the
    complete joined effect/usage/name invariant. -/
theorem capture_constructs_ports_ledger_support
    (cut : HandlerCut requested whole cap tail handler)
    (typed : ConfigurationTyped signature tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result)
    (isValue : operand.IsValue) (freshTicket : tickets owner = none)
    (freshOwners : (issued ++ [.ticket owner]).Nodup)
    (ledger : Ledger (RunState.erase ⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩))
    (support : AccessValid ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ ambient)
    (checks : AccessChecks ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ ambient) :
    ∃ (parameter binder : Nat) (body : Code) (output : Port),
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer cap handler.scope tail⟩
      let extended := tickets.insert owner output (eraseType handler.answer)
      RunStep ⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩
        ⟨after, issued ++ [.ticket owner], completed⟩ ∧
      TicketExtension tickets extended ∧
      ConfigurationTyped signature extended world after result ∧
      Ledger (RunState.erase ⟨after, issued ++ [.ticket owner], completed⟩) ∧ AccessValid after ambient := by
  obtain ⟨parameter, binder, body, output, raw, extension, afterTyped⟩ :=
    capture_constructs_typed_configuration cut typed isValue freshTicket
  have step := RunStep.event
    ⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩
    _ [.ticket owner] [] raw freshOwners
  exact ⟨parameter, binder, body, output, step, extension, afterTyped,
    run_step_preserves_ledger step ledger, raw_step_preserves_access raw support checks⟩

theorem resume_operand_closed
    (typed : ConfigurationTyped signature tickets world ⟨.resume binder value, scope, stack⟩ result)
    (isValue : value.IsValue) : ClosedValue value := by
  obtain ⟨input, expression, control⟩ := typed
  cases expression with
  | checked scope expression => cases expression with
      | resume operand effects formed => exact typed_value_closed operand isValue

theorem resume_access_checks : AccessChecks ⟨.resume binder value, scope, stack⟩ ambient := by
  constructor
  · intro identity payload answer savedScope current result tail same closed
    cases same
    exact False.elim closed.1
  · intro requested operation operand current whole cap tail handler same cut closed
    cases same
  · intro other owner current caller input answer front cap tail plan same resolved built
    cases same

/-- Full clause-prefix resumption preserves the same three independent facets.
    Actual support checks at this resume are derived from its expression form. -/
theorem resume_preserves_ports_ledger_support {front cap tail : Stack}
    (typed : ConfigurationTyped signature tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩ result)
    (isValue : value.IsValue) (resolved : scope.resolve binder = some owner)
    (ledger : Ledger (RunState.erase
      ⟨⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩, issued, completed⟩))
    (support : AccessValid ⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩ ambient) :
    let after : Configuration := ⟨value, scope, cap.append (front.append (.spent owner answer caller tail))⟩
    RunStep ⟨⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩, issued, completed⟩
      ⟨after, issued, .ticket owner :: completed⟩ ∧
    ConfigurationTyped signature tickets world after result ∧
    Ledger (RunState.erase ⟨after, issued, .ticket owner :: completed⟩) ∧ AccessValid after ambient := by
  have raw := RawStep.resume binder owner scope caller input answer front cap tail value
    (resume_operand_closed typed isValue) resolved
  have step := RunStep.event
    ⟨⟨.resume binder value, scope, front.append (.live owner input answer cap caller tail)⟩, issued, completed⟩
    _ [] [.ticket owner] raw (by simpa [RunState.erase] using ledger.2)
  refine ⟨by simpa using step, resume_preserves_configuration_typing resolved typed, ?_,
    raw_step_preserves_access raw support resume_access_checks⟩
  simpa using run_step_preserves_ledger step ledger

def eraseTickets (tickets : Typing.TicketSignatures) : TicketSignatures :=
  fun owner => (tickets owner).map (fun ports => (eraseType ports.1, eraseType ports.2))

theorem erase_ticket_lookup (known : tickets owner = some (input, answer)) :
    eraseTickets tickets owner = some (eraseType input, eraseType answer) := by
  simp [eraseTickets, known]

theorem scope_erasure (typed : Typing.ScopeTyped tickets scope ticket) :
    ScopeTyped (eraseTickets tickets) scope (eraseTicket ticket) := by
  cases typed with
  | none => exact .none
  | bound known => exact .bound (by simp [eraseTickets, known])

theorem scope_known_erasure (known : Typing.ScopeKnown tickets scope) : ScopeKnown (eraseTickets tickets) scope := by
  obtain ⟨ticket, typed⟩ := known
  exact ⟨eraseTicket ticket, scope_erasure typed⟩

theorem clauses_erasure
    (typed : ScopedTyping.ClausesTyped signature world environment effect answer residual clauses) :
    ClausesTyped (eraseSignature signature) world (eraseEnvironment environment) effect (eraseType answer) residual clauses := by
  cases clauses with
  | nil => exact .nil
  | cons operation parameter binder body rest => cases typed with
      | cons known body rest =>
          exact .cons (erase_lookup known) (by simpa [eraseTicket] using typed_erasure body) (clauses_erasure rest)
termination_by sizeOf clauses

theorem context_erasure
    (typed : ScopedTyping.ContextTyped signature world environment ticket allowed context input output) :
    ContextTyped (eraseSignature signature) world (eraseEnvironment environment) (eraseTicket ticket) allowed
      context (eraseType input) (eraseType output) := by
  cases typed with
  | pairLeft right => exact .pairLeft (typed_erasure right)
  | pairRight left => exact .pairRight (typed_erasure left)
  | appFunction argument effects => exact .appFunction (typed_erasure argument) effects
  | appArgument function effects => exact .appArgument (typed_erasure function) effects
  | bind suffix => exact .bind (by simpa using typed_erasure suffix)
  | branch yes no => exact .branch (typed_erasure yes) (typed_erasure no)
  | perform known available formed => exact .perform (erase_lookup known) available (erase_world formed)
  | resume effects formed => exact .resume effects (erase_world formed)
  | resource body formed rowBound effects =>
      exact .resource (fun identity fresh => typed_erasure (body identity fresh)) (erase_world formed) rowBound effects
  | cleanup body effects => exact .cleanup (typed_erasure body) effects

theorem frame_erasure (typed : ScopedTyping.FrameTyped signature tickets world frame) :
    FrameTyped (eraseSignature signature) (eraseTickets tickets) world frame := by
  cases typed with
  | plain scope context => exact .plain (scope_erasure scope) (context_erasure context)
  | handler scope clauses coverage unique =>
      exact .handler (scope_known_erasure scope) (clauses_erasure clauses) (erase_coverage coverage) unique
  | cell scope excluded =>
      exact .cell (scope_known_erasure scope) (fun member => excluded (erasure_preserves_declared_resources _ member))
  | armed scope callable => exact .armed (scope_known_erasure scope) (typed_erasure callable)
  | running scope callable value => exact .running (scope_known_erasure scope) (typed_erasure callable) (typed_erasure value)
  | closing scope => exact .closing (scope_known_erasure scope)
  | retiring known => exact .retiring (erase_ticket_lookup known)

/-- Earlier retained-code typing embeds into the replacement judgment on the
    very same machine forest. Erased equality does not imply old Ty equality. -/
theorem stack_erasure (typed : ScopedTyping.StackTyped signature tickets world stack input result) :
    StackTyped (eraseSignature signature) (eraseTickets tickets) world stack (eraseType input) (eraseType result) := by
  induction typed with
  | nil => exact .nil
  | push frame rest ih => exact .push (frame_erasure frame) ih
  | live known scope saved rest ihSaved ihRest =>
      exact .live (by simp [eraseTickets, known]) (scope_known_erasure scope) ihSaved ihRest
  | spent known scope rest ih => exact .spent (erase_ticket_lookup known) (scope_known_erasure scope) ih

theorem configuration_erasure
    (typed : ScopedTyping.ConfigurationTyped signature tickets world configuration result) :
    ConfigurationTyped (eraseSignature signature) (eraseTickets tickets) world configuration (eraseType result) := by
  obtain ⟨input, expression, stack⟩ := typed
  cases expression with
  | checked scope expression =>
      exact ⟨eraseType input, .checked (scope_erasure scope) (typed_erasure expression), stack_erasure stack⟩

namespace RetainedExamples
open ScopedSignatureGap.Examples
open Ash.OneShot.ScopedPorts.Examples (signature callbackPort payload_typed clauses_typed coverage)

def records : TicketSignatures := TicketSignatures.insert (fun _ => none) 7 .unit .unit
def beforeRequest : Configuration :=
  ⟨.perform (freezeEffect send) 0 (payload (.activation 0)), .none, .push (.handler handler) outside⟩
def afterCapture : Configuration :=
  ⟨.resume 9 .unit, .ticket 9 7, .live 7 .unit .unit capture .none outside⟩
def afterResume : Configuration :=
  ⟨.unit, .ticket 9 7, capture.append (.spent 7 .unit .none outside)⟩

theorem outside_typed : StackTyped signature tickets [0] outside .unit .unit :=
  .push (.cell ⟨_, .none⟩ (by simp [eraseType, Port.resources])) .nil

theorem handler_typed : FrameTyped signature tickets [0] (.handler handler) :=
  .handler ⟨_, .none⟩ (clauses_typed (residual := [])) coverage (by decide)

theorem request_typed : ConfigurationTyped signature (fun _ => none) [0] beforeRequest .unit :=
  ⟨.unit, .checked .none (.perform (allowed := [send]) (by simp [Ash.OneShot.ScopedPorts.Examples.signature]) (by simp)
    (payload_typed (by simp)) (List.nil_subset _)), .push handler_typed outside_typed⟩

theorem source_entries_typed :
    ConfigurationTyped signature (fun _ => none) [] ⟨program, .none, .nil⟩ .unit ∧
    ConfigurationTyped signature (fun _ => none) [0] ⟨openedBody 0, .none, outside⟩ .unit :=
  ⟨⟨.unit, .checked .none Ash.OneShot.ScopedPorts.Examples.generative_source_port_typed, .nil⟩,
    ⟨.unit, .checked .none (Ash.OneShot.ScopedPorts.Examples.opened_body_typed
      (allowed := []) (by simp)), outside_typed⟩⟩

theorem captured_typed : ConfigurationTyped signature records [0] afterCapture .unit :=
  ⟨.unit, .checked (.bound rfl) (.resume (allowed := []) (closing := []) .unit (List.nil_subset _) (List.nil_subset _)),
    .live rfl ⟨_, .none⟩ (.push handler_typed .nil) outside_typed⟩

theorem resumed_typed : ConfigurationTyped signature records [0] afterResume .unit := by
  exact resume_preserves_configuration_typing (front := .nil) rfl captured_typed

/-- Actual completion steps preserve the new port judgment. Resource/ticket
    ledger conservation is still the independent raw-machine theorem. -/
theorem completion_states_typed :
    ConfigurationTyped signature records [0] ⟨.unit, .none, .spent 7 .unit .none outside⟩ .unit ∧
    ConfigurationTyped signature records [0] ⟨.unit, .none, outside⟩ .unit ∧
    ConfigurationTyped signature records [0] ⟨.unit, .none, .nil⟩ .unit := by
  have unitClosed : ClosedValue Code.unit := typed_value_closed (Typed.unit (signature := signature)
    (world := [0]) (environment := TypeEnv.empty) (ticket := .none) (allowed := [])) trivial
  have first := raw_value_step_preserves_typing
    (RawStep.leaveHandler handler .unit unitClosed (.ticket 9 7) (.spent 7 .unit .none outside))
    unitClosed resumed_typed
  have second := raw_value_step_preserves_typing
    (RawStep.leaveClause 7 .unit .unit unitClosed .none .none outside) unitClosed first
  have last := raw_value_step_preserves_typing
    (RawStep.leaveCell 0 41 .unit .none .none .unit unitClosed .nil) unitClosed second
  exact ⟨first, second, last⟩

def escapingReturn : Configuration :=
  ⟨payload (.activation 0), .none, .push (.cell 0 41 .none (embedPort callbackPort)) .nil⟩

/-- Declared result ports alone cannot establish stored-resource exclusion. -/
theorem escaping_return_has_ports : ConfigurationTyped signature (fun _ => none) [0] escapingReturn callbackPort :=
  ⟨callbackPort, .checked .none (payload_typed (allowed := []) (by simp)),
    .push (.cell ⟨_, .none⟩ (by simp [callbackPort, eraseType, embedPort, Port.resources])) .nil⟩

theorem escaping_return_access_rejected : ¬ AccessChecks escapingReturn [] := by
  intro checked
  have excluded := checked.release 0 41 (embedPort callbackPort) .none .none
    (payload (.activation 0)) .nil rfl payload_closed
  exact excluded (opened_payload_retains 0)

end RetainedExamples
end Ash.OneShot.ScopedPorts

#print axioms Ash.OneShot.ScopedPorts.scope_typed_extension
#print axioms Ash.OneShot.ScopedPorts.fresh_ticket_signature_extension
#print axioms Ash.OneShot.ScopedPorts.scope_typed_names_match
#print axioms Ash.OneShot.ScopedPorts.at_type_value_transport
#print axioms Ash.OneShot.ScopedPorts.stack_typed_append
#print axioms Ash.OneShot.ScopedPorts.stack_typed_decompose
#print axioms Ash.OneShot.ScopedPorts.handler_cut_retains_typing
#print axioms Ash.OneShot.ScopedPorts.resume_retains_stack_typing
#print axioms Ash.OneShot.ScopedPorts.raw_value_step_preserves_typing
#print axioms Ash.OneShot.ScopedPorts.resume_preserves_configuration_typing
#print axioms Ash.OneShot.ScopedPorts.stack_typed_extension
#print axioms Ash.OneShot.ScopedPorts.plan_contents_append
#print axioms Ash.OneShot.ScopedPorts.make_plan_retains_types
#print axioms Ash.OneShot.ScopedPorts.close_control_retains_types
#print axioms Ash.OneShot.ScopedPorts.discard_preserves_configuration_typing
#print axioms Ash.OneShot.ScopedPorts.clauses_world_weaken
#print axioms Ash.OneShot.ScopedPorts.context_world_weaken
#print axioms Ash.OneShot.ScopedPorts.stack_world_weaken
#print axioms Ash.OneShot.ScopedPorts.configuration_world_weaken
#print axioms Ash.OneShot.ScopedPorts.raw_value_step_typed
#print axioms Ash.OneShot.ScopedPorts.typed_perform_inversion
#print axioms Ash.OneShot.ScopedPorts.capture_constructs_typed_configuration
#print axioms Ash.OneShot.ScopedPorts.capture_constructs_ports_ledger_support
#print axioms Ash.OneShot.ScopedPorts.resume_operand_closed
#print axioms Ash.OneShot.ScopedPorts.resume_access_checks
#print axioms Ash.OneShot.ScopedPorts.resume_preserves_ports_ledger_support
#print axioms Ash.OneShot.ScopedPorts.scope_erasure
#print axioms Ash.OneShot.ScopedPorts.clauses_erasure
#print axioms Ash.OneShot.ScopedPorts.context_erasure
#print axioms Ash.OneShot.ScopedPorts.frame_erasure
#print axioms Ash.OneShot.ScopedPorts.stack_erasure
#print axioms Ash.OneShot.ScopedPorts.configuration_erasure
#print axioms Ash.OneShot.ScopedPorts.RetainedExamples.request_typed
#print axioms Ash.OneShot.ScopedPorts.RetainedExamples.source_entries_typed
#print axioms Ash.OneShot.ScopedPorts.RetainedExamples.captured_typed
#print axioms Ash.OneShot.ScopedPorts.RetainedExamples.resumed_typed
#print axioms Ash.OneShot.ScopedPorts.RetainedExamples.completion_states_typed
#print axioms Ash.OneShot.ScopedPorts.RetainedExamples.escaping_return_has_ports
#print axioms Ash.OneShot.ScopedPorts.RetainedExamples.escaping_return_access_rejected
