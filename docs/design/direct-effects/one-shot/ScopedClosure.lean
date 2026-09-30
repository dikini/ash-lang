import ScopedExecution

/-!
Resource-name closure through scoped one-shot execution. This invariant keeps
free source resource names out of executing code while allowing deferred local
acquisition templates. It is independent of ordinary typing and live support.
-/

namespace Ash.OneShot.ScopedExecution
open Instantiation ScopedExpressions

def Context.ResourceClosed (context : Context) : Prop := (context.plug .unit).ResourceClosed

theorem context_closed_iff (context : Context) (code : Code) :
    (context.plug code).ResourceClosed ↔ code.ResourceClosed ∧ context.ResourceClosed := by
  cases context <;> simp [Context.ResourceClosed, Code.ResourceClosed, Context.plug, Code.freeNames,
    List.append_eq_nil_iff, and_comm]

def ExecFrame.ResourceClosed : ExecFrame → Prop
  | .plain data => data.context.ResourceClosed
  | .handler data => data.clauses.freeNames = []
  | .cell _ _ _ _ | .armed _ | .running _ _ _ | .unwinding _ | .closing _ _ | .retiring _ => True

def Stack.ResourceClosed : Stack → Prop
  | .nil => True
  | .push frame rest => frame.ResourceClosed ∧ rest.ResourceClosed
  | .live _ _ _ saved _ rest => saved.ResourceClosed ∧ rest.ResourceClosed
  | .spent _ _ _ rest => rest.ResourceClosed

def Configuration.ResourceClosed (configuration : Configuration) : Prop :=
  configuration.expression.ResourceClosed ∧ configuration.stack.ResourceClosed

theorem stack_append_closed (front tail : Stack) :
    (front.append tail).ResourceClosed ↔ front.ResourceClosed ∧ tail.ResourceClosed := by
  induction front <;> simp_all [Stack.append, Stack.ResourceClosed, and_assoc]

theorem closed_cut (cut : HandlerCut requested whole cap tail handler) (closed : whole.ResourceClosed) :
    cap.ResourceClosed ∧ tail.ResourceClosed ∧ handler.clauses.freeNames = [] := by
  induction cut with
  | hit handler tail same => exact ⟨⟨closed.1, trivial⟩, closed.2, closed.1⟩
  | push frame rest cap tail handler miss next ih =>
      obtain ⟨capClosed, tailClosed, handlerClosed⟩ := ih closed.2
      exact ⟨⟨closed.1, capClosed⟩, tailClosed, handlerClosed⟩
  | live ticket q a saved scope rest cap tail handler next ih =>
      obtain ⟨capClosed, tailClosed, handlerClosed⟩ := ih closed.2
      exact ⟨⟨closed.1, capClosed⟩, tailClosed, handlerClosed⟩
  | spent ticket a scope rest cap tail handler next ih => exact ih closed

theorem clause_body_closed (clause : ClauseAt operation clauses parameter binder body)
    (closed : clauses.freeNames = []) : body.ResourceClosed := by
  induction clause with
  | hit => exact (List.append_eq_nil_iff.mp closed).1
  | pass different next ih => exact ih (List.append_eq_nil_iff.mp closed).2

theorem close_control_resource_closed (scope : Scope) (plan : List CloseEntry) :
    (closeControl scope plan).ResourceClosed := by
  induction plan with
  | nil => trivial
  | cons item rest ih => cases item <;> exact ⟨trivial, ih⟩

theorem cell_update_resource_closed (update : CellUpdate identity old new before after)
    (closed : before.ResourceClosed) : after.ResourceClosed := by
  induction update with
  | hit => exact closed
  | push miss next ih => exact ⟨closed.1, ih closed.2⟩
  | live next ih => exact ⟨closed.1, ih closed.2⟩
  | spent next ih => exact ih closed

/-- Closure of instantiation needs the binding; freshness is an independent
    ownership premise supplied by RunStep, not needed for this syntactic fact. -/
theorem binding_closes_body (binder identity : Nat) (initializer body : Code)
    (ready : (Code.resource binder initializer body).ResourceClosed) :
    (body.instantiate (Environment.empty.bind binder identity)).ResourceClosed := by
  apply (body.instantiation_closes_iff _).mpr
  intro name member
  by_cases same : name = binder
  · exact ⟨identity, by simp [Environment.bind, same]⟩
  · have present : name ∈ (Code.resource binder initializer body).freeNames := by
      simp only [Code.freeNames, List.mem_append, List.mem_filter]
      exact Or.inr ⟨member, by simp [same]⟩
    rw [ready] at present
    cases present

/-- Every raw transition preserves resource-name closure of executing code
    and all retained contexts and captures. Callback values carry their own
    closure evidence in ActionData; this does not prove live resource support. -/
theorem raw_step_preserves_resource_closure (step : RawStep before after created discharged)
    (closed : before.ResourceClosed) : after.ResourceClosed := by
  cases step with
  | focus plain focus tail =>
      have parts := (context_closed_iff plain.context _).mp
        (show (plain.context.plug _).ResourceClosed from (focus_reconstructs focus).symm ▸ closed.1)
      exact ⟨parts.1, parts.2, closed.2⟩
  | plug plain value valueClosed scope tail =>
      exact ⟨(context_closed_iff plain.context value).mpr ⟨valueClosed.2.1, closed.2.1⟩, closed.2.2⟩
  | bind parameter value suffix scope tail valueClosed environmentReady =>
      exact ⟨suffix.subst_resource_closed value parameter (List.append_eq_nil_iff.mp closed.1).2 valueClosed.2.1, closed.2⟩
  | beta parameter body value scope tail valueClosed closureReady =>
      exact ⟨body.subst_resource_closed value parameter closureReady.2.1 valueClosed.2.1, closed.2⟩
  | ifTrue yes no scope tail =>
      exact ⟨(List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp closed.1).1).2, closed.2⟩
  | ifFalse yes no scope tail => exact ⟨(List.append_eq_nil_iff.mp closed.1).2, closed.2⟩
  | enterHandler handler body tail =>
      obtain ⟨first, clausesClosed⟩ := List.append_eq_nil_iff.mp closed.1
      exact ⟨(List.append_eq_nil_iff.mp first).2, clausesClosed, closed.2⟩
  | leaveHandler handler value valueClosed scope tail => exact ⟨valueClosed.2.1, closed.2.2⟩
  | enterCell binder identity payload body scope answer tail instantiationReady =>
      exact ⟨binding_closes_body binder identity _ body instantiationReady, trivial, closed.2⟩
  | leaveCell identity payload answer savedScope scope value valueClosed tail => exact ⟨valueClosed.2.1, closed.2.2⟩
  | enterCleanup action body tail =>
      exact ⟨(List.append_eq_nil_iff.mp closed.1).2, trivial, closed.2⟩
  | startCleanup action saved savedClosed scope tail =>
      exact ⟨by simpa only [Code.ResourceClosed, Code.freeNames, List.append_nil] using action.closed.2.1,
        trivial, closed.2.2⟩
  | finishCleanup action saved savedClosed scope tail => exact ⟨savedClosed.2.1, closed.2.2⟩
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler
      operationResult selection clause operandClosed environmentReady =>
      obtain ⟨capClosed, tailClosed, handlerClosed⟩ := closed_cut selection closed.2
      exact ⟨body.subst_resource_closed operand parameter (clause_body_closed clause handlerClosed) operandClosed.2.1,
        capClosed, tailClosed⟩
  | resume binder ticket scope callerScope q a front cap tail value valueClosed resolve =>
      obtain ⟨frontClosed, capClosed, tailClosed⟩ := (stack_append_closed front _).mp closed.2
      exact ⟨valueClosed.2.1, (stack_append_closed cap _).mpr
        ⟨capClosed, (stack_append_closed front _).mpr ⟨frontClosed, tailClosed⟩⟩⟩
  | discard binder ticket closeId scope callerScope q a front cap tail plan resolve build =>
      obtain ⟨frontClosed, _, tailClosed⟩ := (stack_append_closed front _).mp closed.2
      exact ⟨rfl, (stack_append_closed _ _).mpr ⟨close_control_resource_closed scope plan,
        trivial, (stack_append_closed front _).mpr ⟨frontClosed, tailClosed⟩⟩⟩
  | leaveClause ticket answer value valueClosed scope callerScope tail => exact ⟨valueClosed.2.1, closed.2⟩
  | finishClose identity scope callerScope tail => exact ⟨rfl, closed.2.2⟩
  | retire ticket scope tail => exact ⟨rfl, closed.2.2⟩
  | readCell identity payload scope before after selected => exact ⟨rfl, cell_update_resource_closed selected closed.2⟩
  | writeCell identity old new scope before after selected => exact ⟨rfl, cell_update_resource_closed selected closed.2⟩

theorem run_step_preserves_resource_closure (step : RunStep before after)
    (closed : before.configuration.ResourceClosed) : after.configuration.ResourceClosed := by
  cases step with
  | event after created discharged raw fresh => exact raw_step_preserves_resource_closure raw closed

theorem run_steps_preserve_resource_closure (steps : RunSteps before after)
    (closed : before.configuration.ResourceClosed) : after.configuration.ResourceClosed := by
  induction steps with
  | refl => exact closed
  | next first rest ih => exact ih (run_step_preserves_resource_closure first closed)

theorem scoped_execution_preserves_closure_and_ledger (steps : RunSteps before after)
    (closed : before.configuration.ResourceClosed) (ledger : Ledger before.erase) :
    after.configuration.ResourceClosed ∧ Ledger after.erase :=
  ⟨run_steps_preserve_resource_closure steps closed, run_steps_preserve_ledger steps ledger⟩

theorem repeated_calls_preserve_resource_closure : Examples.terminal.configuration.ResourceClosed :=
  run_steps_preserve_resource_closure Examples.repeated_call_execution ⟨rfl, trivial⟩

namespace Examples

def readBody (binder : Nat) : Code :=
  .perform (.cell (.bound binder)) 0 (.resourceRef (.bound binder))

theorem read_body_instantiates (binder identity : Nat) :
    (readBody binder).instantiate (Environment.empty.bind binder identity) =
      .perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)) := by
  simp [readBody, Code.instantiate, Effect.instantiate, ResourceName.instantiate, Environment.bind, freezeEffect]

/-- Acquisition realizes both exact request metadata and its operand with the
    same activation. The active builtin reads that cell before normal release. -/
theorem scoped_cell_read_trace (binder identity : Nat) (payload : Int) (scope : Scope) (answer : Ty) (tail : Stack) :
    RawTrace ⟨.resource binder (.integer payload) (readBody binder), scope, tail⟩
      ⟨.integer payload, scope, tail⟩ [.resource identity] [.resource identity] := by
  have entry := RawStep.enterCell binder identity payload (readBody binder) scope answer tail
    (by simp [Code.ResourceClosed, Code.freeNames, readBody, Effect.freeNames, ResourceName.freeNames])
  rw [read_body_instantiates] at entry
  have read := RawStep.readCell identity payload scope
    (.push (.cell identity payload scope answer) tail) (.push (.cell identity payload scope answer) tail) .hit
  have leave := RawStep.leaveCell identity payload answer scope scope (.integer payload)
    ⟨trivial, rfl, by intro _ present; cases present⟩ tail
  exact .next entry (.next read (.next leave (.refl _)))

theorem fresh_scoped_cell_read (binder : Nat) (payload : Int) (scope : Scope) (answer : Ty) (tail : Stack)
    (issued completed : List Owner) (unique : issued.Nodup) :
    ∃ identity, Owner.resource identity ∉ issued ∧
      RunSteps ⟨⟨.resource binder (.integer payload) (readBody binder), scope, tail⟩, issued, completed⟩
        ⟨⟨.integer payload, scope, tail⟩, issued ++ [.resource identity], .resource identity :: completed⟩ := by
  let prepared := prepareActivation issued
  exact ⟨prepared.identity, prepared.fresh,
    raw_trace_enacts (scoped_cell_read_trace binder prepared.identity payload scope answer tail)
      (prepared_activation_fresh_history prepared unique)⟩

end Examples

end Ash.OneShot.ScopedExecution

#print axioms Ash.OneShot.ScopedExecution.raw_step_preserves_resource_closure
#print axioms Ash.OneShot.ScopedExecution.scoped_execution_preserves_closure_and_ledger
#print axioms Ash.OneShot.ScopedExecution.repeated_calls_preserve_resource_closure
#print axioms Ash.OneShot.ScopedExecution.Examples.fresh_scoped_cell_read
