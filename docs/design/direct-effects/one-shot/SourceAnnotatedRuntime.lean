import SourceAnnotatedRecomposition

/-! Runtime data retain annotated syntax in every code-bearing frame and in
recursively saved continuations. Erasure uses the existing scoped machine and
its ownership semantics; this data layer contains no typing or future-success
certificate. -/
namespace Ash.OneShot.SourceAnnotatedRuntime
open ScopedExpressions (ClosedValue)
open ScopedExecution (Scope)
open SourceAnnotatedCode (Term Clauses Context)

structure Plain where
  context : Context
  scope : Scope
  input : Ty
  output : Ty
  pending : List Nat
  translated : scope.translate context.erase.dependencies = some pending

def Plain.erase (plain : Plain) : ScopedExecution.PlainData :=
  ⟨plain.context.erase, plain.scope, plain.input, plain.output, plain.pending, plain.translated⟩

def Plain.ofRaw (plain : ScopedExecution.PlainData) (context : Context) (same : context.erase = plain.context) : Plain :=
  ⟨context, plain.scope, plain.input, plain.output, plain.pending, by simpa only [same] using plain.translated⟩

theorem Plain.erase_ofRaw (plain : ScopedExecution.PlainData) (context : Context) (same : context.erase = plain.context) :
    (Plain.ofRaw plain context same).erase = plain := by
  cases plain
  cases same
  rfl

structure Handler where
  activation : Nat
  effectInst : Instance
  clauses : Clauses
  scope : Scope
  answer : Ty
  ticketBarrier : Syntax.ticketDependencies clauses.erase.dependencies = []

def Handler.erase (handler : Handler) : ScopedExecution.HandlerData :=
  ⟨handler.activation, handler.effectInst, handler.clauses.erase, handler.scope, handler.answer, handler.ticketBarrier⟩

structure Action where
  identity : Nat
  action : Term
  closed : ClosedValue action.erase
  scope : Scope
  answer : Ty
  requests : List Instance

def Action.erase (action : Action) : ScopedExecution.ActionData :=
  ⟨action.identity, action.action.erase, action.closed, action.scope, action.answer, action.requests⟩

inductive Frame where
  | plain (data : Plain)
  | handler (data : Handler)
  | cell (identity : Nat) (payload : Int) (scope : Scope) (answer : Ty)
  | armed (data : Action)
  | running (data : Action) (saved : Term) (closed : ClosedValue saved.erase)
  | closing (identity : Nat) (scope : Scope)
  | retiring (ticket : Nat)

def Frame.erase : Frame → ScopedExecution.ExecFrame
  | .plain data => .plain data.erase
  | .handler data => .handler data.erase
  | .cell identity payload scope answer => .cell identity payload scope answer
  | .armed data => .armed data.erase
  | .running data saved closed => .running data.erase saved.erase closed
  | .closing identity scope => .closing identity scope
  | .retiring ticket => .retiring ticket

inductive Stack where
  | nil
  | push : Frame → Stack → Stack
  | live (ticket : Nat) (operationResult answer : Ty) (saved : Stack) (scope : Scope) (rest : Stack)
  | spent (ticket : Nat) (answer : Ty) (scope : Scope) (rest : Stack)

def Stack.erase : Stack → ScopedExecution.Stack
  | .nil => .nil
  | .push frame rest => .push frame.erase rest.erase
  | .live ticket input answer saved scope rest => .live ticket input answer saved.erase scope rest.erase
  | .spent ticket answer scope rest => .spent ticket answer scope rest.erase

def Stack.append (stack tail : Stack) : Stack := match stack with
  | .nil => tail
  | .push frame rest => .push frame (rest.append tail)
  | .live ticket input answer saved scope rest => .live ticket input answer saved scope (rest.append tail)
  | .spent ticket answer scope rest => .spent ticket answer scope (rest.append tail)

theorem Stack.erase_append (stack tail : Stack) :
    (stack.append tail).erase = stack.erase.append tail.erase := by
  induction stack <;> simp_all [Stack.append, Stack.erase, ScopedExecution.Stack.append]

theorem Stack.append_assoc (first second third : Stack) :
    (first.append second).append third = first.append (second.append third) := by
  induction first <;> simp_all [Stack.append]

structure Configuration where
  expression : Term
  scope : Scope
  stack : Stack

def Configuration.erase (configuration : Configuration) : ScopedExecution.Configuration :=
  ⟨configuration.expression.erase, configuration.scope, configuration.stack.erase⟩

/-- The retained annotated context projects to the existing focus step. -/
theorem focus_executes (plain : Plain)
    (focus : SourceAnnotatedCode.Focus whole child plain.context) (tail : Stack) :
    ScopedExecution.RawStep
      (Configuration.erase ⟨whole, plain.scope, tail⟩)
      (Configuration.erase ⟨child, plain.scope, .push (.plain plain) tail⟩) [] [] :=
  .focus plain.erase focus.erase tail.erase

/-- Returning a closed annotated value reconstructs the same erased context.
The raw machine's existing saved-scope rule is retained. -/
theorem plug_executes (plain : Plain) (value : Term) (closed : ClosedValue value.erase)
    (scope : Scope) (tail : Stack) :
    ScopedExecution.RawStep
      (Configuration.erase ⟨value, scope, .push (.plain plain) tail⟩)
      (Configuration.erase ⟨plain.context.plug value, plain.scope, tail⟩) [] [] := by
  simpa only [Configuration.erase, Stack.erase, Frame.erase, Plain.erase, SourceAnnotatedCode.Context.erase_plug] using
    (ScopedExecution.RawStep.plug plain.erase value.erase closed scope tail.erase)

/-- Bind, beta and branch retain the annotated stack and use the established
ordinary syntax reduction and its erasure proof. -/
theorem ordinary_executes (step : SourceAnnotatedCode.Reduction before scope after nextScope) (stack : Stack) :
    ScopedExecution.RawStep
      (Configuration.erase ⟨before, scope, stack⟩)
      (Configuration.erase ⟨after, nextScope, stack⟩) [] [] := step.executes stack.erase

end Ash.OneShot.SourceAnnotatedRuntime

#print axioms Ash.OneShot.SourceAnnotatedRuntime.Plain.erase_ofRaw
#print axioms Ash.OneShot.SourceAnnotatedRuntime.Stack.erase_append
#print axioms Ash.OneShot.SourceAnnotatedRuntime.Stack.append_assoc
#print axioms Ash.OneShot.SourceAnnotatedRuntime.focus_executes
#print axioms Ash.OneShot.SourceAnnotatedRuntime.plug_executes
#print axioms Ash.OneShot.SourceAnnotatedRuntime.ordinary_executes
