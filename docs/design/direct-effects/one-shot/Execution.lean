import Usage

/-!
Expression-bearing administrative execution for the one-shot kernel.

Ordinary lexical values are carried by closed substituted syntax. Resource
identities are already instantiated administrative names; fresh source
instantiation remains a separate obligation. Structural ticket binders are
resolved through the current lexical ticket scope. Frame ports and cleanup
request summaries are supplied annotations whose complete typing/inference is
not established here. This module connects concrete control payloads and
expression transitions to the raw ownership ledger, not to full type safety.
-/

namespace Ash.OneShot.Execution
open Syntax

inductive Scope where
  | none
  | ticket (binder owner : Nat)
  deriving DecidableEq, Repr

def Scope.resolve (scope : Scope) (binder : Nat) : Option Nat := match scope with
  | .none => Option.none
  | .ticket localBinder owner => if binder = localBinder then some owner else Option.none

/-- Unresolved free tickets make translation fail; they cannot silently become
    dependencies on an unrelated dynamic owner with the same numeral. -/
def Scope.translate (scope : Scope) : List Dependency → Option (List Nat)
  | [] => some []
  | .ticket binder :: rest => match scope.resolve binder, scope.translate rest with
    | some owner, some owners => some (owner :: owners)
    | _, _ => Option.none
  | _ :: rest => scope.translate rest

inductive Context where
  | pairLeft (right : Expr)
  | pairRight (left : Expr)
  | appFunction (argument : Expr)
  | appArgument (function : Expr)
  | bind (parameter : Nat) (suffix : Expr)
  | branch (yes no : Expr)
  | perform (effectInst : Instance) (operation : Nat)
  | resume (binder : Nat)
  | resource (identity : Nat) (body : Expr)
  | cleanup (body : Expr)

def Context.plug (context : Context) (expression : Expr) : Expr := match context with
  | .pairLeft right => .pair expression right
  | .pairRight left => .pair left expression
  | .appFunction argument => .app expression argument
  | .appArgument function => .app function expression
  | .bind parameter suffix => .bind parameter expression suffix
  | .branch yes no => .branch expression yes no
  | .perform effectInst operation => .perform effectInst operation expression
  | .resume binder => .resume binder expression
  | .resource identity body => .resource identity expression body
  | .cleanup body => .cleanup expression body

def Context.dependencies (context : Context) : List Dependency :=
  (context.plug .unit).dependencies

/-- One strict evaluation position. Scope-establishing handler bodies are not
    focused through: their boundary must be installed first. -/
inductive Focus : Expr → Expr → Context → Prop where
  | pairLeft (notValue : ¬ left.IsValue) : Focus (.pair left right) left (.pairLeft right)
  | pairRight (value : left.IsValue) (notValue : ¬ right.IsValue) :
      Focus (.pair left right) right (.pairRight left)
  | appFunction (notValue : ¬ function.IsValue) :
      Focus (.app function argument) function (.appFunction argument)
  | appArgument (value : function.IsValue) (notValue : ¬ argument.IsValue) :
      Focus (.app function argument) argument (.appArgument function)
  | bind (notValue : ¬ initializer.IsValue) :
      Focus (.bind parameter initializer suffix) initializer (.bind parameter suffix)
  | branch (notValue : ¬ condition.IsValue) :
      Focus (.branch condition yes no) condition (.branch yes no)
  | perform (notValue : ¬ operand.IsValue) :
      Focus (.perform effectInst operation operand) operand (.perform effectInst operation)
  | resume (notValue : ¬ operand.IsValue) :
      Focus (.resume binder operand) operand (.resume binder)
  | resource (notValue : ¬ initializer.IsValue) :
      Focus (.resource identity initializer body) initializer (.resource identity body)
  | cleanup (notValue : ¬ action.IsValue) : Focus (.cleanup action body) action (.cleanup body)

theorem focus_reconstructs (focus : Focus whole child context) : context.plug child = whole := by
  cases focus <;> rfl

structure PlainData where
  context : Context
  scope : Scope
  input : Ty
  output : Ty
  pending : List Nat
  translated : scope.translate context.dependencies = some pending

def PlainData.erase (plain : PlainData) : Frame :=
  ⟨.bind, plain.input, plain.output, resourceDependencies plain.context.dependencies, plain.pending, []⟩

structure HandlerData where
  activation : Nat
  effectInst : Instance
  clauses : Clauses
  scope : Scope
  answer : Ty
  ticketBarrier : ticketDependencies clauses.dependencies = []

def HandlerData.erase (handler : HandlerData) : Frame :=
  ⟨.handler handler.effectInst handler.activation, handler.answer, handler.answer,
    handler.effectInst.resources ++ resourceDependencies handler.clauses.dependencies, [], []⟩

structure ActionData where
  identity : Nat
  action : Expr
  closed : ClosedValue action
  scope : Scope
  answer : Ty
  requests : List Instance

def ActionData.erase (action : ActionData) : Frame :=
  ⟨.armed action.identity, action.answer, action.answer,
    resourceDependencies action.action.dependencies, [], action.requests⟩

inductive ExecFrame where
  | plain (data : PlainData)
  | handler (data : HandlerData)
  | cell (identity : Nat) (payload : Int) (scope : Scope) (answer : Ty)
  | armed (data : ActionData)
  | running (data : ActionData) (saved : Expr) (closed : ClosedValue saved)
  | closing (identity : Nat) (scope : Scope)
  | retiring (ticket : Nat)

def ExecFrame.erase : ExecFrame → Frame
  | .plain data => data.erase
  | .handler data => data.erase
  | .cell identity _ _ answer => ⟨.resource identity, answer, answer, [], [], []⟩
  | .armed data => data.erase
  | .running data saved _ =>
      { data.erase with kind := .running data.identity, input := .unit, access := data.erase.access ++ resourceDependencies saved.dependencies }
  | .closing identity _ => closeFrame identity
  | .retiring ticket => CloseItem.frame (.retire ticket)

inductive Stack where
  | nil
  | push : ExecFrame → Stack → Stack
  | live (ticket : Nat) (operationResult answer : Ty) (saved : Stack) (scope : Scope) (rest : Stack)
  | spent (ticket : Nat) (answer : Ty) (scope : Scope) (rest : Stack)

def Stack.erase : Stack → Control
  | .nil => .nil
  | .push frame rest => .push frame.erase rest.erase
  | .live ticket q a saved _ rest => .live ticket q a saved.erase rest.erase
  | .spent ticket a _ rest => .spent ticket a rest.erase

def Stack.append (stack tail : Stack) : Stack := match stack with
  | .nil => tail
  | .push frame rest => .push frame (rest.append tail)
  | .live ticket q a saved scope rest => .live ticket q a saved scope (rest.append tail)
  | .spent ticket a scope rest => .spent ticket a scope (rest.append tail)

@[simp] theorem erase_append (stack tail : Stack) :
    (stack.append tail).erase = stack.erase.append tail.erase := by
  induction stack <;> simp_all [Stack.append, Stack.erase, Control.append]

theorem stack_append_assoc (a b c : Stack) : (a.append b).append c = a.append (b.append c) := by
  induction a <;> simp_all [Stack.append]

inductive HandlerCut (requested : Instance) : Stack → Stack → Stack → HandlerData → Prop where
  | hit (handler : HandlerData) (tail : Stack) (same : handler.effectInst = requested) :
      HandlerCut requested (.push (.handler handler) tail)
        (.push (.handler handler) .nil) tail handler
  | push (frame : ExecFrame) (rest cap tail : Stack) (handler : HandlerData)
      (miss : frame.erase.target ≠ some requested)
      (next : HandlerCut requested rest cap tail handler) :
      HandlerCut requested (.push frame rest) (.push frame cap) tail handler
  | live (ticket : Nat) (q a : Ty) (saved : Stack) (scope : Scope)
      (rest cap tail : Stack) (handler : HandlerData)
      (next : HandlerCut requested rest cap tail handler) :
      HandlerCut requested (.live ticket q a saved scope rest)
        (.live ticket q a saved scope cap) tail handler
  | spent (ticket : Nat) (a : Ty) (scope : Scope) (rest cap tail : Stack) (handler : HandlerData)
      (next : HandlerCut requested rest cap tail handler) :
      HandlerCut requested (.spent ticket a scope rest) (.spent ticket a scope cap) tail handler

theorem handler_cut_erases (cut : HandlerCut requested whole cap tail handler) :
    SourceCut requested whole.erase cap.erase tail.erase := by
  induction cut with
  | hit handler tail same => exact .hit handler.erase handler.activation tail.erase (by simp [HandlerData.erase, same])
  | push frame rest cap tail handler miss next ih => exact .push frame.erase _ _ _ miss ih
  | live ticket q a saved scope rest cap tail handler next ih => exact .live ticket q a saved.erase _ _ _ ih
  | spent ticket a scope rest cap tail handler next ih => exact .spent ticket a _ _ _ ih

theorem handler_cut_reconstructs (cut : HandlerCut requested whole cap tail handler) :
    whole = cap.append tail := by
  induction cut <;> simp_all [Stack.append]

inductive CloseEntry where
  | release (identity : Nat) (payload : Int)
  | invoke (action : ActionData)
  | retire (ticket : Nat)

def CloseEntry.erase : CloseEntry → CloseItem
  | .release identity _ => .release identity
  | .invoke action => .invoke action.identity action.erase.access action.requests
  | .retire ticket => .retire ticket

def CloseEntry.frame (scope : Scope) : CloseEntry → ExecFrame
  | .release identity payload => .cell identity payload scope .unit
  | .invoke action => .armed { action with scope := scope, answer := .unit }
  | .retire ticket => .retiring ticket

def closeControl (scope : Scope) : List CloseEntry → Stack
  | [] => .nil
  | entry :: rest => .push (entry.frame scope) (closeControl scope rest)

theorem close_control_erases (scope : Scope) (entries : List CloseEntry) :
    (closeControl scope entries).erase = planControl (entries.map CloseEntry.erase) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp_all [closeControl, Stack.erase, CloseEntry.frame, ExecFrame.erase,
        CloseEntry.erase, planControl, CloseItem.frame, ActionData.erase]

/-- This preserves executable cleanup values and cell payloads, while dropping
    abandoned expression contexts and source handlers. Protected frames fail. -/
def makePlan : Stack → Option (List CloseEntry)
  | .nil => some []
  | .push frame rest => match frame, makePlan rest with
    | .plain _, plan | .handler _, plan => plan
    | .cell identity payload _ _, some plan => some (.release identity payload :: plan)
    | .armed action, some plan => some (.invoke action :: plan)
    | _, _ => none
  | .live ticket _ _ saved _ rest => match makePlan saved, makePlan rest with
    | some inside, some outside => some (inside ++ .retire ticket :: outside)
    | _, _ => none
  | .spent _ _ _ rest => makePlan rest

theorem make_plan_erases (stack : Stack) :
    (makePlan stack).map (List.map CloseEntry.erase) = rawPlan stack.erase := by
  induction stack with
  | nil => rfl
  | push frame rest ih =>
      simp only [Stack.erase, rawPlan, ← ih]
      cases frame <;> cases hr : makePlan rest <;>
        simp [makePlan, hr, ExecFrame.erase, PlainData.erase, HandlerData.erase,
          ActionData.erase, closeFrame, CloseItem.frame, CloseEntry.erase]
  | live ticket q a saved scope rest ihSaved ihRest =>
      simp only [Stack.erase, rawPlan, ← ihSaved, ← ihRest]
      cases hs : makePlan saved <;> cases hr : makePlan rest <;>
        simp [makePlan, hs, hr, CloseEntry.erase]
  | spent ticket a scope rest ih => exact ih

inductive ClauseAt (operation : Nat) : Clauses → Nat → Nat → Expr → Prop where
  | hit : ClauseAt operation (.cons operation parameter binder body rest) parameter binder body
  | pass (different : operation ≠ other)
      (next : ClauseAt operation rest parameter binder body) :
      ClauseAt operation (.cons other otherParameter otherBinder otherBody rest) parameter binder body

/-- Exact builtin selection updates only the active cell. A nearer matching
    source handler blocks it, and dormant captures are not searched. -/
inductive CellUpdate (identity : Nat) (old new : Int) : Stack → Stack → Prop where
  | hit : CellUpdate identity old new (.push (.cell identity old scope answer) tail)
      (.push (.cell identity new scope answer) tail)
  | push (miss : frame.erase.target ≠ some (.cell identity))
      (next : CellUpdate identity old new before after) :
      CellUpdate identity old new (.push frame before) (.push frame after)
  | live (next : CellUpdate identity old new before after) :
      CellUpdate identity old new (.live ticket q a saved scope before) (.live ticket q a saved scope after)
  | spent (next : CellUpdate identity old new before after) :
      CellUpdate identity old new (.spent ticket a scope before) (.spent ticket a scope after)

theorem cell_update_erases (update : CellUpdate identity old new before after) :
    before.erase = after.erase := by
  induction update <;> simp_all [Stack.erase, ExecFrame.erase]

structure Configuration where
  expression : Expr
  scope : Scope
  stack : Stack

/-- Raw expression transitions. Capture, resume and disposal do not assume the
    desired ownership invariant or their static admissibility conclusions.
    Resource-name hygiene and lexical closure are explicit administrative
    substitution prerequisites, not an established source-instantiation pass. -/
inductive RawStep : Configuration → Configuration → List Owner → List Owner → Prop where
  | focus (plain : PlainData) (step : Focus whole child plain.context) (tail : Stack) :
      RawStep ⟨whole, plain.scope, tail⟩ ⟨child, plain.scope, .push (.plain plain) tail⟩ [] []
  | plug (plain : PlainData) (value : Expr) (closed : ClosedValue value) (scope : Scope) (tail : Stack) :
      RawStep ⟨value, scope, .push (.plain plain) tail⟩ ⟨plain.context.plug value, plain.scope, tail⟩ [] []
  | bind (parameter : Nat) (value suffix : Expr) (scope : Scope) (tail : Stack)
      (closed : ClosedValue value) (environmentReady : ClosedExcept parameter suffix)
      (fresh : ResourceFresh value suffix) :
      RawStep ⟨.bind parameter value suffix, scope, tail⟩ ⟨suffix.subst parameter value, scope, tail⟩ [] []
  | beta (parameter : Nat) (body value : Expr) (scope : Scope) (tail : Stack)
      (closed : ClosedValue value) (closureReady : ClosedValue (.lambda parameter body))
      (fresh : ResourceFresh value body) :
      RawStep ⟨.app (.lambda parameter body) value, scope, tail⟩
        ⟨body.subst parameter value, .none, tail⟩ [] []
  | ifTrue (yes no : Expr) (scope : Scope) (tail : Stack) :
      RawStep ⟨.branch (.boolean true) yes no, scope, tail⟩ ⟨yes, scope, tail⟩ [] []
  | ifFalse (yes no : Expr) (scope : Scope) (tail : Stack) :
      RawStep ⟨.branch (.boolean false) yes no, scope, tail⟩ ⟨no, scope, tail⟩ [] []
  | enterHandler (handler : HandlerData) (body : Expr) (tail : Stack) :
      RawStep ⟨.handle handler.effectInst body handler.clauses, handler.scope, tail⟩
        ⟨body, handler.scope, .push (.handler handler) tail⟩ [] []
  | leaveHandler (handler : HandlerData) (value : Expr) (closed : ClosedValue value)
      (scope : Scope) (tail : Stack) :
      RawStep ⟨value, scope, .push (.handler handler) tail⟩ ⟨value, handler.scope, tail⟩ [] []
  | enterCell (identity : Nat) (payload : Int) (body : Expr) (scope : Scope) (answer : Ty) (tail : Stack) :
      RawStep ⟨.resource identity (.integer payload) body, scope, tail⟩
        ⟨body, scope, .push (.cell identity payload scope answer) tail⟩ [.resource identity] []
  | leaveCell (identity : Nat) (payload : Int) (answer : Ty) (savedScope scope : Scope)
      (value : Expr) (closed : ClosedValue value) (tail : Stack) :
      RawStep ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩
        ⟨value, savedScope, tail⟩ [] [.resource identity]
  | enterCleanup (action : ActionData) (body : Expr) (tail : Stack) :
      RawStep ⟨.cleanup action.action body, action.scope, tail⟩
        ⟨body, action.scope, .push (.armed action) tail⟩ [.cleanup action.identity] []
  | startCleanup (action : ActionData) (saved : Expr) (closed : ClosedValue saved)
      (scope : Scope) (tail : Stack) :
      RawStep ⟨saved, scope, .push (.armed action) tail⟩
        ⟨.app action.action .unit, .none, .push (.running action saved closed) tail⟩ [] []
  | finishCleanup (action : ActionData) (saved : Expr) (closed : ClosedValue saved)
      (scope : Scope) (tail : Stack) :
      RawStep ⟨.unit, scope, .push (.running action saved closed) tail⟩
        ⟨saved, action.scope, tail⟩ [] [.cleanup action.identity]
  | capture (requested : Instance) (operation parameter binder ticket : Nat)
      (operand body : Expr) (scope : Scope) (whole cap tail : Stack) (handler : HandlerData)
      (operationResult : Ty) (selection : HandlerCut requested whole cap tail handler)
      (clause : ClauseAt operation handler.clauses parameter binder body)
      (closed : ClosedValue operand) (environmentReady : ClosedExcept parameter body)
      (fresh : ResourceFresh operand body) :
      RawStep ⟨.perform requested operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder ticket,
          .live ticket operationResult handler.answer cap handler.scope tail⟩ [.ticket ticket] []
  | resume (binder ticket : Nat) (scope callerScope : Scope) (q a : Ty) (front cap tail : Stack)
      (value : Expr) (closed : ClosedValue value) (resolve : scope.resolve binder = some ticket) :
      RawStep ⟨.resume binder value, scope, front.append (.live ticket q a cap callerScope tail)⟩
        ⟨value, scope, cap.append (front.append (.spent ticket a callerScope tail))⟩ [] [.ticket ticket]
  | discard (binder ticket closeId : Nat) (scope callerScope : Scope) (q a : Ty)
      (front cap tail : Stack) (plan : List CloseEntry) (resolve : scope.resolve binder = some ticket)
      (build : makePlan cap = some plan) :
      RawStep ⟨.discard binder, scope, front.append (.live ticket q a cap callerScope tail)⟩
        ⟨.unit, scope, (closeControl scope plan).append
          (.push (.closing closeId scope) (front.append (.spent ticket a callerScope tail)))⟩
        [.close closeId] [.ticket ticket]
  | leaveClause (ticket : Nat) (answer : Ty) (value : Expr) (closed : ClosedValue value)
      (scope callerScope : Scope) (tail : Stack) :
      RawStep ⟨value, scope, .spent ticket answer callerScope tail⟩ ⟨value, callerScope, tail⟩ [] []
  | finishClose (identity : Nat) (scope callerScope : Scope) (tail : Stack) :
      RawStep ⟨.unit, scope, .push (.closing identity callerScope) tail⟩
        ⟨.unit, callerScope, tail⟩ [] [.close identity]
  | retire (ticket : Nat) (scope : Scope) (tail : Stack) :
      RawStep ⟨.unit, scope, .push (.retiring ticket) tail⟩ ⟨.unit, scope, tail⟩ [] [.ticket ticket]
  | readCell (identity : Nat) (payload : Int) (scope : Scope) (before after : Stack)
      (selected : CellUpdate identity payload payload before after) :
      RawStep ⟨.perform (.cell identity) 0 (.resourceRef identity), scope, before⟩
        ⟨.integer payload, scope, after⟩ [] []
  | writeCell (identity : Nat) (old new : Int) (scope : Scope) (before after : Stack)
      (selected : CellUpdate identity old new before after) :
      RawStep ⟨.perform (.cell identity) 1 (.pair (.resourceRef identity) (.integer new)), scope, before⟩
        ⟨.unit, scope, after⟩ [] []

theorem raw_step_erases (step : RawStep before after created discharged) :
    Flow before.stack.erase after.stack.erase created discharged := by
  cases step with
  | focus plain step tail => exact .enter plain.erase tail.erase trivial
  | plug plain value closed scope tail => exact .leavePlain plain.erase tail.erase rfl
  | bind | beta | ifTrue | ifFalse => exact .stay _
  | enterHandler handler body tail => exact .enter handler.erase tail.erase trivial
  | leaveHandler handler value closed scope tail => exact .leavePlain handler.erase tail.erase rfl
  | enterCell identity payload body scope answer tail =>
      exact .enter (ExecFrame.erase (.cell identity payload scope answer)) tail.erase trivial
  | leaveCell identity payload answer savedScope scope value closed tail =>
      exact .release (ExecFrame.erase (.cell identity payload savedScope answer)) identity tail.erase rfl
  | enterCleanup action body tail => exact .enter action.erase tail.erase trivial
  | startCleanup action saved closed scope tail =>
      exact .startAction action.erase action.identity tail.erase (resourceDependencies saved.dependencies) rfl
  | finishCleanup action saved closed scope tail =>
      exact .finishAction (ExecFrame.erase (.running action saved closed)) action.identity tail.erase rfl
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler
      operationResult selection clause closed environmentReady fresh =>
      exact .capture requested ticket operationResult handler.answer _ _ _ (handler_cut_erases selection)
  | resume binder ticket scope callerScope q a front cap tail value closed resolve =>
      simpa only [erase_append, Stack.erase] using
        Flow.resume ticket q a front.erase cap.erase tail.erase
  | discard binder ticket closeId scope callerScope q a front cap tail plan resolve build =>
      have erasedBuild : rawPlan cap.erase = some (plan.map CloseEntry.erase) := by
        rw [← make_plan_erases, build]
        rfl
      simpa only [erase_append, Stack.erase, close_control_erases, ExecFrame.erase] using
        Flow.discard ticket closeId q a front.erase cap.erase tail.erase _ erasedBuild
  | leaveClause ticket answer value closed scope callerScope tail => exact .leaveClause ticket answer tail.erase
  | finishClose identity scope callerScope tail => exact .finishClose (closeFrame identity) identity tail.erase rfl
  | retire ticket scope tail => exact .retire (CloseItem.frame (.retire ticket)) ticket tail.erase rfl
  | readCell identity payload scope before after selected =>
      simpa only [cell_update_erases selected] using Flow.stay before.erase
  | writeCell identity old new scope before after selected =>
      simpa only [cell_update_erases selected] using Flow.stay before.erase

structure RunState where
  configuration : Configuration
  issued : List Owner
  completed : List Owner

def RunState.erase (state : RunState) : State :=
  ⟨state.configuration.stack.erase, state.issued, state.completed⟩

inductive RunStep : RunState → RunState → Prop where
  | event (before : RunState) (after : Configuration) (created discharged : List Owner)
      (step : RawStep before.configuration after created discharged)
      (fresh : (before.issued ++ created).Nodup) :
      RunStep before ⟨after, before.issued ++ created, discharged ++ before.completed⟩

theorem run_step_erases (step : RunStep before after) : Step before.erase after.erase := by
  cases step with
  | event after created discharged step fresh =>
      exact .event before.erase after.stack.erase created discharged (raw_step_erases step) fresh

theorem run_step_preserves_ledger (step : RunStep before after) (ledger : Ledger before.erase) :
    Ledger after.erase := step_preserves_ledger (run_step_erases step) ledger

inductive RunSteps : RunState → RunState → Prop where
  | refl (state : RunState) : RunSteps state state
  | next (first : RunStep before middle) (rest : RunSteps middle after) : RunSteps before after

theorem run_steps_preserve_ledger (steps : RunSteps before after) (ledger : Ledger before.erase) :
    Ledger after.erase := by
  induction steps with
  | refl => exact ledger
  | next first rest ih => exact ih (run_step_preserves_ledger first ledger)

theorem run_no_double_completion (steps : RunSteps before after) (ledger : Ledger before.erase) :
    after.completed.Nodup := ledger_no_double_completion (run_steps_preserve_ledger steps ledger)

/-- A raw trace records fresh creations in execution order and completions in
    the ledger's newest-first order. It does not assume that allocation is fresh. -/
inductive RawTrace : Configuration → Configuration → List Owner → List Owner → Prop where
  | refl (configuration : Configuration) : RawTrace configuration configuration [] []
  | next (first : RawStep before middle created discharged)
      (rest : RawTrace middle after laterCreated laterDischarged) :
      RawTrace before after (created ++ laterCreated) (laterDischarged ++ discharged)

theorem raw_trace_enacts (trace : RawTrace before after created discharged)
    (fresh : (issued ++ created).Nodup) :
    RunSteps ⟨before, issued, completed⟩ ⟨after, issued ++ created, discharged ++ completed⟩ := by
  induction trace generalizing issued completed with
  | refl configuration => simpa using RunSteps.refl (⟨configuration, issued, completed⟩ : RunState)
  | @next before middle made done after laterMade laterDone first rest ih =>
      have allFresh : ((issued ++ made) ++ laterMade).Nodup := by simpa [List.append_assoc] using fresh
      have firstStep := RunStep.event ⟨before, issued, completed⟩ middle made done first
        (List.nodup_append.mp allFresh).1
      have following := ih (issued := issued ++ made) (completed := done ++ completed) allFresh
      simpa only [List.append_assoc] using RunSteps.next firstStep following

theorem start_cleanup_preserves_retained_support
    {action : ActionData} {tail : Stack}
    (support : Supported (.push action.erase tail.erase) ambient)
    (closed : ClosedValue saved)
    (savedSupported : resourceDependencies saved.dependencies ⊆ tail.erase.visible ++ ambient) :
    Supported (.push (ExecFrame.erase (.running action saved closed)) tail.erase) ambient := by
  cases support with
  | push frame rest ambient next access =>
      apply Supported.push _ _ _ next
      intro resource retained
      rcases List.mem_append.mp retained with inAction | inSaved
      · exact access inAction
      · exact savedSupported inSaved

namespace Examples

theorem closed_unit : ClosedValue .unit := by simp [ClosedValue, Expr.IsValue, Expr.dependencies]
theorem closed_integer (n : Int) : ClosedValue (.integer n) := by
  simp [ClosedValue, Expr.IsValue, Expr.dependencies]
theorem closed_reference (r : Nat) : ClosedValue (.resourceRef r) := by
  simp [ClosedValue, Expr.IsValue, Expr.dependencies]

def callbackBody : Expr := .perform (.user 1 []) 0 .unit
def callback : Expr := .lambda 0 callbackBody

theorem callback_closed : ClosedValue callback := by
  simp [callback, callbackBody, ClosedValue, Expr.IsValue, Expr.dependencies,
    instanceDependencies, Instance.resources, without]

def action : ActionData := ⟨7, callback, callback_closed, .none, .integer, [.user 1 []]⟩

def clauses : Clauses := .cons 0 1 9 (.resume 9 .unit) .nil
def handler : HandlerData := ⟨8, .user 1 [], clauses, .none, .integer, by
  simp [clauses, ticketDependencies, Clauses.dependencies, Expr.dependencies, without]⟩

def handlerStack : Stack := .push (.handler handler) .nil
def captureStack : Stack := .push (.running action (.integer 42) (closed_integer 42)) handlerStack
def spentStack : Stack := .spent 3 .integer .none .nil
def capturedState : Configuration :=
  ⟨.resume 9 .unit, .ticket 9 3, .live 3 .unit .integer captureStack .none .nil⟩

/-- The callback actually requests an operation, its running completion is
    captured and resumed, and only its returned unit discharges cleanup. -/
theorem cleanup_outward_capture_trace :
    RawTrace
      ⟨.handle (.user 1 []) (.cleanup callback (.integer 42)) clauses, .none, .nil⟩
      ⟨.integer 42, .none, .nil⟩
      [.cleanup 7, .ticket 3] [.cleanup 7, .ticket 3] := by
  have select : HandlerCut (.user 1 []) captureStack captureStack .nil handler :=
    .push _ _ _ _ _ (by simp [ExecFrame.erase, Frame.target]) (.hit handler .nil rfl)
  have e0 := RawStep.enterHandler handler (.cleanup callback (.integer 42)) .nil
  have e1 := RawStep.enterCleanup action (.integer 42) handlerStack
  have e2 := RawStep.startCleanup action (.integer 42) (closed_integer 42) .none handlerStack
  have e3 := RawStep.beta 0 callbackBody .unit .none captureStack closed_unit callback_closed
    (by simp [ResourceFresh, Expr.dependencies])
  have e4 := RawStep.capture (.user 1 []) 0 1 9 3 .unit (.resume 9 .unit) .none
    captureStack captureStack .nil handler .unit select (.hit) closed_unit
    (by simp [ClosedExcept, Expr.dependencies]) (by simp [ResourceFresh, Expr.dependencies])
  have e5 := RawStep.resume 9 3 (.ticket 9 3) .none .unit .integer .nil captureStack .nil .unit closed_unit rfl
  have e6 := RawStep.finishCleanup action (.integer 42) (closed_integer 42) (.ticket 9 3)
    (.push (.handler handler) spentStack)
  have e7 := RawStep.leaveHandler handler (.integer 42) (closed_integer 42) .none spentStack
  have e8 := RawStep.leaveClause 3 .integer (.integer 42) (closed_integer 42) .none .none .nil
  exact .next e0 (.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.next e7
    (.next e8 (.refl _)))))))))

theorem cleanup_outward_capture_execution :
    RunSteps
      ⟨⟨.handle (.user 1 []) (.cleanup callback (.integer 42)) clauses, .none, .nil⟩, [], []⟩
      ⟨⟨.integer 42, .none, .nil⟩, [.cleanup 7, .ticket 3], [.cleanup 7, .ticket 3]⟩ :=
  raw_trace_enacts cleanup_outward_capture_trace (by decide)

theorem completed_callback_has_no_duplicate_completion :
    Ledger (⟨⟨.integer 42, .none, .nil⟩, [.cleanup 7, .ticket 3], [.cleanup 7, .ticket 3]⟩ : RunState).erase :=
  run_steps_preserve_ledger cleanup_outward_capture_execution ⟨.refl [], by decide⟩

theorem running_retains_saved_resource :
    4 ∈ (ExecFrame.erase (.running action (.resourceRef 4) (closed_reference 4))).access := by
  simp [ExecFrame.erase, Expr.dependencies, resourceDependencies]

theorem running_cannot_be_disposed : makePlan captureStack = none := rfl

theorem unresolved_ticket_cannot_be_annotated :
    Scope.none.translate (Context.resume 9).dependencies = none := rfl

theorem binder_resolves_to_dynamic_owner :
    (Scope.ticket 9 3).translate (Context.resume 9).dependencies = some [3] := rfl

def readBody : Expr := .bind 0 (.perform (.cell 4) 0 (.resourceRef 4)) .unit
def readCallback : Expr := .lambda 2 readBody
theorem read_callback_closed : ClosedValue readCallback := by
  simp [readCallback, readBody, ClosedValue, Expr.IsValue, Expr.dependencies,
    instanceDependencies, Instance.resources, without]

def readAction : ActionData := ⟨7, readCallback, read_callback_closed, .none, .unit, [.cell 4]⟩
def discardHandler : HandlerData := ⟨10, .user 1 [], .cons 0 1 9 (.discard 9) .nil, .none, .unit, by
  simp [ticketDependencies, Clauses.dependencies, Expr.dependencies, without]⟩
def abandoned : Stack := .push (.armed readAction)
  (.push (.cell 4 17 .none .unit) (.push (.handler discardHandler) .nil))
def closePlan : List CloseEntry := [.invoke readAction, .release 4 17]
def closeScope : Scope := .ticket 9 3
def closingAction : ActionData := { readAction with scope := closeScope, answer := .unit }
def closeTail : Stack := .push (.closing 8 closeScope) (.spent 3 .unit .none .nil)
def closeCellTail : Stack := .push (.cell 4 17 closeScope .unit) closeTail
def runningClose : Stack := .push (.running closingAction .unit closed_unit) closeCellTail
def readSuffix : PlainData := ⟨.bind 0 .unit, .none, .integer, .unit, [], rfl⟩

theorem cell_cleanup_disposal_is_admitted :
    Discardable abandoned.erase (.spent 3 .unit .nil) (closePlan.map CloseEntry.erase) := by
  refine .checked ?_ .nil
  refine Closes.armed readAction.erase 7 _ _ _ [.release 4] rfl rfl ?_ ?_ ?_
  · simp [readAction, ActionData.erase, readCallback, readBody, Expr.dependencies,
      instanceDependencies, Instance.resources, resourceDependencies, without,
      planControl, CloseItem.frame, Control.append, Control.visible, Frame.visible]
  · exact .cons (.cell 4) [] (.builtin 4) rfl rfl .nil
  · exact .resource _ 4 _ _ _ [] rfl
      (.handler discardHandler.erase (.user 1 []) 10 _ _ _ [] rfl (.nil _ _))

/-- The discarded callback reads the retained cell through ordinary focus,
    builtin request, binding return, and application completion before release. -/
theorem disposal_reads_cell_before_release :
    RawTrace ⟨.discard 9, closeScope, .live 3 .unit .unit abandoned .none .nil⟩
      ⟨.unit, .none, .nil⟩ [.close 8] [.close 8, .resource 4, .cleanup 7, .ticket 3] := by
  have e0 := RawStep.discard 9 3 8 closeScope .none .unit .unit .nil abandoned .nil closePlan rfl rfl
  have e1 := RawStep.startCleanup closingAction .unit closed_unit closeScope closeCellTail
  have e2 := RawStep.beta 2 readBody .unit .none runningClose closed_unit read_callback_closed
    (by simp [ResourceFresh, Expr.dependencies])
  have e3 := RawStep.focus readSuffix
    (Focus.bind (initializer := .perform (.cell 4) 0 (.resourceRef 4))
      (by simp [Expr.IsValue])) runningClose
  have cell : CellUpdate 4 17 17 (.push (.plain readSuffix) runningClose)
      (.push (.plain readSuffix) runningClose) :=
    .push (by simp [ExecFrame.erase, PlainData.erase, Frame.target])
      (.push (by simp [ExecFrame.erase, Frame.target]) .hit)
  have e4 := RawStep.readCell 4 17 .none _ _ cell
  have e5 := RawStep.plug readSuffix (.integer 17) (closed_integer 17) .none runningClose
  have e6 := RawStep.bind 0 (.integer 17) .unit .none runningClose (closed_integer 17)
    (by simp [ClosedExcept, Expr.dependencies]) (by simp [ResourceFresh, Expr.dependencies])
  have e7 := RawStep.finishCleanup closingAction .unit closed_unit .none closeCellTail
  have e8 := RawStep.leaveCell 4 17 .unit closeScope closeScope .unit closed_unit closeTail
  have e9 := RawStep.finishClose 8 closeScope closeScope (.spent 3 .unit .none .nil)
  have e10 := RawStep.leaveClause 3 .unit .unit closed_unit closeScope .none .nil
  exact .next e0 (.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.next e7
    (.next e8 (.next e9 (.next e10 (.refl _)))))))))))

theorem disposal_execution_preserves_ledger :
    Ledger (⟨⟨.unit, .none, .nil⟩,
      [.resource 4, .cleanup 7, .ticket 3, .close 8],
      [.close 8, .resource 4, .cleanup 7, .ticket 3]⟩ : RunState).erase := by
  have execution := raw_trace_enacts disposal_reads_cell_before_release
    (issued := [.resource 4, .cleanup 7, .ticket 3]) (completed := []) (by decide)
  apply run_steps_preserve_ledger execution
  constructor
  · exact (List.reverse_perm [Owner.resource 4, .cleanup 7, .ticket 3]).symm
  · decide

/-- Deliberately unsafe raw execution: conservation alone does not prevent an
    escaped reference. The missing joint typing/support invariant must reject it. -/
theorem raw_dangling_reference_trace :
    RawTrace ⟨.resource 4 (.integer 0) (.resourceRef 4), .none, .nil⟩
      ⟨.resourceRef 4, .none, .nil⟩ [.resource 4] [.resource 4] :=
  .next (.enterCell 4 0 (.resourceRef 4) .none .unit .nil)
    (.next (.leaveCell 4 0 .unit .none .none (.resourceRef 4) (closed_reference 4) .nil) (.refl _))

theorem ledger_does_not_establish_result_support :
    Ledger (⟨⟨.resourceRef 4, .none, .nil⟩, [.resource 4], [.resource 4]⟩ : RunState).erase ∧
      ¬ resourceDependencies (Expr.resourceRef 4).dependencies ⊆ (Stack.nil.erase.visible ++ []) := by
  constructor
  · exact run_steps_preserve_ledger (raw_trace_enacts raw_dangling_reference_trace
      (issued := []) (completed := []) (by decide))
      ⟨.refl [], by decide⟩
  · simp [Expr.dependencies, resourceDependencies, Stack.erase, Control.visible]

end Examples

end Ash.OneShot.Execution

#print axioms Ash.OneShot.Execution.handler_cut_erases
#print axioms Ash.OneShot.Execution.handler_cut_reconstructs
#print axioms Ash.OneShot.Execution.make_plan_erases
#print axioms Ash.OneShot.Execution.raw_step_erases
#print axioms Ash.OneShot.Execution.run_steps_preserve_ledger
#print axioms Ash.OneShot.Execution.start_cleanup_preserves_retained_support
#print axioms Ash.OneShot.Execution.Examples.cleanup_outward_capture_execution
#print axioms Ash.OneShot.Execution.Examples.cell_cleanup_disposal_is_admitted
#print axioms Ash.OneShot.Execution.Examples.disposal_reads_cell_before_release
#print axioms Ash.OneShot.Execution.Examples.ledger_does_not_establish_result_support
