import ScopedExpressions

/-!
Operational integration of scoped resource code with one-shot control.
The full transition grammar retains templates in callable bodies, allocates
activations at acquisition, and projects to the existing ownership calculus.
Joint source admission and Core simulation remain separate proof obligations.
-/

namespace Ash.OneShot.ScopedExpressions
open Instantiation Syntax

def effectAtoms (effect : Effect) : List Nat := effect.resources.filterMap fun name =>
  match name with | .activation key => some key | .bound _ => none

mutual
def Code.dependencies : Code → List Dependency
  | .unit | .boolean _ | .integer _ => []
  | .variable name => [.variable name]
  | .resourceRef (.bound _) => []
  | .resourceRef (.activation key) => [.resource key]
  | .pair left right | .app left right | .cleanup left right => left.dependencies ++ right.dependencies
  | .lambda parameter body => without (.variable parameter) body.dependencies
  | .bind name initializer body => initializer.dependencies ++ without (.variable name) body.dependencies
  | .branch condition yes no => condition.dependencies ++ yes.dependencies ++ no.dependencies
  | .perform effect _ operand => (effectAtoms effect).map Dependency.resource ++ operand.dependencies
  | .handle effect body clauses => (effectAtoms effect).map Dependency.resource ++ body.dependencies ++ clauses.dependencies
  | .resume ticket operand => .ticket ticket :: operand.dependencies
  | .discard ticket => [.ticket ticket]
  | .resource _ initializer body => initializer.dependencies ++ body.dependencies

def Clauses.dependencies : Clauses → List Dependency
  | .nil => []
  | .cons _ parameter ticket body rest =>
      without (.ticket ticket) (without (.variable parameter) body.dependencies) ++ rest.dependencies
end

def Code.IsValue : Code → Prop
  | .unit | .boolean _ | .integer _ | .resourceRef (.activation _) | .lambda _ _ => True
  | .pair left right => left.IsValue ∧ right.IsValue
  | _ => False

/-- Source-name closure is independent of ordinary/ticket closure and of the
    live-support judgment. Locally bound resource sites remain deferred. -/
def ClosedValue (value : Code) : Prop :=
  value.IsValue ∧ value.ResourceClosed ∧ ∀ dependency ∈ value.dependencies,
    match dependency with | .resource _ => True | _ => False

def ClosedExcept (parameter : Nat) (suffix : Code) : Prop :=
  ∀ name, Dependency.variable name ∈ suffix.dependencies → name = parameter

theorem Code.subst_resource_closed (code value : Code) (name : Nat)
    (codeClosed : code.ResourceClosed) (valueClosed : value.ResourceClosed) :
    (code.subst name value).ResourceClosed := by
  have resolved := ((code.subst name value).instantiation_closes_iff (fun _ => some 0)).mpr
    (fun _ _ => ⟨0, rfl⟩)
  rw [code.instantiation_subst name value _ valueClosed,
    code.closed_instantiation_identity _ codeClosed] at resolved
  exact resolved

end Ash.OneShot.ScopedExpressions

namespace Ash.OneShot.ScopedExecution
open Instantiation ScopedExpressions
open Syntax (resourceDependencies ticketDependencies Dependency)

abbrev Scope := Execution.Scope

inductive Context where
  | pairLeft (right : Code)
  | pairRight (left : Code)
  | appFunction (argument : Code)
  | appArgument (function : Code)
  | bind (parameter : Nat) (suffix : Code)
  | branch (yes no : Code)
  | perform (effectInst : Effect) (operation : Nat)
  | resume (binder : Nat)
  | resource (identity : Nat) (body : Code)
  | cleanup (body : Code)

def Context.plug (context : Context) (expression : Code) : Code := match context with
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
inductive Focus : Code → Code → Context → Prop where
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
  action : Code
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
  | running (data : ActionData) (saved : Code) (closed : ClosedValue saved)
  /-- An internal cleanup return point that continues abandonment, not a value return. -/
  | unwinding (data : ActionData)
  | closing (identity : Nat) (scope : Scope)
  | retiring (ticket : Nat)

def ExecFrame.erase : ExecFrame → Frame
  | .plain data => data.erase
  | .handler data => data.erase
  | .cell identity _ _ answer => ⟨.resource identity, answer, answer, [], [], []⟩
  | .armed data => data.erase
  | .running data saved _ =>
      { data.erase with kind := .running data.identity, input := .unit, access := data.erase.access ++ resourceDependencies saved.dependencies }
  | .unwinding data => { data.erase with kind := .running data.identity, input := .unit }
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

inductive ClauseAt (operation : Nat) : Clauses → Nat → Nat → Code → Prop where
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
  expression : Code
  scope : Scope
  stack : Stack

/-- Scoped execution retains acquisition templates inside callable code and
    instantiates a body at each entry. Raw rules do not establish source typing,
    capture compatibility, live support, or permitted disposal by themselves. -/
inductive RawStep : Configuration → Configuration → List Owner → List Owner → Prop where
  | focus (plain : PlainData) (step : Focus whole child plain.context) (tail : Stack) :
      RawStep ⟨whole, plain.scope, tail⟩ ⟨child, plain.scope, .push (.plain plain) tail⟩ [] []
  | plug (plain : PlainData) (value : Code) (closed : ClosedValue value) (scope : Scope) (tail : Stack) :
      RawStep ⟨value, scope, .push (.plain plain) tail⟩ ⟨plain.context.plug value, plain.scope, tail⟩ [] []
  | bind (parameter : Nat) (value suffix : Code) (scope : Scope) (tail : Stack)
      (closed : ClosedValue value) (environmentReady : ClosedExcept parameter suffix) :
      RawStep ⟨.bind parameter value suffix, scope, tail⟩ ⟨suffix.subst parameter value, scope, tail⟩ [] []
  | beta (parameter : Nat) (body value : Code) (scope : Scope) (tail : Stack)
      (closed : ClosedValue value) (closureReady : ClosedValue (.lambda parameter body)) :
      RawStep ⟨.app (.lambda parameter body) value, scope, tail⟩
        ⟨body.subst parameter value, .none, tail⟩ [] []
  | ifTrue (yes no : Code) (scope : Scope) (tail : Stack) :
      RawStep ⟨.branch (.boolean true) yes no, scope, tail⟩ ⟨yes, scope, tail⟩ [] []
  | ifFalse (yes no : Code) (scope : Scope) (tail : Stack) :
      RawStep ⟨.branch (.boolean false) yes no, scope, tail⟩ ⟨no, scope, tail⟩ [] []
  | enterHandler (handler : HandlerData) (body : Code) (tail : Stack) :
      RawStep ⟨.handle (freezeEffect handler.effectInst) body handler.clauses, handler.scope, tail⟩
        ⟨body, handler.scope, .push (.handler handler) tail⟩ [] []
  | leaveHandler (handler : HandlerData) (value : Code) (closed : ClosedValue value)
      (scope : Scope) (tail : Stack) :
      RawStep ⟨value, scope, .push (.handler handler) tail⟩ ⟨value, handler.scope, tail⟩ [] []
  | enterCell (binder identity : Nat) (payload : Int) (body : Code) (scope : Scope) (answer : Ty) (tail : Stack)
      (instantiationReady : (Code.resource binder (.integer payload) body).ResourceClosed) :
      RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
        ⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩ [.resource identity] []
  | leaveCell (identity : Nat) (payload : Int) (answer : Ty) (savedScope scope : Scope)
      (value : Code) (closed : ClosedValue value) (tail : Stack) :
      RawStep ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩
        ⟨value, savedScope, tail⟩ [] [.resource identity]
  | enterCleanup (action : ActionData) (body : Code) (tail : Stack) :
      RawStep ⟨.cleanup action.action body, action.scope, tail⟩
        ⟨body, action.scope, .push (.armed action) tail⟩ [.cleanup action.identity] []
  | startCleanup (action : ActionData) (saved : Code) (closed : ClosedValue saved)
      (scope : Scope) (tail : Stack) :
      RawStep ⟨saved, scope, .push (.armed action) tail⟩
        ⟨.app action.action .unit, .none, .push (.running action saved closed) tail⟩ [] []
  | finishCleanup (action : ActionData) (saved : Code) (closed : ClosedValue saved)
      (scope : Scope) (tail : Stack) :
      RawStep ⟨.unit, scope, .push (.running action saved closed) tail⟩
        ⟨saved, action.scope, tail⟩ [] [.cleanup action.identity]
  | capture (requested : Instance) (operation parameter binder ticket : Nat)
      (operand body : Code) (scope : Scope) (whole cap tail : Stack) (handler : HandlerData)
      (operationResult : Ty) (selection : HandlerCut requested whole cap tail handler)
      (clause : ClauseAt operation handler.clauses parameter binder body)
      (closed : ClosedValue operand) (environmentReady : ClosedExcept parameter body) :
      RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder ticket,
          .live ticket operationResult handler.answer cap handler.scope tail⟩ [.ticket ticket] []
  | resume (binder ticket : Nat) (scope callerScope : Scope) (q a : Ty) (front cap tail : Stack)
      (value : Code) (closed : ClosedValue value) (resolve : scope.resolve binder = some ticket) :
      RawStep ⟨.resume binder value, scope, front.append (.live ticket q a cap callerScope tail)⟩
        ⟨value, scope, cap.append (front.append (.spent ticket a callerScope tail))⟩ [] [.ticket ticket]
  | discard (binder ticket closeId : Nat) (scope callerScope : Scope) (q a : Ty)
      (front cap tail : Stack) (plan : List CloseEntry) (resolve : scope.resolve binder = some ticket)
      (build : makePlan cap = some plan) :
      RawStep ⟨.discard binder, scope, front.append (.live ticket q a cap callerScope tail)⟩
        ⟨.unit, scope, (closeControl scope plan).append
          (.push (.closing closeId scope) (front.append (.spent ticket a callerScope tail)))⟩
        [.close closeId] [.ticket ticket]
  | leaveClause (ticket : Nat) (answer : Ty) (value : Code) (closed : ClosedValue value)
      (scope callerScope : Scope) (tail : Stack) :
      RawStep ⟨value, scope, .spent ticket answer callerScope tail⟩ ⟨value, callerScope, tail⟩ [] []
  | finishClose (identity : Nat) (scope callerScope : Scope) (tail : Stack) :
      RawStep ⟨.unit, scope, .push (.closing identity callerScope) tail⟩
        ⟨.unit, callerScope, tail⟩ [] [.close identity]
  | retire (ticket : Nat) (scope : Scope) (tail : Stack) :
      RawStep ⟨.unit, scope, .push (.retiring ticket) tail⟩ ⟨.unit, scope, tail⟩ [] [.ticket ticket]
  | readCell (identity : Nat) (payload : Int) (scope : Scope) (before after : Stack)
      (selected : CellUpdate identity payload payload before after) :
      RawStep ⟨.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before⟩
        ⟨.integer payload, scope, after⟩ [] []
  | writeCell (identity : Nat) (old new : Int) (scope : Scope) (before after : Stack)
      (selected : CellUpdate identity old new before after) :
      RawStep ⟨.perform (freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before⟩
        ⟨.unit, scope, after⟩ [] []

theorem raw_step_erases (step : RawStep before after created discharged) :
    Flow before.stack.erase after.stack.erase created discharged := by
  cases step with
  | focus plain step tail => exact .enter plain.erase tail.erase trivial
  | plug plain value closed scope tail => exact .leavePlain plain.erase tail.erase rfl
  | bind | beta | ifTrue | ifFalse => exact .stay _
  | enterHandler handler body tail => exact .enter handler.erase tail.erase trivial
  | leaveHandler handler value closed scope tail => exact .leavePlain handler.erase tail.erase rfl
  | enterCell binder identity payload body scope answer tail instantiationReady =>
      exact .enter (ExecFrame.erase (.cell identity payload scope answer)) tail.erase trivial
  | leaveCell identity payload answer savedScope scope value closed tail =>
      exact .release (ExecFrame.erase (.cell identity payload savedScope answer)) identity tail.erase rfl
  | enterCleanup action body tail => exact .enter action.erase tail.erase trivial
  | startCleanup action saved closed scope tail =>
      exact .startAction action.erase action.identity tail.erase (resourceDependencies saved.dependencies) rfl
  | finishCleanup action saved closed scope tail =>
      exact .finishAction (ExecFrame.erase (.running action saved closed)) action.identity tail.erase rfl
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler
      operationResult selection clause closed environmentReady =>
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

/-- A resource-closed entry with an integer initializer has an actual fresh
    successor. The constructed state retains resource-name closure and the
    existing ownership ledger; type/usage/support preservation is not assumed
    or concluded by this bounded progress case. -/
theorem resource_entry_progress (binder : Nat) (payload : Int) (body : Code)
    (scope : Scope) (answer : Ty) (tail : Stack) (issued completed : List Owner)
    (ready : (Code.resource binder (.integer payload) body).ResourceClosed)
    (ledger : Ledger (RunState.erase ⟨⟨.resource binder (.integer payload) body, scope, tail⟩, issued, completed⟩)) :
    ∃ identity, Owner.resource identity ∉ issued ∧
      RunStep ⟨⟨.resource binder (.integer payload) body, scope, tail⟩, issued, completed⟩
        ⟨⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩,
          issued ++ [.resource identity], completed⟩ ∧
      (body.instantiate (Environment.empty.bind binder identity)).ResourceClosed ∧
      Ledger (RunState.erase
        ⟨⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩,
          issued ++ [.resource identity], completed⟩) := by
  let prepared := prepareActivation issued
  have step := RunStep.event
    ⟨⟨.resource binder (.integer payload) body, scope, tail⟩, issued, completed⟩
    ⟨body.instantiate (Environment.empty.bind binder prepared.identity), scope, .push (.cell prepared.identity payload scope answer) tail⟩
    [.resource prepared.identity] [] (.enterCell binder prepared.identity payload body scope answer tail ready)
    (prepared_activation_fresh_history prepared ledger.2)
  exact ⟨prepared.identity, prepared.fresh, step, acquisition_closes_body Environment.empty prepared ready,
    run_step_preserves_ledger step ledger⟩

namespace Examples

def acquisition : Code := .resource 4 (.integer 0) .unit
def function : Code := .lambda 2 acquisition
def calls : Code := .bind 1 (.app (.variable 0) .unit) (.app (.variable 0) .unit)
def program : Code := .bind 0 function calls
def call : Code := .app function .unit
def suffix : PlainData := ⟨.bind 1 call, .none, .unit, .unit, [], rfl⟩
def initial : RunState := ⟨⟨program, .none, .nil⟩, [], []⟩
def terminal : RunState := ⟨⟨.unit, .none, .nil⟩, [.resource 0, .resource 1], [.resource 1, .resource 0]⟩

theorem unit_closed : ClosedValue .unit := ⟨trivial, rfl, by intro _ present; cases present⟩
theorem function_closed : ClosedValue function := ⟨trivial, rfl, by intro _ present; cases present⟩
theorem program_resource_closed : program.ResourceClosed := rfl

/-- Two calls execute the same retained lambda template. Source slot 4 does
    not enter ownership history: acquisition creates keys 0 and 1 instead. -/
theorem repeated_call_trace :
    RawTrace initial.configuration terminal.configuration [.resource 0, .resource 1] [.resource 1, .resource 0] := by
  have e0 := RawStep.bind 0 function calls .none Stack.nil function_closed
    (by simp [ClosedExcept, calls, Code.dependencies, Syntax.without])
  have e1 := RawStep.focus suffix (Focus.bind (initializer := call) (by simp [call, Code.IsValue])) Stack.nil
  have e2 := RawStep.beta 2 acquisition .unit .none (.push (.plain suffix) .nil) unit_closed function_closed
  have e3 := RawStep.enterCell 4 0 0 .unit .none .unit (.push (.plain suffix) .nil) rfl
  have e4 := RawStep.leaveCell 0 0 .unit .none .none .unit unit_closed (.push (.plain suffix) .nil)
  have e5 := RawStep.plug suffix .unit unit_closed .none Stack.nil
  have e6 := RawStep.bind 1 .unit call .none Stack.nil unit_closed
    (by simp [ClosedExcept, call, function, acquisition, Code.dependencies, Syntax.without])
  have e7 := RawStep.beta 2 acquisition .unit .none Stack.nil unit_closed function_closed
  have e8 := RawStep.enterCell 4 1 0 .unit .none .unit Stack.nil rfl
  have e9 := RawStep.leaveCell 1 0 .unit .none .none .unit unit_closed Stack.nil
  exact .next e0 (.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.next e7 (.next e8 (.next e9 (.refl _))))))))))

theorem repeated_call_execution : RunSteps initial terminal :=
  raw_trace_enacts repeated_call_trace (issued := []) (completed := []) (by decide)

theorem repeated_calls_preserve_ledger : Ledger terminal.erase :=
  run_steps_preserve_ledger repeated_call_execution ⟨.refl _, by decide⟩

theorem repeated_calls_complete_distinct_activations :
    RunSteps initial terminal ∧ terminal.configuration.expression.IsValue ∧ terminal.configuration.stack = .nil ∧
    terminal.issued = [.resource 0, .resource 1] ∧ terminal.completed = [.resource 1, .resource 0] ∧
    terminal.completed.Nodup ∧ Owner.resource 4 ∉ terminal.issued :=
  ⟨repeated_call_execution, trivial, rfl, rfl, rfl, ledger_no_double_completion repeated_calls_preserve_ledger, by decide⟩

/-- An equal source-slot numeral cannot hide an older runtime activation. -/
theorem activation_dependency_survives_equal_binder :
    (Code.resource 4 (.integer 0) (.resourceRef (.activation 4))).dependencies = [.resource 4] := rfl

end Examples

end Ash.OneShot.ScopedExecution

#print axioms Ash.OneShot.ScopedExecution.raw_step_erases
#print axioms Ash.OneShot.ScopedExecution.run_steps_preserve_ledger
#print axioms Ash.OneShot.ScopedExecution.run_no_double_completion
#print axioms Ash.OneShot.ScopedExpressions.Code.subst_resource_closed
#print axioms Ash.OneShot.ScopedExecution.resource_entry_progress
#print axioms Ash.OneShot.ScopedExecution.Examples.repeated_calls_complete_distinct_activations
#print axioms Ash.OneShot.ScopedExecution.Examples.activation_dependency_survives_equal_binder
