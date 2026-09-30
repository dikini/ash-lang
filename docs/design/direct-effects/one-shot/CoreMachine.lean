import CoreSyntax

/-! Independent graph-based successful Core evaluator for TASK-0032.
The transition definition does not use Code evaluation, calculus admission,
Event or a preserving calculus successor. Lists store the next inner frame
first, reversing Rust's vector orientation. Tuple locations address a finite
heap; scoped cell payloads remain owned by boundary frames, as in Rust.

This mathematical model has unbounded identities/storage. Each successful
transition models completion of all relevant preparation and disposal checks,
including checks during mutation; initial preflight alone is insufficient for
Rust discard. Failed or unsupported cases are not Step transitions. This batch
covers strict ordinary constructs, the singleton nonrecursive function-template
entry wrapper, cells, handlers, one-shot capture/resume/discard and cleanup.
Static metadata authentication, successful Rust preparation correspondence and
calculus simulation remain separate obligations. -/
namespace Ash.OneShot.CoreMachine
open CoreSyntax

mutual
inductive Value where
  | unit
  | boolean : Bool → Value
  | integer : Int → Value
  | handle : Nat → Value
  | location : Nat → Value
  | closure : Nat → NodeRef → Environment → Value
  deriving Repr

inductive Environment where
  | empty
  | binding : Nat → Value → Environment → Environment
  | resource : Nat → Nat → Environment → Environment
  | functionTemplate : Nat → Nat → NodeRef → Environment → Environment
  deriving Repr
end

/-- A template lookup captures this finite environment suffix, including the
    template itself. It does not create a cyclic heap alias or store a closure
    with a back edge. This mirrors Rust's RecursiveMemberKind::Function path. -/
def Environment.lookup : Environment → Nat → Option Value
  | .empty, _ => none
  | .binding binder value rest, name => if name == binder then some value else rest.lookup name
  | .resource _ _ rest, name => rest.lookup name
  | environment@(.functionTemplate binder parameter body rest), name =>
      if name == binder then some (.closure parameter body environment) else rest.lookup name

def Environment.resourceKey : Environment → Nat → Option Nat
  | .empty, _ => none
  | .binding _ _ rest, name | .functionTemplate _ _ _ rest, name => rest.resourceKey name
  | .resource binder key rest, name => if name == binder then some key else rest.resourceKey name

def Environment.instantiation (environment : Environment) : Instantiation.Environment :=
  environment.resourceKey

inductive HeapCell where
  | pair : Value → Value → HeapCell
  deriving Repr

abbrev Heap := List HeapCell

inductive Frame where
  | bind : Nat → NodeRef → Environment → Frame
  | applyFunction : NodeRef → Environment → Frame
  | applyArgument : Value → Frame
  | tupleLeft : NodeRef → Environment → Frame
  | tupleRight : Value → Frame
  | matchCases : List MatchArm → Environment → Frame
  | resourceInitializer : NodeRef → Nat → Binder → NodeRef → Environment → Frame
  | resourceBoundary : NodeRef → Nat → Int → Frame
  | request : Instantiation.Effect → Nat → Environment → Frame
  | handlerBoundary : NodeRef → Environment → Nat → Frame
  | resume : Nat → Nat → Frame
  | clauseBoundary : Nat → Nat → Nat → Nat → Option (List Frame) → Frame
  | cleanupBoundary : NodeRef → Environment → Nat → Frame
  | cleanupCompletion : Nat → Value → Frame
  | closeCompletion : Nat → Frame
  deriving Repr

inductive Control where
  | evaluate : NodeRef → Environment → Control
  | returned : Value → Control
  | discard : Nat → Nat → Control
  deriving Repr

/-- Model observations include node-entry and ghost ownership events. Rust's
    loop entry trace includes cleanup registration before it bypasses dispatch_entry;
    its separate EffectTrace has no model ghost identities. Dynamic keys distinguish
    repeated resource occurrences; handler, owner, cleanup and close counters
    are separate. -/
inductive Observation where
  | entered : NodeRef → Observation
  | acquired : NodeRef → Nat → Observation
  | read : Nat → Int → Observation
  | written : Nat → Int → Observation
  | released : Nat → Observation
  | handlerEntered : NodeRef → Nat → Observation
  | captured : Nat → Nat → Observation
  | resumed : Nat → Observation
  | discarded : Nat → Observation
  | clauseReturned : Nat → Observation
  | cleanupArmed : Nat → Observation
  | cleanupStarted : Nat → Observation
  | cleanupFinished : Nat → Observation
  | closeStarted : Nat → Observation
  | closeFinished : Nat → Observation
  | nestedConsumed : Nat → Observation
  deriving DecidableEq, Repr

structure State where
  control : Control
  frames : List Frame := []
  heap : Heap := []
  nextActivation : Nat := 0
  observations : List Observation := []
  nextHandler : Nat := 0
  nextOwner : Nat := 0
  nextCleanup : Nat := 0
  nextClose : Nat := 0
  deriving Repr

inductive Error where
  | missingNode : NodeRef → Error
  | missingVariable : Nat → Error
  | nonFunction
  | nonInteger
  | unsupportedNode : CoreSyntax.UnsupportedNode → Error
  | unsupportedTuple : Nat → Error
  | unsupportedMatch
  | unsupportedGlobalWrapper
  | recursiveInitializer
  | unboundResource : Nat → Error
  | unsupportedRequest : Instantiation.Effect → Nat → Error
  | invalidCellOperand
  | missingCell : Nat → Error
  | fuelExhausted
  | invalidHandler : NodeRef → Error
  | unhandledEffect : Instantiation.Effect → Nat → Error
  | missingClause : Nat → Error
  | unsupportedClausePattern
  | missingOwner : Nat → Nat → Error
  | consumedOwner : Nat → Nat → Error
  | liveClauseReturn : Nat → Nat → Error
  | runningCloseBlocked
  | cleanupCallback
  | cleanupResult
  | closeResult
  deriving DecidableEq, Repr

inductive Outcome where
  | stepped : State → Outcome
  | done : Value → Outcome
  | rejected : Error → Outcome
  deriving Repr

/-- Binder-aware raw-graph occurrence checking for the nonrecursive wrapper.
    The fuel bound is explicit and fails closed; no calculus dependency checker
    or initial-admission object supplies this fact. -/
def mentions (graph : Graph) : Nat → Nat → NodeRef → Except Error Bool
  | 0, _, _ => .error .fuelExhausted
  | fuel + 1, name, index => do
      let some node := graph.node index | throw (.missingNode index)
      match node.kind with
      | .variable binder => pure (name == binder)
      | .function binder body =>
          if name == binder.id then pure false else mentions graph fuel name body
      | .bind binder initializer body =>
          let left ← mentions graph fuel name initializer
          let right ← if name == binder.id then pure false else mentions graph fuel name body
          pure (left || right)
      | .resource _ handle initializer body =>
          let left ← mentions graph fuel name initializer
          let right ← if name == handle.id then pure false else mentions graph fuel name body
          pure (left || right)
      | .handler _ _ body clauses =>
          let head ← mentions graph fuel name body
          let tails ← clauses.mapM fun clause => match clause.argument with
            | .binder argument =>
                if name == argument.id then pure false else mentions graph fuel name clause.body
            | _ => throw .unsupportedMatch
          pure (head || tails.any id)
      | .recursiveBind _ _ => throw .unsupportedGlobalWrapper
      | _ =>
          let children ← node.kind.children.mapM (mentions graph fuel name)
          pure (children.any id)

/-- Matching is deliberately restricted to Unit and exact exhaustive Bool
    patterns. No wildcard or general-pattern fallback is synthesized. -/
def selectArm (arms : List MatchArm) (value : Value) : Except Error NodeRef :=
  match arms, value with
  | [⟨.unit, body⟩], .unit => .ok body
  | [⟨.boolean true, yes⟩, ⟨.boolean false, no⟩], .boolean condition
    | [⟨.boolean false, no⟩, ⟨.boolean true, yes⟩], .boolean condition =>
      .ok (if condition then yes else no)
  | _, _ => .error .unsupportedMatch

structure CellCut where
  inside : List Frame
  node : NodeRef
  key : Nat
  payload : Int
  outside : List Frame
  deriving Repr

inductive InterpreterCut where
  | cell : CellCut → InterpreterCut
  | handler : List Frame → NodeRef → Environment → Nat → List Frame → InterpreterCut
  deriving Repr

/-- Source and builtin interpreters share one nearest exact search. A matching
    source boundary prevents builtin fallback, including for cell operations. -/
def findInterpreter (graph : Graph) (effect : Instantiation.Effect) : List Frame → Except Error InterpreterCut
  | [] => .error (.unhandledEffect effect 0)
  | .resourceBoundary node key payload :: rest =>
      if effect == .cell (.activation key) then .ok (.cell ⟨[], node, key, payload, rest⟩)
      else do
        match ← findInterpreter graph effect rest with
        | .cell cut => pure (.cell { cut with inside := .resourceBoundary node key payload :: cut.inside })
        | .handler inside selected environment occurrence outside =>
            pure (.handler (.resourceBoundary node key payload :: inside) selected environment occurrence outside)
  | .handlerBoundary node environment occurrence :: rest => do
      let some declaration := graph.node node | throw (.invalidHandler node)
      match declaration.kind with
      | .handler _ handled _ _ =>
          if effect == handled.instantiate environment.instantiation then
            pure (.handler [] node environment occurrence rest)
          else
            match ← findInterpreter graph effect rest with
            | .cell cut => pure (.cell { cut with inside := .handlerBoundary node environment occurrence :: cut.inside })
            | .handler inside selected selectedEnvironment selectedOccurrence outside =>
                pure (.handler (.handlerBoundary node environment occurrence :: inside) selected selectedEnvironment selectedOccurrence outside)
      | _ => throw (.invalidHandler node)
  | frame :: rest => do
      match ← findInterpreter graph effect rest with
      | .cell cut => pure (.cell { cut with inside := frame :: cut.inside })
      | .handler inside node environment occurrence outside =>
          pure (.handler (frame :: inside) node environment occurrence outside)


def cellOperand (heap : Heap) (operation : Nat) (value : Value) : Except Error (Nat × Option Int) :=
  match operation, value with
  | 0, .handle key => .ok (key, none)
  | 1, .location location =>
      match heap[location]? with
      | some (.pair (.handle key) (.integer written)) => .ok (key, some written)
      | _ => .error .invalidCellOperand
  | _, _ => .error .invalidCellOperand
def interpretCell (state : State) (cut : CellCut) (operation : Nat) (value : Value) : Outcome :=
  match cellOperand state.heap operation value with
  | .error error => .rejected error
  | .ok (handle, written) =>
      if handle != cut.key then .rejected .invalidCellOperand
      else match written with
      | none => .stepped { state with
          control := .returned (.integer cut.payload)
          observations := state.observations ++ [.read cut.key cut.payload] }
      | some payload => .stepped { state with
          control := .returned .unit
          frames := cut.inside ++ .resourceBoundary cut.node cut.key payload :: cut.outside
          observations := state.observations ++ [.written cut.key payload] }

structure OwnerCut where
  inside : List Frame
  handler : Nat
  owner : Nat
  occurrence : Nat
  ticket : Nat
  capture : List Frame
  outside : List Frame
  deriving Repr

/-- A consumed nearest same-owner occurrence rejects immediately. It is never
    skipped to an older live activation of the same static clause owner. -/
def findOwner (handler owner : Nat) : List Frame → Except Error OwnerCut
  | [] => .error (.missingOwner handler owner)
  | .clauseBoundary candidate selected occurrence ticket capture :: rest =>
      if handler == candidate && owner == selected then
        match capture with
        | none => .error (.consumedOwner handler owner)
        | some saved => .ok ⟨[], candidate, selected, occurrence, ticket, saved, rest⟩
      else do
        let cut ← findOwner handler owner rest
        pure { cut with inside := .clauseBoundary candidate selected occurrence ticket capture :: cut.inside }
  | frame :: rest => do
      let cut ← findOwner handler owner rest
      pure { cut with inside := frame :: cut.inside }

mutual
/-- Explicit computational mass for nested captures; environments and values
    do not contribute to close traversal fuel. -/
def Frame.closeMass : Frame → Nat
  | .clauseBoundary _ _ _ _ (some capture) => framesMass capture + 1
  | _ => 1

def framesMass : List Frame → Nat
  | [] => 0
  | frame :: rest => frame.closeMass + framesMass rest
end

/-- Project captured ownership in structural inner-first order. Source
    handlers and ordinary suffix frames do not survive. Nested live captures
    contribute at their clause's exact position; running completion rejects. -/
def closeFuel : Nat → List Frame → Except Error (List Frame × List Observation)
  | 0, _ => .error .fuelExhausted
  | _ + 1, [] => .ok ([], [])
  | fuel + 1, frame :: rest => do
      match frame with
      | .cleanupCompletion _ _ | .closeCompletion _ => throw .runningCloseBlocked
      | .clauseBoundary _ _ _ ticket (some capture) =>
          let (nested, consumed) ← closeFuel fuel capture
          let (tail, after) ← closeFuel fuel rest
          pure (nested ++ tail, .nestedConsumed ticket :: consumed ++ after)
      | .resourceBoundary _ _ _ | .cleanupBoundary _ _ _ =>
          let (tail, consumed) ← closeFuel fuel rest
          pure (frame :: tail, consumed)
      | _ => closeFuel fuel rest

def returnResume (state : State) (handler owner : Nat) (value : Value) : Outcome :=
  match findOwner handler owner state.frames with
  | .error error => .rejected error
  | .ok cut => .stepped { state with
      control := .returned value
      frames := cut.capture ++ cut.inside ++
        .clauseBoundary cut.handler cut.owner cut.occurrence cut.ticket none :: cut.outside
      observations := state.observations ++ [.resumed cut.ticket] }

def discardOwner (state : State) (handler owner : Nat) : Outcome :=
  match findOwner handler owner state.frames with
  | .error error => .rejected error
  | .ok cut =>
      match closeFuel (framesMass cut.capture + 1) cut.capture with
      | .error error => .rejected error
      | .ok (closing, consumed) =>
          let remaining := cut.inside ++
            .clauseBoundary cut.handler cut.owner cut.occurrence cut.ticket none :: cut.outside
          if closing.isEmpty then .stepped { state with
              control := .returned .unit
              frames := remaining
              observations := state.observations ++ [.discarded cut.ticket] ++ consumed }
          else .stepped { state with
              control := .returned .unit
              frames := closing ++ .closeCompletion state.nextClose :: remaining
              nextClose := state.nextClose + 1
              observations := state.observations ++ [.discarded cut.ticket] ++ consumed ++ [.closeStarted state.nextClose] }

def request (graph : Graph) (state : State) (effect : Instantiation.Effect) (operation : Nat)
    (environment : Environment) (value : Value) : Outcome :=
  let requested := effect.instantiate environment.instantiation
  match requested with
  | .cell (.bound name) => .rejected (.unboundResource name)
  | _ => match findInterpreter graph requested state.frames with
    | .error (.unhandledEffect _ _) => .rejected (.unhandledEffect requested operation)
    | .error error => .rejected error
    | .ok (.cell cut) => interpretCell state cut operation value
    | .ok (.handler inside node handlerEnvironment occurrence outside) =>
        match graph.node node with
        | some ⟨_, _, _, _, .handler handler _ _ clauses⟩ =>
            match clauses.find? (fun clause => clause.operation == operation) with
            | none => .rejected (.missingClause operation)
            | some clause => match clause.argument with
                | .binder argument =>
                    let captured := inside ++ [.handlerBoundary node handlerEnvironment occurrence]
                    .stepped { state with
                      control := .evaluate clause.body (.binding argument.id value handlerEnvironment)
                      frames := .clauseBoundary handler clause.owner occurrence state.nextOwner (some captured) :: outside
                      nextOwner := state.nextOwner + 1
                      observations := state.observations ++ [.captured occurrence state.nextOwner] }
                | _ => .rejected .unsupportedClausePattern
        | _ => .rejected (.invalidHandler node)

/-- This is the independent successful evaluator function. Its error branch
    gives no transition and is never a preservation/progress escape hatch. -/
def next (graph : Graph) (state : State) : Outcome :=
  match state.control with
  | .discard handler owner => discardOwner state handler owner
  | .evaluate index environment =>
      match graph.node index with
      | none => .rejected (.missingNode index)
      | some node =>
          let entered : State := { state with observations := state.observations ++ [.entered index] }
          match node.kind with
          | .unit => .stepped { entered with control := .returned .unit }
          | .boolean value => .stepped { entered with control := .returned (.boolean value) }
          | .integer value => .stepped { entered with control := .returned (.integer value) }
          | .variable name => match environment.lookup name with
              | none => .rejected (.missingVariable name)
              | some value => .stepped { entered with control := .returned value }
          | .function binder body =>
              .stepped { entered with control := .returned (.closure binder.id body environment) }
          | .bind binder initializer body => .stepped { entered with
              control := .evaluate initializer environment
              frames := .bind binder.id body environment :: state.frames }
          | .apply function argument => .stepped { entered with
              control := .evaluate function environment
              frames := .applyFunction argument environment :: state.frames }
          | .tuple [left, right] => .stepped { entered with
              control := .evaluate left environment
              frames := .tupleLeft right environment :: state.frames }
          | .tuple elements => .rejected (.unsupportedTuple elements.length)
          | .matchCases scrutinee arms => .stepped { entered with
              control := .evaluate scrutinee environment
              frames := .matchCases arms environment :: state.frames }
          | .resource identity handle initializer body => .stepped { entered with
              control := .evaluate initializer environment
              frames := .resourceInitializer index identity handle body environment :: state.frames }
          | .request effect operation operand => .stepped { entered with
              control := .evaluate operand environment
              frames := .request effect operation environment :: state.frames }
          | .recursiveBind [member] body =>
              match graph.node member.initializer with
              | some ⟨_, _, _, _, .function parameter functionBody⟩ =>
                  match mentions graph (graph.nodes.length + 1) member.binder.id member.initializer with
                  | .error error => .rejected error
                  | .ok true => .rejected .recursiveInitializer
                  | .ok false => .stepped { entered with control := .evaluate body (.functionTemplate member.binder.id parameter.id functionBody environment) }
              | _ => .rejected .unsupportedGlobalWrapper
          | .recursiveBind _ _ => .rejected .unsupportedGlobalWrapper
          | .handler _ _ body _ => .stepped { entered with
              control := .evaluate body environment
              frames := .handlerBoundary index environment state.nextHandler :: state.frames
              nextHandler := state.nextHandler + 1
              observations := entered.observations ++ [.handlerEntered index state.nextHandler] }
          | .resume handler owner _ operand => .stepped { entered with
              control := .evaluate operand environment
              frames := .resume handler owner :: state.frames }
          | .discard handler owner _ => .stepped { entered with control := .discard handler owner }
          | .cleanup callback action body =>
              match environment.lookup callback.id with
              | some (.closure _ _ _) => .stepped { entered with
                  control := .evaluate body environment
                  frames := .cleanupBoundary action environment state.nextCleanup :: state.frames
                  nextCleanup := state.nextCleanup + 1
                  observations := entered.observations ++ [.cleanupArmed state.nextCleanup] }
              | _ => .rejected .cleanupCallback
          | .unsupported kind => .rejected (.unsupportedNode kind)
  | .returned value =>
      match state.frames with
      | [] => .done value
      | frame :: rest =>
          let popped : State := { state with frames := rest }
          match frame with
          | .bind binder body environment => .stepped { popped with
              control := .evaluate body (.binding binder value environment) }
          | .applyFunction argument environment => .stepped { popped with
              control := .evaluate argument environment
              frames := .applyArgument value :: rest }
          | .applyArgument function => match function with
              | .closure parameter body environment => .stepped { popped with
                  control := .evaluate body (.binding parameter value environment) }
              | _ => .rejected .nonFunction
          | .tupleLeft right environment => .stepped { popped with
              control := .evaluate right environment
              frames := .tupleRight value :: rest }
          | .tupleRight left => .stepped { popped with
              control := .returned (.location state.heap.length)
              heap := state.heap ++ [.pair left value] }
          | .matchCases arms environment => match selectArm arms value with
              | .error error => .rejected error
              | .ok body => .stepped { popped with control := .evaluate body environment }
          | .resourceInitializer index identity handle body environment => match value with
              | .integer payload =>
                  let key := state.nextActivation
                  let acquired := .binding handle.id (.handle key) (.resource identity key environment)
                  .stepped { popped with
                      control := .evaluate body acquired
                      frames := .resourceBoundary index key payload :: rest
                      nextActivation := key + 1
                      observations := state.observations ++ [.acquired index key] }
              | _ => .rejected .nonInteger
          | .resourceBoundary _ key _ => .stepped { popped with
              control := .returned value
              observations := state.observations ++ [.released key] }
          | .request effect operation environment => request graph popped effect operation environment value
          | .handlerBoundary _ _ _ => .stepped { popped with control := .returned value }
          | .resume handler owner => returnResume popped handler owner value
          | .clauseBoundary handler owner _ ticket capture =>
              match capture with
              | some _ => .rejected (.liveClauseReturn handler owner)
              | none => .stepped { popped with
                  control := .returned value
                  observations := state.observations ++ [.clauseReturned ticket] }
          | .cleanupBoundary action environment key => .stepped { popped with
              control := .evaluate action environment
              frames := .cleanupCompletion key value :: rest
              observations := state.observations ++ [.cleanupStarted key] }
          | .cleanupCompletion key saved => match value with
              | .unit => .stepped { popped with
                  control := .returned saved
                  observations := state.observations ++ [.cleanupFinished key] }
              | _ => .rejected .cleanupResult
          | .closeCompletion key => match value with
              | .unit => .stepped { popped with
                  control := .returned .unit
                  observations := state.observations ++ [.closeFinished key] }
              | _ => .rejected .closeResult

/-- The source transition is defined only from this evaluator's own result. -/
def Step (graph : Graph) (before after : State) : Prop := next graph before = .stepped after

/-- Rejected evaluation cannot be counted as a successful source step. -/
theorem rejected_not_step (graph : Graph) (before : State) (error : Error)
    (rejected : next graph before = .rejected error) (after : State) :
    ¬ Step graph before after := by
  unfold Step
  rw [rejected]
  intro impossible
  cases impossible

/-- Terminal observation likewise is not a computational transition. -/
theorem done_not_step (graph : Graph) (before : State) (value : Value)
    (terminal : next graph before = .done value) (after : State) :
    ¬ Step graph before after := by
  unfold Step
  rw [terminal]
  intro impossible
  cases impossible

inductive RunResult where
  | done : Value → State → RunResult
  | stopped : Error → State → RunResult
  | exhausted : State → RunResult
  deriving Repr

/-- A bounded runner exposes unsupported families and exhaustion distinctly. -/
def run (graph : Graph) : Nat → State → RunResult
  | 0, state => .exhausted state
  | fuel + 1, state => match next graph state with
      | .stepped successor => run graph fuel successor
      | .done value => .done value state
      | .rejected error => .stopped error state

def initial (graph : Graph) : State := { control := .evaluate graph.root .empty }

end Ash.OneShot.CoreMachine
