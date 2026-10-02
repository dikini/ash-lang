import CoreCallableRunningLocalHandler
import CoreCallableCleanupActivation
namespace Ash.OneShot.CoreCallableGeneratedChronology
open CoreSyntax CoreTranslation CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableGeneralHistory CoreCallableCallerBarriers CoreCallableRunningOccurrence
open CoreCallableRunningCapture CoreCallableSiteLineage CoreCaptureEntry CoreRequestFrames

/-- A current evaluator endpoint separates strict administrative maps from the
full lexical history. All fields describe this endpoint, never a future state. -/
structure Endpoint (graph : Graph) where
  state : CoreMachine.State
  focus : Configuration
  owners : OwnerMap
  maps : List MappedFrame
  physical : List CoreMachine.Frame
  lexical : Stack
  history : GeneralHistory graph state.heap physical lexical
  frames : state.frames = framesOf maps ++ physical

noncomputable def Endpoint.point (current : Endpoint graph) : CoreUnwindRelation.Point :=
  ⟨current.state,.eval (CoreCleanupRunFrames.attach current.focus current.lexical),current.owners,current.maps⟩

/-- Positive matching or one of the existing permitted administrative families
with a strict decrease. No unrestricted target stuttering constructor exists. -/
inductive Matching (graph : Graph) (before after : Endpoint graph)
    : List Owner → List Owner → Prop where
  | positive (step : CoreUnwindRelation.Positive before.point.machine after.point.machine created discharged) :
      Matching graph before after created discharged
  | administrative (same : before.point.machine = after.point.machine)
      (permitted : CoreAdministrativeSteps.ready graph before.state = true ∨
        CoreStrictPotential.traversalReady graph before.state = true)
      (decreasing : CoreStrictPotential.potential graph after.state < CoreStrictPotential.potential graph before.state) :
      Matching graph before after [] []

/-- Only operation producers construct these results; generated executions
below accept named operations and their current inputs, never a Result. -/
structure Result (before : Endpoint graph) (created discharged : List Owner) where
  after : Endpoint graph
  core : CoreMachine.next graph before.state = .stepped after.state
  matching : Matching graph before after created discharged

private theorem heap_refl (heap : CoreMachine.Heap) : HeapExtends heap heap := fun _ _ h => h

private theorem raw_positive (step : RawStep before after created discharged) (allowed : LexicalUnwind.ordinary before.expression) :
    CoreUnwindRelation.Positive (.eval before) (.eval after) created discharged :=
  .one (.evaluate step allowed)

private theorem value_ordinary {code : Code} (value : ClosedValue code) : LexicalUnwind.ordinary code := by
  have closed := value.1
  cases code <;> simp_all [LexicalUnwind.ordinary,Code.IsValue]

/-- The current component contains no independently chosen lexical suffix. -/
structure EmptyFocus (current : Endpoint graph) (code : Code) (scope : Execution.Scope) : Prop where
  maps : current.maps = []
  focus : current.focus = ⟨code,scope,.nil⟩

private theorem empty_frames (empty : EmptyFocus current code scope) : current.state.frames = current.physical := by
  simpa only [empty.maps,framesOf,List.map_nil,List.nil_append] using current.frames

private theorem empty_point (empty : EmptyFocus current code scope) :
    current.point.machine = .eval ⟨code,scope,current.lexical⟩ := by
  simp only [Endpoint.point,empty.focus,CoreCleanupRunFrames.attach,Stack.append]

/-- Root endpoints are constructed from the SAME immutable actual start.
The initial outside history is the start's original history, weakened reflexively. -/
noncomputable def started
    (start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget) :
    Endpoint graph := {
  state := startedState start.predecessor action environment data.identity savedValue originalPhysical
  focus := ⟨.app data.action .unit,.none,.nil⟩
  owners := cleanupOwners
  maps := []
  physical := .cleanupCompletion data.identity savedValue :: originalPhysical
  lexical := .push (.running data savedCode start.saved.closed) originalTarget
  history := by
    have completion := GeneralHistory.append (.running start.running) start.originalHistory
    simpa only [startedState,Stack.append,List.singleton_append] using completion
  frames := rfl }

noncomputable def start_before
    (start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget) :
    Endpoint graph := {
  state := returnedState start.predecessor savedValue (.cleanupBoundary action environment data.identity :: originalPhysical)
  focus := ⟨savedCode,start.scope,.nil⟩
  owners := start.callerOwners, maps := []
  physical := .cleanupBoundary action environment data.identity :: originalPhysical
  lexical := .push (.armed data) originalTarget
  history := .push (.cleanup start.installed.delayed) (by trivial) start.originalHistory
  frames := rfl }

structure BindInput (current : Endpoint graph) where
  owners : OwnerMap
  ownersSame : current.owners = owners
  binder : Binder
  body : Nat
  environment : Environment
  plain : PlainData
  past : CallerBindPast graph owners binder body environment plain current.physical current.lexical
  predecessor : past.predecessor = current.state
  original : HEq past.originalHistory current.history
  control : current.state.control = .evaluate past.site environment
  empty : EmptyFocus current (.bind binder.id past.contextCode past.suffixCode) plain.scope

noncomputable def bind_result {graph : Graph} {current : Endpoint graph} (input : BindInput current) : Result current [] [] := by
  have extension : HeapExtends input.past.predecessor.heap current.state.heap := by
    rw [input.predecessor]; exact heap_refl _
  let history := GeneralHistory.push (.ordinary (input.past.saved.saved.related.heap_weaken extension))
    (by trivial) current.history
  let after : Endpoint graph := {
    state := { current.state with
      control := .evaluate input.past.initializer input.environment
      frames := .bind input.binder.id input.body input.environment :: current.physical
      observations := current.state.observations ++ [.entered input.past.site]}
    focus := ⟨input.past.contextCode,input.plain.scope,.nil⟩
    owners := input.owners,maps := []
    physical := .bind input.binder.id input.body input.environment :: current.physical
    lexical := .push (.plain input.plain) current.lexical
    history := history,frames := rfl }
  have core := input.past.actual
  rw [input.predecessor] at core
  have beforeSame : { current.state with
      control := .evaluate input.past.site input.environment
      frames := current.physical} = current.state := by rw [← input.control,← empty_frames input.empty]
  rw [beforeSame] at core
  refine ⟨after,core,.positive ?_⟩
  rw [empty_point input.empty]
  exact raw_positive input.past.focus (by trivial)

structure HandlerInput (current : Endpoint graph) where
  owners : OwnerMap
  ownersSame : current.owners = owners
  site : Nat
  environment : Environment
  data : HandlerData
  installation : GeneralHandlerPast graph owners site environment data
  predecessor : installation.predecessor = current.state
  suffix : installation.originalSuffix = current.physical
  code : Code
  raw : Code
  rawClauses : Clauses
  fuel : Nat
  translated : translateFuel graph fuel owners installation.body = .ok raw
  siteTranslated : translateFuel graph (fuel + 1) owners site = .ok (.handle installation.effect raw rawClauses)
  lexical : EnvCloses graph owners current.state.heap environment
    (.handle installation.effect raw rawClauses) (.handle (Instantiation.freezeEffect data.effectInst) code data.clauses)
  -- Exact current Core control and target component are threaded from execution.
  control : current.state.control = .evaluate site environment
  empty : EmptyFocus current (.handle (Instantiation.freezeEffect data.effectInst) code data.clauses) data.scope

noncomputable def handler_result {graph : Graph} {current : Endpoint graph} (input : HandlerInput current) : Result current [] [] := by
  have extension : HeapExtends input.installation.predecessor.heap current.state.heap := by
    rw [input.predecessor]; exact heap_refl _
  let header := input.installation.header.heap_weaken extension
  let after : Endpoint graph := {
    state := { current.state with
      control := .evaluate input.installation.body input.environment
      frames := .handlerBoundary input.site input.environment input.data.activation :: current.physical
      nextHandler := current.state.nextHandler + 1
      observations := current.state.observations ++ [.entered input.site,.handlerEntered input.site input.data.activation]}
    focus := ⟨input.code,input.data.scope,.nil⟩
    owners := input.owners,maps := []
    physical := .handlerBoundary input.site input.environment input.data.activation :: current.physical
    lexical := .push (.handler input.data) current.lexical
    history := .handler input.installation header current.history,frames := rfl }
  have core := input.installation.actual
  rw [input.predecessor,input.suffix] at core
  have beforeSame : { current.state with
      control := .evaluate input.site input.environment
      frames := current.physical} = current.state := by rw [← input.control,← empty_frames input.empty]
  rw [beforeSame] at core
  refine ⟨after,core,.positive ?_⟩
  rw [empty_point input.empty]
  exact raw_positive (.enterHandler input.data input.code current.lexical) (by trivial)


structure BetaInput (current : Endpoint graph) where
  frameOwners : OwnerMap
  parameter : Nat
  body : Nat
  environment : Environment
  value : CoreMachine.Value
  argument : Code
  bodyCode : Code
  scope : Execution.Scope
  function : ValueRel graph current.owners current.state.heap (.closure parameter body environment) (.lambda parameter bodyCode)
  operand : ValueRel graph current.owners current.state.heap value argument
  control : current.state.control = .returned value
  maps : current.maps = [(frameOwners,.applyArgument (.closure parameter body environment))]
  focus : current.focus = ⟨.app (.lambda parameter bodyCode) argument,scope,.nil⟩

noncomputable def beta_result {graph : Graph} {current : Endpoint graph} (input : BetaInput current) : Result current [] [] := by
  let after : Endpoint graph := {
    state := { current.state with
      control := .evaluate input.body (.binding input.parameter input.value input.environment)
      frames := current.physical }
    focus := ⟨input.bodyCode.subst input.parameter input.argument,.none,.nil⟩
    owners := [],maps := [],physical := current.physical,lexical := current.lexical
    history := current.history,frames := rfl }
  have shape : current.state.frames = .applyArgument (.closure input.parameter input.body input.environment) :: current.physical := by
    simpa [input.maps,framesOf] using current.frames
  have beforeSame : { current.state with
      control := .returned input.value
      frames := .applyArgument (.closure input.parameter input.body input.environment) :: current.physical } = current.state := by
    rw [← input.control,← shape]
  have core : CoreMachine.next graph current.state = .stepped after.state := by
    obtain ⟨fuel,raw,translated,actual,rawStep,closed,value⟩ := CoreStrictSteps.application_complete
      input.function input.operand current.physical input.scope current.lexical
    rw [beforeSame] at actual
    exact actual
  refine ⟨after,core,.positive ?_⟩
  simpa only [Endpoint.point,input.focus,CoreCleanupRunFrames.attach,Stack.append,after] using
    raw_positive (.beta input.parameter input.bodyCode input.argument input.scope current.lexical
      input.operand.closed input.function.closed) (by trivial)

/-- Head bind completion consumes the original installed receipt and its exact
canonical suffix history. The suffix is not replaced with arbitrary history. -/
structure BindReturnInput (current : Endpoint graph) where
  owners : OwnerMap
  binder : Binder
  body : Nat
  environment : Environment
  plain : PlainData
  suffixPhysical : List CoreMachine.Frame
  suffixTarget : Stack
  past : CallerBindPast graph owners binder body environment plain suffixPhysical suffixTarget
  extension : HeapExtends past.predecessor.heap current.state.heap
  value : CoreMachine.Value
  code : Code
  scope : Execution.Scope
  operand : ValueRel graph current.owners current.state.heap value code
  control : current.state.control = .returned value
  empty : EmptyFocus current code scope
  physical : current.physical = .bind binder.id body environment :: suffixPhysical
  lexical : current.lexical = .push (.plain plain) suffixTarget
  sameHistory : HEq current.history (past.current_history extension)

noncomputable def bind_return_result {graph : Graph} {current : Endpoint graph} (input : BindReturnInput current) : Result current [] [] := by
  let after : Endpoint graph := {
    state := { current.state with
      control := .evaluate input.body (.binding input.binder.id input.value input.environment)
      frames := input.suffixPhysical }
    focus := ⟨input.past.suffixCode.subst input.binder.id input.code,input.plain.scope,.nil⟩
    owners := input.owners,maps := [],physical := input.suffixPhysical,lexical := input.suffixTarget
    history := input.past.originalHistory.heap_weaken input.extension,frames := rfl }
  have proof : CoreMachine.next graph current.state = .stepped after.state ∧
      CoreUnwindRelation.Positive current.point.machine after.point.machine [] [] := by
    obtain ⟨core,plug,reduce,site,origin,history⟩ := CoreCallableCallerBarriers.bind_return
      input.past input.extension input.operand input.scope
    have beforeSame : { current.state with
        control := .returned input.value
        frames := .bind input.binder.id input.body input.environment :: input.suffixPhysical } = current.state := by
      rw [← input.physical,← empty_frames input.empty,← input.control]
    rw [beforeSame] at core
    refine ⟨core,?_⟩
    rw [empty_point input.empty,input.lexical]
    exact .next (.evaluate plug (value_ordinary input.operand.closed))
      (raw_positive reduce (by trivial))
  exact ⟨after,proof.1,.positive proof.2⟩

structure HandlerReturnInput (current : Endpoint graph) where
  owners : OwnerMap
  site : Nat
  environment : Environment
  data : HandlerData
  installation : GeneralHandlerPast graph owners site environment data
  header : CoreEffectFrames.BoundaryRel graph owners current.state.heap
    (.handlerBoundary site environment data.activation) (.handler data)
  suffixPhysical : List CoreMachine.Frame
  suffixTarget : Stack
  suffix : GeneralHistory graph current.state.heap suffixPhysical suffixTarget
  value : CoreMachine.Value
  code : Code
  scope : Execution.Scope
  operand : ValueRel graph current.owners current.state.heap value code
  control : current.state.control = .returned value
  empty : EmptyFocus current code scope
  physical : current.physical = .handlerBoundary site environment data.activation :: suffixPhysical
  lexical : current.lexical = .push (.handler data) suffixTarget
  sameHistory : HEq current.history (GeneralHistory.handler installation header suffix)

noncomputable def handler_return_result {graph : Graph} {current : Endpoint graph} (input : HandlerReturnInput current) : Result current [] [] := by
  let after : Endpoint graph := {
    state := { current.state with frames := input.suffixPhysical }
    focus := ⟨input.code,input.data.scope,.nil⟩
    owners := input.owners,maps := [],physical := input.suffixPhysical,lexical := input.suffixTarget
    history := input.suffix,frames := rfl }
  have proof : CoreMachine.next graph current.state = .stepped after.state ∧
      CoreUnwindRelation.Positive current.point.machine after.point.machine [] [] := by
    obtain ⟨core,raw,saved⟩ := CoreEffectEntry.handler_leave input.header input.operand input.scope input.suffixPhysical input.suffixTarget
    have beforeSame : { current.state with
        control := .returned input.value
        frames := .handlerBoundary input.site input.environment input.data.activation :: input.suffixPhysical } = current.state := by
      rw [← input.physical,← empty_frames input.empty,← input.control]
    rw [beforeSame] at core
    refine ⟨?_,?_⟩
    · simpa only [after,← input.control] using core
    · rw [empty_point input.empty,input.lexical]
      exact raw_positive raw (value_ordinary input.operand.closed)
  exact ⟨after,proof.1,.positive proof.2⟩

/-- Current literal interpretation chooses a finite actual evaluator family.
Neither a next equation nor a matching witness is an input. -/
inductive Literal (current : Endpoint graph) (index : Nat) (environment : Environment) : Code → Type where
  | unit (known : graph.node index = some node) (kind : node.kind = .unit)
      (saved : EnvCloses graph current.owners current.state.heap environment .unit code) : Literal current index environment code
  | integer (known : graph.node index = some node) (kind : node.kind = .integer value)
      (saved : EnvCloses graph current.owners current.state.heap environment (.integer value) code) : Literal current index environment code
  | lexicalVariable (known : graph.node index = some node) (kind : node.kind = .variable name)
      (saved : EnvCloses graph current.owners current.state.heap environment (.variable name) code)
      (closed : ClosedValue code) : Literal current index environment code
  | lambda (known : graph.node index = some node) (kind : node.kind = .function parameter body)
      (translated : translateFuel graph fuel current.owners body = .ok rawBody)
      (callable : CallableCertificate graph parameter.id body rawBody)
      (saved : EnvCloses graph current.owners current.state.heap environment (.lambda parameter.id rawBody) code)
      (closed : ClosedValue code) : Literal current index environment code

structure LiteralInput (current : Endpoint graph) where
  index : Nat
  environment : Environment
  code : Code
  scope : Execution.Scope
  literal : Literal current index environment code
  control : current.state.control = .evaluate index environment
  stack : OrdinaryWithMaps graph current.state.heap current.maps code scope
    current.focus.expression current.focus.scope current.focus.stack

private theorem literal_produced {graph : Graph} {current : Endpoint graph} (input : LiteralInput current) :
    ∃ value, CoreAdministrativeSteps.ValueWitness graph current.owners
      current.state
      { current.state with
        control := .returned value
        observations := current.state.observations ++ [.entered input.index] } input.code := by
  have same : { current.state with
    control := .evaluate input.index input.environment
    frames := current.state.frames } = current.state := by rw [← input.control]
  cases input.literal with
  | unit known kind saved =>
    have actual := (CoreAdministrativeSteps.unit_evaluate (base := current.state) known kind saved current.state.frames).1
    rw [same] at actual
    exact ⟨.unit,actual⟩
  | integer known kind saved =>
    have actual := (CoreAdministrativeSteps.integer_evaluate (base := current.state) known kind saved current.state.frames).1
    rw [same] at actual
    exact ⟨_,actual⟩
  | lexicalVariable known kind saved closed =>
    obtain ⟨value,lookup,actual,translated⟩ := CoreAdministrativeSteps.variable_evaluate (base := current.state) known kind saved closed current.state.frames
    rw [same] at actual
    exact ⟨value,actual⟩
  | lambda known kind translated callable saved closed =>
    have actual := (CoreAdministrativeSteps.lambda_evaluate (base := current.state) known kind translated callable saved closed current.state.frames).1
    rw [same] at actual
    exact ⟨_,actual⟩

noncomputable def literal_result {graph : Graph} {current : Endpoint graph} (input : LiteralInput current) : Result current [] [] := by
  let value := Classical.choose (literal_produced input)
  have actual := Classical.choose_spec (literal_produced input)
  let after : Endpoint graph := {
    state := { current.state with
      control := .returned value
      observations := current.state.observations ++ [.entered input.index] }
    focus := current.focus,owners := current.owners,maps := current.maps
    physical := current.physical,lexical := current.lexical,history := current.history,frames := current.frames }
  exact ⟨after,actual.core,.administrative rfl (Or.inl actual.permitted)
    (CoreStrictPotential.administrative_potential actual)⟩


/-- These are literal evaluator traversal families, not supplied step proofs. -/
inductive EntryKind (node : CoreSyntax.Node) : Nat → CoreMachine.Frame → Type where
  | application (kind : node.kind = .apply function argument) :
      EntryKind node function (.applyFunction argument environment)
  | tuple (kind : node.kind = .tuple [left,right]) :
      EntryKind node left (.tupleLeft right environment)
  | request (kind : node.kind = .request effect operation operand) :
      EntryKind node operand (.request effect operation environment)
  | resume (kind : node.kind = .resume handler owner post operand) :
      EntryKind node operand (.resume handler owner)

structure EntryInput (current : Endpoint graph) where
  ordered : CoreTranslationFuel.Postorder graph
  site : Nat
  environment : Environment
  node : CoreSyntax.Node
  known : graph.node site = some node
  nextIndex : Nat
  frame : CoreMachine.Frame
  kind : EntryKind node nextIndex frame
  environmentSame : match frame with
    | .applyFunction _ saved | .tupleLeft _ saved | .request _ _ saved => saved = environment
    | _ => True
  control : current.state.control = .evaluate site environment
  maps : current.maps = []
  stack : current.focus.stack = .nil
  interpreted : ControlRel graph current.owners current.state.heap current.state.control current.focus.expression

private theorem entry_produced {graph : Graph} {current : Endpoint graph} (input : EntryInput current) :
    let nextState := { current.state with
      control := .evaluate input.nextIndex input.environment
      frames := input.frame :: current.physical
      observations := current.state.observations ++ [.entered input.site] }
    CoreMachine.next graph current.state = .stepped nextState ∧
    CoreStrictPotential.traversalReady graph current.state = true ∧
    CoreStrictPotential.potential graph nextState < CoreStrictPotential.potential graph current.state := by
  rcases input with ⟨ordered,site,environment,node,known,nextIndex,frame,kind,environmentSame,control,maps,stack,interpreted⟩
  have frames : current.state.frames = current.physical := by simpa [maps,framesOf] using current.frames
  have beforeSame : { current.state with
    control := .evaluate site environment
    frames := current.physical } = current.state := by rw [← control,← frames]
  cases kind with
  | application kind =>
    have same := environmentSame
    dsimp only at same
    obtain ⟨core,decreasing⟩ := CoreStrictPotential.application_entry_decreases (base := current.state)
      ordered known kind current.physical
    rw [beforeSame] at core decreasing
    exact ⟨by simpa only [same] using core,by simp [CoreStrictPotential.traversalReady,control,known,kind],by simpa only [same] using decreasing⟩
  | tuple kind =>
    have same := environmentSame
    dsimp only at same
    obtain ⟨core,decreasing⟩ := CoreStrictPotential.tuple_entry_decreases (base := current.state)
      ordered known kind current.physical
    rw [beforeSame] at core decreasing
    exact ⟨by simpa only [same] using core,by simp [CoreStrictPotential.traversalReady,control,known,kind],by simpa only [same] using decreasing⟩
  | request kind =>
    have same := environmentSame
    dsimp only at same
    obtain ⟨core,decreasing⟩ := CoreStrictPotential.request_entry_decreases (base := current.state)
      ordered known kind current.physical
    rw [beforeSame] at core decreasing
    exact ⟨by simpa only [same] using core,by simp [CoreStrictPotential.traversalReady,control,known,kind],by simpa only [same] using decreasing⟩
  | resume kind =>
    obtain ⟨core,decreasing⟩ := CoreStrictPotential.resume_entry_decreases (base := current.state)
      ordered known kind current.physical
    rw [beforeSame] at core decreasing
    exact ⟨core,by simp [CoreStrictPotential.traversalReady,control,known,kind],decreasing⟩

noncomputable def entry_result {graph : Graph} {current : Endpoint graph} (input : EntryInput current) : Result current [] [] := by
  let after : Endpoint graph := {
    state := { current.state with
      control := .evaluate input.nextIndex input.environment
      frames := input.frame :: current.physical
      observations := current.state.observations ++ [.entered input.site] }
    focus := current.focus,owners := current.owners,maps := [(current.owners,input.frame)]
    physical := current.physical,lexical := current.lexical,history := current.history,frames := rfl }
  have actual := entry_produced input
  exact ⟨after,actual.1,.administrative rfl (Or.inr actual.2.1) actual.2.2⟩

inductive SwapKind : CoreMachine.Frame → CoreMachine.Frame → Type where
  | application : SwapKind (.applyFunction argument environment) (.applyArgument value)
  | tuple : SwapKind (.tupleLeft right environment) (.tupleRight value)

structure SwapInput (current : Endpoint graph) where
  frameOwners : OwnerMap
  beforeFrame : CoreMachine.Frame
  afterFrame : CoreMachine.Frame
  kind : SwapKind beforeFrame afterFrame
  value : CoreMachine.Value
  nextIndex : Nat
  environment : Environment
  frameBefore : beforeFrame = .applyFunction nextIndex environment ∨ beforeFrame = .tupleLeft nextIndex environment
  frameAfter : afterFrame = .applyArgument value ∨ afterFrame = .tupleRight value
  -- The completed value and saved next operand describe the current whole target.
  code : Code
  related : ValueRel graph current.owners current.state.heap value code
  interpreted : ComponentMapped graph current.owners current.maps
    (CoreCleanupRunFrames.isolate current.state current.maps) current.focus
  control : current.state.control = .returned value
  maps : current.maps = [(frameOwners,beforeFrame)]

private theorem swap_produced {graph : Graph} {current : Endpoint graph} (input : SwapInput current) :
    let nextState := { current.state with
      control := .evaluate input.nextIndex input.environment
      frames := input.afterFrame :: current.physical }
    CoreMachine.next graph current.state = .stepped nextState ∧
    CoreStrictPotential.traversalReady graph current.state = true ∧
    CoreStrictPotential.potential graph nextState < CoreStrictPotential.potential graph current.state := by
  rcases input with ⟨frameOwners,beforeFrame,afterFrame,kind,value,nextIndex,environment,frameBefore,frameAfter,code,related,interpreted,control,maps⟩
  have frames : current.state.frames = beforeFrame :: current.physical := by simpa [maps,framesOf] using current.frames
  cases kind with
  | application =>
    obtain before | before := frameBefore
    · cases before
      obtain after | after := frameAfter
      · cases after
        have same : { current.state with
          control := .returned value
          frames := .applyFunction nextIndex environment :: current.physical } = current.state := by
          rw [← frames,← control]
        obtain ⟨core,decreasing⟩ := CoreStrictPotential.application_argument_decreases (graph := graph) current.state current.physical
        rw [same] at core decreasing
        exact ⟨core,by simp [CoreStrictPotential.traversalReady,control,frames],decreasing⟩
      · cases after
    · cases before
  | tuple =>
    obtain before | before := frameBefore
    · cases before
    · cases before
      obtain after | after := frameAfter
      · cases after
      · cases after
        have same : { current.state with
          control := .returned value
          frames := .tupleLeft nextIndex environment :: current.physical } = current.state := by
          rw [← frames,← control]
        obtain ⟨core,decreasing⟩ := CoreStrictPotential.tuple_right_decreases (graph := graph) current.state current.physical
        rw [same] at core decreasing
        exact ⟨core,by simp [CoreStrictPotential.traversalReady,control,frames],decreasing⟩

noncomputable def swap_result {graph : Graph} {current : Endpoint graph} (input : SwapInput current) : Result current [] [] := by
  let after : Endpoint graph := {
    state := { current.state with
      control := .evaluate input.nextIndex input.environment
      frames := input.afterFrame :: current.physical }
    focus := current.focus,owners := input.frameOwners,maps := [(input.frameOwners,input.afterFrame)]
    physical := current.physical,lexical := current.lexical,history := current.history,frames := rfl }
  have actual := swap_produced input
  exact ⟨after,actual.1,.administrative rfl (Or.inr actual.2.1) actual.2.2⟩

structure TupleInput (current : Endpoint graph) where
  frameOwners : OwnerMap
  left : CoreMachine.Value
  right : CoreMachine.Value
  leftCode : Code
  rightCode : Code
  leftRelated : ValueRel graph current.owners current.state.heap left leftCode
  rightRelated : ValueRel graph current.owners current.state.heap right rightCode
  control : current.state.control = .returned right
  maps : current.maps = [(frameOwners,.tupleRight left)]
  scope : Execution.Scope
  focus : current.focus = ⟨.pair leftCode rightCode,scope,.nil⟩

noncomputable def tuple_result {graph : Graph} {current : Endpoint graph} (input : TupleInput current) : Result current [] [] := by
  have extension := CoreValueRelation.heap_append current.state.heap [.pair input.left input.right]
  let after : Endpoint graph := {
    state := { current.state with
      control := .returned (.location current.state.heap.length)
      frames := current.physical
      heap := current.state.heap ++ [.pair input.left input.right] }
    focus := current.focus,owners := current.owners,maps := []
    physical := current.physical,lexical := current.lexical,history := current.history.heap_weaken extension,frames := rfl }
  have frames : current.state.frames = .tupleRight input.left :: current.physical := by simpa [input.maps,framesOf] using current.frames
  have same : { current.state with
    control := .returned input.right
    frames := .tupleRight input.left :: current.physical } = current.state := by rw [← frames,← input.control]
  have actual : CoreAdministrativeSteps.ValueWitness graph current.owners current.state after.state (.pair input.leftCode input.rightCode) := by
    have proof := (CoreAdministrativeSteps.tuple_allocate (base := current.state) input.leftRelated input.rightRelated current.physical).1
    rw [same] at proof
    exact proof
  exact ⟨after,actual.core,.administrative rfl (Or.inl actual.permitted)
    (CoreStrictPotential.administrative_potential actual)⟩


noncomputable def location (current : Endpoint graph) (index : Fin (handler_locations current.history).length) :=
  (handler_locations current.history)[index]

structure CaptureInput (current : Endpoint graph) where
  index : Fin (handler_locations current.history).length
  requested : Instance
  effect : Instantiation.Effect
  operation : Nat
  selectedClause : CoreSyntax.Clause
  value : CoreMachine.Value
  code : Code
  environment : Environment
  plain : PlainData
  context : SourceRecursiveRoutes.Context
  outward : List Instance
  result : Ty
  same : (location current index).data.effectInst = requested
  prefixScope : SourceRecursiveRoutes.Scope context (location current index).front.erase
  route : SourceResourceRoutes.Route outward context requested none
  lookup : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) current.physical =
    .ok (.handler (location current index).inside (location current index).site (location current index).environment
      (location current index).data.activation (location current index).outside)
  selected : (location current index).installation.clauses.find? (fun clause => clause.operation == operation) = some selectedClause
  operand : ValueRel graph current.owners current.state.heap value code
  requestCarrier : EnvCloses graph current.owners current.state.heap environment
    (.perform effect operation .unit) (.perform (Instantiation.freezeEffect requested) operation .unit)
  plainContext : plain.context = .perform (Instantiation.freezeEffect requested) operation
  ready : ∀ parameter binder body, ClauseAt operation (location current index).data.clauses parameter binder body → ClosedExcept parameter body
  control : current.state.control = .returned value
  maps : current.maps = [(current.owners,.request effect operation environment)]
  focus : current.focus = ⟨.perform (Instantiation.freezeEffect requested) operation code,plain.scope,.nil⟩

structure CaptureData {graph : Graph} {current : Endpoint graph} (input : CaptureInput current) where
  fuel : Nat
  argument : Binder
  rawBody : Code
  body : Code
  pattern : input.selectedClause.argument = .binder argument
  translated : translateFuel graph fuel
    (⟨(location current input.index).installation.handler,input.selectedClause.owner,ticket graph input.selectedClause.owner⟩ ::
      (location current input.index).owners) input.selectedClause.body = .ok rawBody
  installation : GeneralClausePast graph (location current input.index).owners
    (location current input.index).installation.handler input.selectedClause.owner (location current input.index).data.activation current.state.nextOwner
    ((location current input.index).inside ++ [.handlerBoundary (location current input.index).site
      (location current input.index).environment (location current input.index).data.activation]) (location current input.index).data
  header : OwnerHeader graph (location current input.index).owners current.state.heap
    (location current input.index).installation.handler input.selectedClause.owner (location current input.index).data.activation (location current input.index).data
  sameInstallation : HEq installation.installation (location current input.index).installation
  sameSelected : installation.selected = input.selectedClause
  sameInside : installation.originalInside = (location current input.index).inside
  sameOutside : installation.originalOutside = (location current input.index).outside
  actual : GeneralStepWitness graph
    ⟨captureBefore current.state input.value input.effect input.operation input.environment current.physical,
      .eval ⟨.perform (Instantiation.freezeEffect input.requested) input.operation input.code,input.plain.scope,current.lexical⟩,
      current.owners,[(current.owners,.request input.effect input.operation input.environment)]⟩
    ⟨captureAfter current.state input.selectedClause argument.id input.value (location current input.index).installation.handler
      (location current input.index).data.activation (location current input.index).site (location current input.index).environment
      (location current input.index).inside (location current input.index).outside,
      .eval ⟨body.subst argument.id input.code,.ticket (ticket graph input.selectedClause.owner) current.state.nextOwner,
        .live current.state.nextOwner input.result (location current input.index).data.answer
          ((location current input.index).front.append (.push (.handler (location current input.index).data) .nil))
          (location current input.index).data.scope (location current input.index).tail⟩,
      ⟨(location current input.index).installation.handler,input.selectedClause.owner,ticket graph input.selectedClause.owner⟩ ::
        (location current input.index).owners,[]⟩ [.ticket current.state.nextOwner] []

private theorem capture_produced {graph : Graph} {current : Endpoint graph} (input : CaptureInput current) : Nonempty (CaptureData input) := by
  obtain ⟨fuel,argument,rawBody,body,pattern,clauseAt,translated,closed,step,installation,header,successor,
    site,environment,installed,selected,inside,outside,same⟩ := capture_history current.history input.index
      input.same input.prefixScope input.route input.lookup input.selected input.operand input.requestCarrier
      input.plain input.plainContext input.ready input.result input.plain.scope
  exact ⟨⟨fuel,argument,rawBody,body,pattern,translated,installation,header,installed,selected,inside,outside,step⟩⟩

noncomputable def capture_data {graph : Graph} {current : Endpoint graph} (input : CaptureInput current) : CaptureData input :=
  Classical.choice (capture_produced input)

noncomputable def capture_result {graph : Graph} {current : Endpoint graph} (input : CaptureInput current) : Result current [.ticket current.state.nextOwner] [] := by
  let data := capture_data input
  let here := location current input.index
  let after : Endpoint graph := {
    state := captureAfter current.state input.selectedClause data.argument.id input.value here.installation.handler
      here.data.activation here.site here.environment here.inside here.outside
    focus := ⟨data.body.subst data.argument.id input.code,.ticket (ticket graph input.selectedClause.owner) current.state.nextOwner,.nil⟩
    owners := ⟨here.installation.handler,input.selectedClause.owner,ticket graph input.selectedClause.owner⟩ :: here.owners
    maps := []
    physical := .clauseBoundary here.installation.handler input.selectedClause.owner here.data.activation current.state.nextOwner
      (some (here.inside ++ [.handlerBoundary here.site here.environment here.data.activation])) :: here.outside
    lexical := .live current.state.nextOwner input.result here.data.answer
      (here.front.append (.push (.handler here.data) .nil)) here.data.scope here.tail
    history := .live data.installation data.header (here.before.append (.handler here.installation here.header .nil)) here.after
    frames := rfl }
  have frames : current.state.frames = .request input.effect input.operation input.environment :: current.physical := by
    simpa [input.maps,framesOf] using current.frames
  have beforeSame : captureBefore current.state input.value input.effect input.operation input.environment current.physical = current.state := by
    simp only [captureBefore]
    rw [← frames,← input.control]
  refine ⟨after,?_,.positive ?_⟩
  · simpa only [beforeSame] using data.actual.core
  · simpa only [Endpoint.point,input.focus,CoreCleanupRunFrames.attach,Stack.append,after,here] using data.actual.target

/-- A current mixed front is checked structurally. Nonmatching live/spent
identities are explicit current guards; a matching spent frame has no rule. -/
inductive PassFront (handler owner : Nat) :
    {physical : List CoreMachine.Frame} → {target : Stack} → GeneralHistory graph heap physical target → Prop where
  | nil : PassFront handler owner (GeneralHistory.nil (graph := graph) (heap := heap))
  | push (frame : PushCarrier graph owners heap core target) (ordinary)
      (tail : GeneralHistory graph heap physical lexical) (pass : PassFront handler owner tail) :
      PassFront handler owner (.push frame ordinary tail)
  | handler (past : GeneralHandlerPast graph owners site environment data)
      (header : CoreEffectFrames.BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data))
      (tail : GeneralHistory graph heap physical target) (pass : PassFront handler owner tail) :
      PassFront handler owner (.handler past header tail)
  | live (past : GeneralClausePast graph owners otherHandler otherOwner activation clauseTicket captured data)
      (header : OwnerHeader graph owners heap otherHandler otherOwner activation data)
      (saved : GeneralHistory graph heap captured capturedTarget)
      (tail : GeneralHistory graph heap physical target)
      (different : handler ≠ otherHandler ∨ owner ≠ otherOwner) (pass : PassFront handler owner tail) :
      PassFront handler owner (.live (result := result) past header saved tail)
  | spent (past : GeneralClausePast graph owners otherHandler otherOwner activation clauseTicket captured data)
      (header : OwnerHeader graph owners heap otherHandler otherOwner activation data)
      (tail : GeneralHistory graph heap physical target)
      (different : handler ≠ otherHandler ∨ owner ≠ otherOwner) (pass : PassFront handler owner tail) :
      PassFront handler owner (.spent past header tail)
  | append (first : GeneralHistory graph heap firstPhysical firstTarget) (second : GeneralHistory graph heap secondPhysical secondTarget)
      (left : PassFront handler owner first) (right : PassFront handler owner second) :
      PassFront handler owner (first.append second)

def PhysicalPass (handler owner : Nat) (physical : List CoreMachine.Frame) : Prop :=
  ∀ rest cut, CoreMachine.findOwner handler owner rest = .ok cut →
    CoreMachine.findOwner handler owner (physical ++ rest) = .ok {cut with inside := physical ++ cut.inside}

private theorem carrier_pass (frame : PushCarrier graph owners heap core target) : PhysicalPass handler owner [core] := by
  intro rest cut found
  cases frame with
  | ordinary related =>
    rename_i plain
    change FrameRel graph owners heap core plain.context at related
    generalize contextEq : plain.context = context at related
    cases related <;> simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | initializer related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | request related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | resume related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | cleanup related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | boundary related => cases related <;> simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]

private theorem different_pair {a b c d : Nat} (different : a ≠ c ∨ b ≠ d) : ¬ (a = c ∧ b = d) := by
  intro same
  cases different with
  | inl h => exact h same.1
  | inr h => exact h same.2

theorem PassFront.physical_pass {graph : Graph} {heap : CoreMachine.Heap} {handler owner : Nat}
    {physical : List CoreMachine.Frame} {target : Stack} {history : GeneralHistory graph heap physical target}
    (pass : PassFront handler owner history) : PhysicalPass handler owner physical := by
  induction pass with
  | nil => exact fun _ _ h => h
  | push frame ordinary tail pass ih =>
    intro rest cut found
    have leading := carrier_pass frame (rest := _ ++ rest) (cut := _) (ih rest cut found)
    simpa using leading
  | handler past header tail pass ih =>
    intro rest cut found
    have leading := carrier_pass (PushCarrier.boundary header) (rest := _ ++ rest) (cut := _) (ih rest cut found)
    simpa using leading
  | live past header saved tail different pass ih =>
    intro rest cut found
    have tailFound := ih rest cut found
    simp only [List.cons_append]
    have notSame := different_pair different
    simp [CoreMachine.findOwner,Bool.and_eq_true,beq_iff_eq,notSame,tailFound,Functor.map,Except.map]
  | spent past header tail different pass ih =>
    intro rest cut found
    have tailFound := ih rest cut found
    simp only [List.cons_append]
    have notSame := different_pair different
    simp [CoreMachine.findOwner,Bool.and_eq_true,beq_iff_eq,notSame,tailFound,Functor.map,Except.map]
  | append first second left right ihLeft ihRight =>
    intro rest cut found
    simpa [List.append_assoc] using ihLeft _ _ (ihRight rest cut found)


structure ResumeInput (current : Endpoint graph) where
  handler : Nat
  owner : Nat
  occurrence : Nat
  dynamicTicket : Nat
  savedOwners : OwnerMap
  frameOwners : OwnerMap
  data : HandlerData
  result : Ty
  captured : List CoreMachine.Frame
  capturedTarget : Stack
  installation : GeneralClausePast graph savedOwners handler owner occurrence dynamicTicket captured data
  header : OwnerHeader graph savedOwners current.state.heap handler owner occurrence data
  capturedHistory : GeneralHistory graph current.state.heap captured capturedTarget
  outside : List CoreMachine.Frame
  tail : Stack
  outsideHistory : GeneralHistory graph current.state.heap outside tail
  front : List CoreMachine.Frame
  frontTarget : Stack
  frontHistory : GeneralHistory graph current.state.heap front frontTarget
  pass : PassFront handler owner frontHistory
  physical : current.physical = front ++ .clauseBoundary handler owner occurrence dynamicTicket (some captured) :: outside
  lexical : current.lexical = frontTarget.append (.live dynamicTicket result data.answer capturedTarget data.scope tail)
  sameHistory : HEq current.history
    (frontHistory.append (.live (result := result) installation header capturedHistory outsideHistory))
  plain : PlainData
  binder : Nat
  frame : CoreResumeFrames.ResumeRel graph frameOwners current.state.heap (.resume handler owner) plain
  context : plain.context = .resume binder
  value : CoreMachine.Value
  code : Code
  operand : ValueRel graph current.owners current.state.heap value code
  resolve : plain.scope.resolve binder = some dynamicTicket
  control : current.state.control = .returned value
  maps : current.maps = [(frameOwners,.resume handler owner)]
  focus : current.focus = ⟨.resume binder code,plain.scope,.nil⟩

noncomputable def OwnerLocation.reindex (selected : OwnerLocation graph heap handler owner physical target)
    (samePhysical : nextPhysical = physical) (sameTarget : nextTarget = target) :
    OwnerLocation graph heap handler owner nextPhysical nextTarget := by
  cases samePhysical
  cases sameTarget
  exact selected

@[simp] theorem OwnerLocation.reindex_ticket (selected : OwnerLocation graph heap handler owner physical target)
    (samePhysical : nextPhysical = physical) (sameTarget : nextTarget = target) :
    (OwnerLocation.reindex selected samePhysical sameTarget).dynamicTicket = selected.dynamicTicket := by
  cases samePhysical
  cases sameTarget
  rfl

/-- First physical lookup follows from the structurally checked SAME current
front. The original complete clause/header and captured/outside histories are
used to construct the cut; scan success is not a premise. -/
noncomputable def resume_location {graph : Graph} {current : Endpoint graph} (input : ResumeInput current) :
    OwnerLocation graph current.state.heap input.handler input.owner current.physical current.lexical := by
  let here : OwnerLocation graph current.state.heap input.handler input.owner
      (.clauseBoundary input.handler input.owner input.occurrence input.dynamicTicket (some input.captured) :: input.outside)
      (.live input.dynamicTicket input.result input.data.answer input.capturedTarget input.data.scope input.tail) := {
    front := [],frontTarget := .nil,frontHistory := .nil
    owners := input.savedOwners,occurrence := input.occurrence,dynamicTicket := input.dynamicTicket
    data := input.data,result := input.result,captured := input.captured,capturedTarget := input.capturedTarget
    capturedHistory := input.capturedHistory,installation := input.installation,header := input.header
    outside := input.outside,tail := input.tail,outsideHistory := input.outsideHistory
    whole := .live input.installation input.header input.capturedHistory input.outsideHistory
    physicalSame := rfl,targetSame := rfl
    cut := .hit input.header input.capturedHistory.related input.outsideHistory.related }
  have leading := here.prepend input.frontHistory input.pass.physical_pass
  exact OwnerLocation.reindex leading input.physical input.lexical

noncomputable def resume_result {graph : Graph} {current : Endpoint graph} (input : ResumeInput current) : Result current [] [.ticket (resume_location input).dynamicTicket] := by
  let selected := resume_location input
  let after : Endpoint graph := {
    state := resumeAfter current.state input.handler input.owner selected.occurrence selected.dynamicTicket input.value
      selected.captured selected.front selected.outside
    focus := ⟨input.code,input.plain.scope,.nil⟩
    owners := current.owners,maps := []
    physical := selected.captured ++ (selected.front ++
      .clauseBoundary input.handler input.owner selected.occurrence selected.dynamicTicket none :: selected.outside)
    lexical := selected.capturedTarget.append (selected.frontTarget.append
      (.spent selected.dynamicTicket selected.data.answer selected.data.scope selected.tail))
    history := selected.restored_history
    frames := by simp [resumeAfter,List.append_assoc,framesOf] }
  have resolve : input.plain.scope.resolve input.binder = some selected.dynamicTicket := by
    simpa only [selected,resume_location,OwnerLocation.reindex_ticket,OwnerLocation.prepend] using input.resolve
  have actual := resume_general selected.cut input.frame input.context input.operand resolve input.plain.scope
  have frames : current.state.frames = .resume input.handler input.owner :: current.physical := by
    simpa [input.maps,framesOf] using current.frames
  have beforeSame : resumeBefore current.state input.handler input.owner input.value current.physical = current.state := by
    simp only [resumeBefore]
    rw [← frames,← input.control]
  refine ⟨after,?_,.positive ?_⟩
  · simpa only [beforeSame] using actual.core
  · simpa only [Endpoint.point,input.focus,CoreCleanupRunFrames.attach,Stack.append,after] using actual.target

/-- Normal spent-marker return threads the exact suffix and current value.
It does not authenticate a dormant cleanup caller's activation scope. -/
structure SpentReturnInput (current : Endpoint graph) where
  owners : OwnerMap
  handler : Nat
  owner : Nat
  occurrence : Nat
  dynamicTicket : Nat
  captured : List CoreMachine.Frame
  data : HandlerData
  installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data
  header : OwnerHeader graph owners current.state.heap handler owner occurrence data
  suffixPhysical : List CoreMachine.Frame
  suffixTarget : Stack
  suffix : GeneralHistory graph current.state.heap suffixPhysical suffixTarget
  value : CoreMachine.Value
  code : Code
  scope : Execution.Scope
  operand : ValueRel graph current.owners current.state.heap value code
  control : current.state.control = .returned value
  empty : EmptyFocus current code scope
  physical : current.physical = .clauseBoundary handler owner occurrence dynamicTicket none :: suffixPhysical
  lexical : current.lexical = .spent dynamicTicket data.answer data.scope suffixTarget
  sameHistory : HEq current.history (GeneralHistory.spent installation header suffix)

noncomputable def spent_return_result {graph : Graph} {current : Endpoint graph} (input : SpentReturnInput current) : Result current [] [] := by
  let after : Endpoint graph := {
    state := observedState current.state input.value input.suffixPhysical (.clauseReturned input.dynamicTicket)
    focus := ⟨input.code,input.data.scope,.nil⟩
    owners := input.owners,maps := [],physical := input.suffixPhysical,lexical := input.suffixTarget
    history := input.suffix,frames := rfl }
  have actual := leave_clause (base := current.state) input.header input.operand input.suffix.related input.dynamicTicket input.scope
  have beforeSame : returnedState current.state input.value
      (.clauseBoundary input.handler input.owner input.occurrence input.dynamicTicket none :: input.suffixPhysical) = current.state := by
    simp only [returnedState]
    rw [← input.physical,← empty_frames input.empty,← input.control]
  refine ⟨after,?_,.positive ?_⟩
  · simpa only [beforeSame] using actual.core
  · rw [empty_point input.empty,input.lexical]
    exact actual.target

/-- The only edge constructors are named operation producers. There is no
constructor accepting Result, GeneralLink, GeneralChain or arbitrary matching. -/
inductive Operation : (before after : Endpoint graph) → List Owner → List Owner → Type where
  | bind (input : BindInput before) : Operation before (bind_result input).after [] []
  | beta (input : BetaInput before) : Operation before (beta_result input).after [] []
  | bindReturn (input : BindReturnInput before) : Operation before (bind_return_result input).after [] []
  | handler (input : HandlerInput before) : Operation before (handler_result input).after [] []
  | handlerReturn (input : HandlerReturnInput before) : Operation before (handler_return_result input).after [] []
  | literal (input : LiteralInput before) : Operation before (literal_result input).after [] []
  | entry (input : EntryInput before) : Operation before (entry_result input).after [] []
  | swap (input : SwapInput before) : Operation before (swap_result input).after [] []
  | tuple (input : TupleInput before) : Operation before (tuple_result input).after [] []
  | capture (input : CaptureInput before) : Operation before (capture_result input).after [.ticket before.state.nextOwner] []
  | resume (input : ResumeInput before) : Operation before (resume_result input).after [] [.ticket (resume_location input).dynamicTicket]
  | spentReturn (input : SpentReturnInput before) : Operation before (spent_return_result input).after [] []

theorem Operation.actual {graph : Graph} {before after : Endpoint graph} (operation : Operation before after created discharged) :
    CoreMachine.next graph before.state = .stepped after.state ∧ Matching graph before after created discharged := by
  cases operation with
  | bind input => exact ⟨(bind_result input).core,(bind_result input).matching⟩
  | beta input => exact ⟨(beta_result input).core,(beta_result input).matching⟩
  | bindReturn input => exact ⟨(bind_return_result input).core,(bind_return_result input).matching⟩
  | handler input => exact ⟨(handler_result input).core,(handler_result input).matching⟩
  | handlerReturn input => exact ⟨(handler_return_result input).core,(handler_return_result input).matching⟩
  | literal input => exact ⟨(literal_result input).core,(literal_result input).matching⟩
  | entry input => exact ⟨(entry_result input).core,(entry_result input).matching⟩
  | swap input => exact ⟨(swap_result input).core,(swap_result input).matching⟩
  | tuple input => exact ⟨(tuple_result input).core,(tuple_result input).matching⟩
  | capture input => exact ⟨(capture_result input).core,(capture_result input).matching⟩
  | resume input => exact ⟨(resume_result input).core,(resume_result input).matching⟩
  | spentReturn input => exact ⟨(spent_return_result input).core,(spent_return_result input).matching⟩

/-- Execution starts at the actual produced running endpoint and extends only
with an operation whose source is exactly the preceding endpoint. Immutable
start receipt, original saved value and complete original suffix stay indexed. -/
inductive Generated
    (start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget) :
    (current : Endpoint graph) → Nat → List Owner → List Owner → Type where
  | initial : Generated start (started start) 0 [] []
  | next (earlier : Generated start before count created discharged)
      (operation : Operation before after laterCreated laterDischarged) :
      Generated start after (count + 1) (created ++ laterCreated) (laterDischarged ++ discharged)


theorem Matching.target_trace {graph : Graph} {before after : Endpoint graph}
    (matching : Matching graph before after created discharged) :
    CoreUnwindRelation.Trace before.point.machine after.point.machine created discharged := by
  cases matching with
  | positive step => exact step.trace
  | administrative same permitted decreasing => rw [same]; exact .refl _

theorem Matching.accounting {graph : Graph} {before after : Endpoint graph}
    (matching : Matching graph before after created discharged) :
    (before.point.machine.stack.erase.owners ++ created).Perm (after.point.machine.stack.erase.owners ++ discharged) := by
  cases matching with
  | positive step => exact positive_accounting step
  | administrative same permitted decreasing => rw [same]

theorem Generated.core_steps {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (generated : Generated start current count created discharged) :
    CoreAllocationHistory.Steps graph count (started start).state current.state := by
  induction generated with
  | initial => exact .refl _
  | next earlier operation ih => exact .snoc ih operation.actual.1

theorem Generated.target_trace {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (generated : Generated start current count created discharged) :
    CoreUnwindRelation.Trace (started start).point.machine current.point.machine created discharged := by
  induction generated with
  | initial => exact .refl _
  | next earlier operation ih => exact ih.append operation.actual.2.target_trace

theorem Generated.accounting {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (generated : Generated start current count created discharged) :
    ((started start).point.machine.stack.erase.owners ++ created).Perm
      (current.point.machine.stack.erase.owners ++ discharged) := by
  induction generated with
  | initial => exact .refl _
  | next earlier operation ih =>
    have edge := operation.actual.2.accounting
    apply List.perm_iff_count.mpr
    intro owner
    have firstCount := ih.count_eq owner
    have edgeCount := edge.count_eq owner
    simp only [List.count_append] at firstCount edgeCount ⊢
    omega

/-- Every generated edge is an actual next equation with positive target work
or a named finite administrative family and strict common-potential decrease. -/
theorem Operation.bounded_matching {graph : Graph} {before after : Endpoint graph}
    (operation : Operation before after created discharged) :
    CoreMachine.next graph before.state = .stepped after.state ∧
    (CoreUnwindRelation.Positive before.point.machine after.point.machine created discharged ∨
      (created = [] ∧ discharged = [] ∧ before.point.machine = after.point.machine ∧
        (CoreAdministrativeSteps.ready graph before.state = true ∨ CoreStrictPotential.traversalReady graph before.state = true) ∧
        CoreStrictPotential.potential graph after.state < CoreStrictPotential.potential graph before.state)) := by
  have actual := operation.actual
  refine ⟨actual.1,?_⟩
  cases actual.2 with
  | positive step => exact Or.inl step
  | administrative same permitted decreasing => exact Or.inr ⟨rfl,rfl,same,permitted,decreasing⟩


/-- Full immutable running data, including original saved map, value, action
and original physical suffix. Heap weakening changes only proof evidence. -/
structure RunningStamp where
  owners : OwnerMap
  action : Nat
  environment : Environment
  data : ActionData
  savedValue : CoreMachine.Value
  savedCode : Code
  originalPhysical : List CoreMachine.Frame

noncomputable def running_stamps (history : GeneralHistory graph heap physical target) : List RunningStamp :=
  match history with
  | .nil | .retained _ | .unwinding _ | .closing _ _ _ => []
  | .push _ _ tail => running_stamps tail
  | .handler _ _ tail => running_stamps tail
  | @GeneralHistory.running _ _ owners action environment data value code original _ => [⟨owners,action,environment,data,value,code,original⟩]
  | .live _ _ saved tail => running_stamps saved ++ running_stamps tail
  | .spent _ _ tail => running_stamps tail
  | .append first second => running_stamps first ++ running_stamps second

theorem running_stamps_weaken (history : GeneralHistory graph heap physical target) (extension : HeapExtends heap larger) :
    running_stamps (history.heap_weaken extension) = running_stamps history := by
  induction history <;> simp_all [GeneralHistory.heap_weaken,running_stamps]

private theorem stamps_heq {graph : Graph} {heap : CoreMachine.Heap}
    (first : GeneralHistory graph heap firstPhysical firstTarget)
    (second : GeneralHistory graph heap secondPhysical secondTarget)
    (physicalSame : firstPhysical = secondPhysical) (targetSame : firstTarget = secondTarget)
    (same : HEq first second) : running_stamps first = running_stamps second := by
  cases physicalSame
  cases targetSame
  exact congrArg running_stamps (eq_of_heq same)

private theorem stamps_prepend (selected : HandlerLocation graph heap physical target)
    (leading : GeneralHistory graph heap front frontTarget) :
    running_stamps (selected.prepend leading).before = running_stamps leading ++ running_stamps selected.before ∧
    running_stamps (selected.prepend leading).after = running_stamps selected.after := ⟨rfl,rfl⟩

private theorem stamps_suffix (selected : HandlerLocation graph heap physical target)
    (trailing : GeneralHistory graph heap front frontTarget) :
    running_stamps (selected.suffix trailing).before = running_stamps selected.before ∧
    running_stamps (selected.suffix trailing).after = running_stamps selected.after ++ running_stamps trailing := ⟨rfl,rfl⟩

/-- Physical handler selection partitions the SAME complete history's running
receipts, including dormant receipts inside live owners. -/
theorem handler_location_stamps (history : GeneralHistory graph heap physical target)
    (selected : HandlerLocation graph heap physical target) (member : selected ∈ handler_locations history) :
    running_stamps history = running_stamps selected.before ++ running_stamps selected.after := by
  induction history with
  | nil | retained | running | unwinding | closing => simp [handler_locations] at member
  | push frame ordinary tail ih =>
    simp only [handler_locations] at member
    obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    simpa [running_stamps,HandlerLocation.prepend] using ih old oldMember
  | handler past header tail ih =>
    simp only [handler_locations] at member
    cases member with
    | head => simp [running_stamps]
    | tail _ member =>
      obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
      simpa [running_stamps,HandlerLocation.prepend] using ih old oldMember
  | live past header saved tail ihSaved ihTail =>
    simp only [handler_locations] at member
    obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    simpa [running_stamps,HandlerLocation.prepend,List.append_assoc] using
      congrArg (fun stamps => running_stamps saved ++ stamps) (ihTail old oldMember)
  | spent past header tail ih =>
    simp only [handler_locations] at member
    obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    simpa [running_stamps,HandlerLocation.prepend] using ih old oldMember
  | append first second ihFirst ihSecond =>
    simp only [handler_locations] at member
    cases List.mem_append.mp member with
    | inl member =>
      obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
      simpa [running_stamps,HandlerLocation.suffix,List.append_assoc] using
        congrArg (fun stamps => stamps ++ running_stamps second) (ihFirst old oldMember)
    | inr member =>
      obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
      simpa [running_stamps,HandlerLocation.prepend,List.append_assoc] using
        congrArg (fun stamps => running_stamps first ++ stamps) (ihSecond old oldMember)


private theorem restored_stamps (selected : OwnerLocation graph heap handler owner physical target) :
    running_stamps selected.restored_history = running_stamps selected.capturedHistory ++
      (running_stamps selected.frontHistory ++ running_stamps selected.outsideHistory) := rfl

private theorem reindex_restored_stamps (selected : OwnerLocation graph heap handler owner physical target)
    (samePhysical : nextPhysical = physical) (sameTarget : nextTarget = target) :
    running_stamps (OwnerLocation.reindex selected samePhysical sameTarget).restored_history =
      running_stamps selected.restored_history := by
  cases samePhysical
  cases sameTarget
  rfl

private theorem perm_of_eq {α : Type} {a b : List α} (same : a = b) : a.Perm b := by
  rw [same]

/-- Named operations preserve the full immutable running receipt data. Resume
can change its nesting order, so the statement is a permutation. -/
theorem Operation.running_receipts {graph : Graph} {before after : Endpoint graph}
    (operation : Operation before after created discharged) :
    (running_stamps before.history).Perm (running_stamps after.history) := by
  cases operation with
  | bind input => simp [bind_result,running_stamps]
  | beta input => simp [beta_result]
  | bindReturn input =>
    have same := stamps_heq before.history (input.past.current_history input.extension)
      input.physical input.lexical input.sameHistory
    simpa only [bind_return_result,CallerBindPast.current_history,running_stamps] using perm_of_eq same
  | handler input => simp [handler_result,running_stamps]
  | handlerReturn input =>
    have same := stamps_heq before.history
      (GeneralHistory.handler input.installation input.header input.suffix)
      input.physical input.lexical input.sameHistory
    simpa only [handler_return_result,running_stamps] using perm_of_eq same
  | literal input => simp [literal_result]
  | entry input => simp [entry_result]
  | swap input => simp [swap_result]
  | tuple input => simp [tuple_result,running_stamps_weaken]
  | capture input =>
    have same := handler_location_stamps before.history (location before input.index)
      (by exact List.getElem_mem _)
    simpa [capture_result,captureAfter,running_stamps] using perm_of_eq same
  | resume input =>
    have same := stamps_heq before.history
      (input.frontHistory.append (.live input.installation input.header input.capturedHistory input.outsideHistory))
      input.physical input.lexical input.sameHistory
    have afterSame : running_stamps (resume_result input).after.history =
        running_stamps input.capturedHistory ++ (running_stamps input.frontHistory ++ running_stamps input.outsideHistory) := by
      change running_stamps (resume_location input).restored_history = _
      unfold resume_location
      rw [reindex_restored_stamps]
      simp only [restored_stamps,OwnerLocation.prepend,running_stamps,List.append_nil]
    rw [afterSame,same]
    simp only [running_stamps]
    simpa only [List.append_assoc] using
      (List.perm_append_comm : (running_stamps input.frontHistory ++ running_stamps input.capturedHistory).Perm
        (running_stamps input.capturedHistory ++ running_stamps input.frontHistory)).append_right (running_stamps input.outsideHistory)
  | spentReturn input =>
    have same := stamps_heq before.history
      (GeneralHistory.spent input.installation input.header input.suffix)
      input.physical input.lexical input.sameHistory
    simpa [spent_return_result,observedState,running_stamps] using perm_of_eq same

noncomputable def original_stamp
    (_start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget) : RunningStamp :=
  ⟨cleanupOwners,action,environment,data,savedValue,savedCode,originalPhysical⟩

theorem Generated.same_original_receipt {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (generated : Generated start current count created discharged) :
    original_stamp start ∈ running_stamps current.history := by
  induction generated with
  | initial => simp [started,original_stamp,id,running_stamps]
  | next earlier operation ih => exact operation.running_receipts.mem_iff.mp ih

theorem Generated.from_actual_start {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (generated : Generated start current count created discharged) :
    CoreAllocationHistory.Steps graph (count + 1) (start_before start).state current.state ∧
    CoreUnwindRelation.Trace (start_before start).point.machine current.point.machine created discharged := by
  have core : CoreAllocationHistory.Steps graph (count + 1) (start_before start).state current.state := by
    induction generated with
    | initial => exact .snoc (.refl _) start.actual.core
    | next earlier operation ih => exact .snoc ih operation.actual.1
  refine ⟨core,?_⟩
  have first := start.actual.target.trace
  simpa only [start_before,started,Endpoint.point,CoreCleanupRunFrames.attach,Stack.append,List.nil_append,List.append_nil] using
    first.append generated.target_trace


/-- Every retained stamp comes from an actual running receipt node in the
current complete history, including dormant capture nodes. -/
theorem running_stamps_sound {graph : Graph} {heap : CoreMachine.Heap}
    (stamp : RunningStamp) (history : GeneralHistory graph heap physical target)
    (member : stamp ∈ running_stamps history) :
    CoreCallableCleanupReachableTransport.RunningReceipt graph stamp.owners heap stamp.action stamp.environment
      stamp.data stamp.savedValue stamp.savedCode stamp.originalPhysical := by
  induction history generalizing stamp with
  | nil | retained | unwinding | closing => simp [running_stamps] at member
  | push frame ordinary tail ih => exact ih stamp member
  | handler past header tail ih => exact ih stamp member
  | running receipt =>
    simp only [running_stamps,List.mem_singleton] at member
    cases member
    exact receipt
  | live past header saved tail ihSaved ihTail =>
    cases List.mem_append.mp member with
    | inl member => exact ihSaved stamp member
    | inr member => exact ihTail stamp member
  | spent past header tail ih => exact ih stamp member
  | append first second ihFirst ihSecond =>
    cases List.mem_append.mp member with
    | inl member => exact ihFirst stamp member
    | inr member => exact ihSecond stamp member

theorem Generated.retained_running_receipt {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (generated : Generated start current count created discharged) :
    CoreCallableCleanupReachableTransport.RunningReceipt graph cleanupOwners current.state.heap action environment data savedValue savedCode originalPhysical :=
  running_stamps_sound (original_stamp start) current.history generated.same_original_receipt

/-- Matching spent control cannot be passed, even when an older live owner is
present farther out. This is a current structural obstruction. -/
theorem matching_spent_blocks
    (past : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data)
    (header : OwnerHeader graph owners heap handler owner occurrence data)
    (tail : GeneralHistory graph heap physical target) :
    ¬ PassFront handler owner (GeneralHistory.spent past header tail) := by
  intro passed
  have hit : CoreMachine.findOwner handler owner [.clauseBoundary handler owner 0 0 (some [])] =
      .ok ⟨[],handler,owner,0,0,[],[]⟩ := by simp [CoreMachine.findOwner]
  have impossible := passed.physical_pass _ _ hit
  simp [CoreMachine.findOwner] at impossible

#print axioms Operation.actual
#print axioms Operation.bounded_matching
#print axioms Operation.running_receipts
#print axioms Generated.core_steps
#print axioms Generated.target_trace
#print axioms Generated.accounting
#print axioms Generated.from_actual_start
#print axioms Generated.same_original_receipt
#print axioms PassFront.physical_pass
#print axioms Generated.retained_running_receipt
#print axioms matching_spent_blocks
end Ash.OneShot.CoreCallableGeneratedChronology
