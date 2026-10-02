import CoreCallableComposedRuntimeCurrent
import CoreCallableGeneralStartedFrom
import CoreCellSteps
import CoreCallableGeneratedBindProducers
import ComposedResourceRuntimeOriginProbes
namespace Ash.OneShot.CoreCallableComposedRuntimeCalls
open ScopedExpressions ScopedExecution CoreSyntax CoreTranslation CoreMachine CoreValueRelation
open CoreStrictStack CoreStrictFrames CoreInitialPrefix CoreCallableComposedResourceEntry
open CoreCallableComposedRuntimeBindings CoreCallableComposedRuntimeCurrent
open CoreCallableGeneratedChronology CoreCallableChecks CoreOrdinaryCompletion
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {graph : Graph} {s : Selection graph}

def opened (r : ReaderSelection s) (code : Code) : Code := (closeCode s code).subst r.binder.id r.initializer

/-- Finite original higher-order node selection; no future environment or value. -/
structure HigherSelection (r : ReaderSelection s) where
  binder : Binder
  parameter : Binder
  binderType : binder.type = .function r.binder.type .integer [.cell (.bound s.resource)]
  functionSite : Nat
  functionBody : Nat
  tailSite : Nat
  node : CoreSyntax.Node
  functionNode : CoreSyntax.Node
  rawFunction : Code
  rawTail : Code
  fuel : Nat
  known : graph.node r.tailSite = some node
  kind : node.kind = .bind binder functionSite tailSite
  functionKnown : graph.node functionSite = some functionNode
  functionKind : functionNode.kind = .function parameter functionBody
  functionTranslated : translateFuel graph fuel [] functionSite = .ok (.lambda parameter.id rawFunction)
  tailTranslated : translateFuel graph fuel [] tailSite = .ok rawTail
  rawSame : r.rawTail = .bind binder.id (.lambda parameter.id rawFunction) rawTail
  binderOuter : binder.id ≠ s.outer.id
  binderHandle : binder.id ≠ s.handle.id
  binderReader : binder.id ≠ r.binder.id
  parameterOuter : parameter.id ≠ s.outer.id
  parameterHandle : parameter.id ≠ s.handle.id
  parameterReader : parameter.id ≠ r.binder.id
  ready : ClosedExcept binder.id (opened r rawTail)
  noTicket : Execution.Scope.none.translate (Context.bind binder.id (opened r rawTail)).dependencies = some []

def HigherSelection.closedBody {r : ReaderSelection s} (h : HigherSelection r) : Code := opened r h.rawFunction
def HigherSelection.initializer {r : ReaderSelection s} (h : HigherSelection r) : Code := .lambda h.parameter.id h.closedBody
def HigherSelection.suffix {r : ReaderSelection s} (h : HigherSelection r) : Code := opened r h.rawTail
def HigherSelection.plain {r : ReaderSelection s} (h : HigherSelection r) : PlainData :=
  ⟨.bind h.binder.id h.suffix,.none,
    .function r.inputType .integer [.cell s.s8.nextActivation]
      (Syntax.resourceDependencies h.closedBody.dependencies),.integer,[],h.noTicket⟩

theorem HigherSelection.body_exact {r : ReaderSelection s} (h : HigherSelection r) :
    r.suffix.subst r.binder.id r.initializer = .bind h.binder.id h.initializer h.suffix := by
  simp only [ReaderSelection.suffix,h.rawSame,closeCode,opened,HigherSelection.initializer,
    HigherSelection.closedBody,HigherSelection.suffix,Code.subst,Code.instantiate,
    Ne.symm h.binderOuter,Ne.symm h.binderHandle,Ne.symm h.binderReader,
    Ne.symm h.parameterOuter,Ne.symm h.parameterHandle,Ne.symm h.parameterReader,↓reduceIte]

/-- The existing executable callable check is run again on the original higher node. -/
structure CheckedHigher {r : ReaderSelection s} (h : HigherSelection r) where
  callable : CheckedCallable
  accepted : checkAmbient graph h.functionSite [] = .ok callable
  parameterSame : callable.parameter = h.parameter.id
  bodySame : callable.body = h.functionBody
  rawSame : callable.rawBody = h.rawFunction
  closedAccepted : closedLambdaCheck h.initializer = true
  closed : ClosedValue h.initializer

def produce_higher {r : ReaderSelection s} (h : HigherSelection r) : Except CoreCallableComposedRuntimeBindings.Error (CheckedHigher h) := do
  match accepted : checkAmbient graph h.functionSite [] with
  | .error error => .error (.callable error)
  | .ok callable =>
    if parameterSame : callable.parameter = h.parameter.id then
      if bodySame : callable.body = h.functionBody then
        if rawSame : codeEq callable.rawBody h.rawFunction = true then
          if closed : closedLambdaCheck h.initializer = true then
            .ok ⟨callable,accepted,parameterSame,bodySame,codeEq_sound _ _ rawSame,closed,closedLambdaCheck_sound closed⟩
          else .error .closed
        else .error .selection
      else .error .selection
    else .error .selection

def HigherSelection.s13 {r : ReaderSelection s} (h : HigherSelection r) : CoreMachine.State := {r.s12 with
  control := .evaluate h.functionSite r.installedEnvironment,
  frames := .bind h.binder.id h.tailSite r.installedEnvironment :: r.s12.frames,
  observations := r.s12.observations ++ [.entered r.tailSite]}
def HigherSelection.s14 {r : ReaderSelection s} (h : HigherSelection r) : CoreMachine.State := {h.s13 with
  control := .returned (.closure h.parameter.id h.functionBody r.installedEnvironment),
  observations := h.s13.observations ++ [.entered h.functionSite]}
def HigherSelection.environment {r : ReaderSelection s} (h : HigherSelection r) : Environment :=
  .binding h.binder.id (.closure h.parameter.id h.functionBody r.installedEnvironment) r.installedEnvironment
def HigherSelection.s15 {r : ReaderSelection s} (h : HigherSelection r) : CoreMachine.State := {h.s14 with
  control := .evaluate h.tailSite h.environment,frames := r.s12.frames}
def HigherSelection.p13 {r : ReaderSelection s} (h : HigherSelection r) : CoreInitialPrefix.Point :=
  ⟨h.s13,r.p12.target,[],([], .bind h.binder.id h.tailSite r.installedEnvironment)::r.p12.annotations⟩
def HigherSelection.p14 {r : ReaderSelection s} (h : HigherSelection r) : CoreInitialPrefix.Point :=
  ⟨h.s14,r.p12.target,[],h.p13.annotations⟩
def HigherSelection.p15 {r : ReaderSelection s} (h : HigherSelection r) : CoreInitialPrefix.Point :=
  ⟨h.s15,⟨h.suffix.subst h.binder.id h.initializer,.none,r.p12.target.stack⟩,[],r.p12.annotations⟩

theorem higher_chain {r : ReaderSelection s} (h : HigherSelection r)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode)
    (reader : CheckedReader r) (higher : CheckedHigher h) :
    Chain graph r.p12 [h.p13,h.p14,h.p15] h.p15 ∧
    EnvCloses graph [] [] h.environment h.rawTail (h.suffix.subst h.binder.id h.initializer) := by
  have certificates := checkAmbient_certificate higher.accepted
  rw [higher.parameterSame,higher.bodySame,higher.rawSame] at certificates
  have closing := (reader_chain s r input reader).2
  rw [h.rawSame,h.body_exact] at closing
  have tail : PushedWithMaps graph [] r.p12.annotations r.p12.target.stack :=
    .boundary (.cell s.resourceKnown s.resourceKind) .nil
  have produced := CoreReadyBindings.lambda_binding_mapped (base := r.s12)
    (ordered := CoreTranslationFuel.checkShape_postorder graph input.shape)
    h.known h.kind h.functionKnown h.functionKind h.functionTranslated h.tailTranslated
    certificates.2 rfl certificates.1 closing higher.closed h.ready h.plain rfl tail
  simpa [HigherSelection.p13,HigherSelection.p14,HigherSelection.p15,HigherSelection.s13,
    HigherSelection.s14,HigherSelection.s15,HigherSelection.environment,HigherSelection.plain,
    ReaderSelection.p12,ReaderSelection.s12,ReaderSelection.s11,ReaderSelection.s10,
    Selection.s9,Selection.s8,Selection.s7,Selection.s6,Selection.s5,Selection.s4,Selection.s3,
    Selection.s2,Selection.s1,Selection.s0,CoreMachine.initial,framesOf,h.body_exact] using ⟨produced.1,produced.2.1⟩

noncomputable def higher_current {r : ReaderSelection s} (h : HigherSelection r) : Endpoint graph where
  state := h.s15
  focus := ⟨h.suffix.subst h.binder.id h.initializer,.none,.nil⟩
  owners := []; maps := []
  physical := r.s12.frames
  lexical := (current r).lexical
  history := installed_history s r
  frames := rfl

theorem higher_current_point {r : ReaderSelection s} (h : HigherSelection r) :
    (higher_current h).point.state = h.p15.state ∧
    (higher_current h).point.machine = .eval h.p15.target := ⟨rfl,rfl⟩

theorem higher_value {r : ReaderSelection s} (h : HigherSelection r)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode)
    (reader : CheckedReader r) (higher : CheckedHigher h) :
    ValueRel graph [] [] (.closure h.parameter.id h.functionBody r.installedEnvironment) h.initializer := by
  have certificates := checkAmbient_certificate higher.accepted
  rw [higher.parameterSame,higher.bodySame,higher.rawSame] at certificates
  have closing := (reader_chain s r input reader).2
  rw [h.rawSame,h.body_exact] at closing
  exact .closure certificates.2 certificates.1 (bind_components closing).1 higher.closed

/-- Literal output evidence is recovered from its actual current lexical
lookup, not an independently chosen returned value. -/
theorem variable_output {before : Endpoint graph} (input : LiteralInput before)
    (known : graph.node input.index = some node) (kind : node.kind = .variable name)
    (saved : EnvCloses graph before.owners before.state.heap input.environment (.variable name) input.code)
    (closed : ClosedValue input.code) :
    ∃ value, input.environment.lookup name = some value ∧
      (literal_result input).after.state.control = .returned value ∧
      ValueRel graph before.owners before.state.heap value input.code := by
  obtain ⟨value,lookup,related⟩ := saved.lookup closed
  have actual : CoreMachine.next graph before.state = .stepped
      {before.state with control := .returned value, observations := before.state.observations ++ [.entered input.index]} := by
    simp [CoreMachine.next,input.control,known,kind,lookup]
  have same := CoreMachine.Outcome.stepped.inj ((literal_result input).core.symm.trans actual)
  exact ⟨value,lookup,congrArg CoreMachine.State.control same,related⟩

private theorem link_step {graph : Graph} {before after : CoreInitialPrefix.Point}
    (link : Link graph before after) : CoreMachine.Step graph before.state after.state := by
  cases link with
  | positive _ core _ _ => exact core
  | traversal witness => exact witness.core
  | value witness => exact witness.core

private theorem chain_steps {graph : Graph} (chain : Chain graph before points after) :
    CoreAllocationHistory.Steps graph points.length before.state after.state := by
  induction chain with
  | last link => exact .snoc (.refl _) (link_step link)
  | next link rest ih =>
    simpa [Nat.add_comm] using (CoreAllocationHistory.Steps.snoc (.refl _) (link_step link)).trans ih

private theorem raw_trace (positive : CoreInitialPrefix.Positive before after) :
    ∃ created discharged, CoreUnwindRelation.Trace (.eval before) (.eval after) created discharged := by
  induction positive with
  | one step allowed => exact ⟨_,_,.next (.evaluate step allowed) (.refl _)⟩
  | next step rest allowed ih =>
    obtain ⟨created,discharged,later⟩ := ih
    exact ⟨_,_,.next (.evaluate step allowed) later⟩

private theorem chain_trace {graph : Graph} (chain : Chain graph before points after) :
    ∃ created discharged, CoreUnwindRelation.Trace (.eval before.target) (.eval after.target) created discharged := by
  have linkTrace : ∀ {first last : CoreInitialPrefix.Point}, Link graph first last →
      ∃ created discharged, CoreUnwindRelation.Trace (.eval first.target) (.eval last.target) created discharged := by
    intro first last link
    cases link with
    | positive _ core positive _ => exact raw_trace positive
    | traversal _ => exact ⟨[],[],.refl _⟩
    | value _ => exact ⟨[],[],.refl _⟩
  induction chain with
  | last link => exact linkTrace link
  | next link rest ih =>
    obtain ⟨created,discharged,first⟩ := linkTrace link
    obtain ⟨laterCreated,laterDischarged,later⟩ := ih
    exact ⟨_,_,first.append later⟩

theorem segment_target {graph : Graph} {first last : Endpoint graph}
    (segment : CoreCallableInitialChronology.OperationSegment first last count created discharged) :
    CoreUnwindRelation.Trace first.point.machine last.point.machine created discharged := by
  induction segment with
  | initial => exact .refl _
  | next earlier operation ih => exact ih.append operation.actual.2.target_trace

namespace Original
open ComposedResourceRuntimeOriginProbes
def higherFunction : Code := .app (.variable 11) .unit
def higherTail : Code := match rawTail with | .bind _ _ body => body | _ => .unit
def selectedHigher : HigherSelection reader where
  binder := ⟨13,CoreCallableCompositionalResourceRoot.higherType⟩
  parameter := ⟨11,CoreCallableCompositionalResourceRoot.readerType⟩
  binderType := rfl
  functionSite := 10
  functionBody := 9
  tailSite := 18
  node := CoreTranslation.Examples.node 19 (.bind ⟨13,CoreCallableCompositionalResourceRoot.higherType⟩ 10 18) .integer
  functionNode := CoreTranslation.Examples.node 10 (.function ⟨11,CoreCallableCompositionalResourceRoot.readerType⟩ 9) CoreCallableCompositionalResourceRoot.higherType
  rawFunction := higherFunction
  rawTail := higherTail
  fuel := 24
  known := rfl
  kind := rfl
  functionKnown := rfl
  functionKind := rfl
  functionTranslated := rfl
  tailTranslated := rfl
  rawSame := rfl
  binderOuter := by decide
  binderHandle := by decide
  binderReader := by decide
  parameterOuter := by decide
  parameterHandle := by decide
  parameterReader := by decide
  ready := by
    intro name member
    change Syntax.Dependency.variable name ∈ [.variable 13,.resource 0,.resource 0] at member
    simpa using member
  noTicket := rfl

theorem higher_executed : ∃ checked, produce_higher selectedHigher = .ok checked := ⟨_,rfl⟩
noncomputable def checkedHigher := Classical.choose higher_executed

theorem reader_to_higher : CoreInitialPrefix.Chain CoreCallableCompositionalResourceRoot.graph reader.p12
    [selectedHigher.p13,selectedHigher.p14,selectedHigher.p15] selectedHigher.p15 :=
  (higher_chain selectedHigher initialInput checkedReader checkedHigher).1

open CoreCallableGeneratedBindProducers
abbrev G := CoreCallableCompositionalResourceRoot.graph
noncomputable def e15 : Endpoint G := higher_current selectedHigher
abbrev branchCode : Code := .branch (.boolean true) (.integer 17) (.integer 17)

noncomputable def bindReady : BindReady e15 where
  site := 18
  binder := ⟨5,.integer⟩
  initializer := 13
  body := 17
  environment := selectedHigher.environment
  plain := ⟨.bind 5 branchCode,.none,.integer,.integer,[],rfl⟩
  node := CoreTranslation.Examples.node 18 (.bind ⟨5,.integer⟩ 13 17) .integer
  known := rfl
  kind := rfl
  fuel := 24
  rawInitializer := .app (.variable 13) (.variable 12)
  rawBody := .branch (.boolean true) (.variable 7) (.variable 7)
  initializerCode := .app selectedHigher.initializer reader.initializer
  suffix := branchCode
  initializerTranslated := rfl
  bodyTranslated := rfl
  closing := (higher_chain selectedHigher initialInput checkedReader checkedHigher).2
  notValue := by simp [Code.IsValue]
  closed := by intro name member; cases member
  context := rfl
  control := rfl
  empty := ⟨rfl,rfl⟩

noncomputable def bindInput : BindInput e15 :=
  bind_from_current_origins (CoreTranslationFuel.checkShape_postorder G initialInput.shape)
    ⟨.empty G,(by intro mapped member; cases member),.inactive (.empty G),(by intro mapped member; cases member)⟩
    ⟨.inactive (.empty G),(by intro mapped member; cases member)⟩ bindReady
noncomputable def e16 : Endpoint G := (bind_result bindInput).after

theorem bind_codes : bindInput.past.contextCode = .app selectedHigher.initializer reader.initializer ∧
    bindInput.past.suffixCode = branchCode := by
  have shape := congrArg Configuration.expression bindInput.empty.focus
  change Code.bind 5 (.app selectedHigher.initializer reader.initializer) branchCode =
    Code.bind 5 bindInput.past.contextCode bindInput.past.suffixCode at shape
  exact ⟨(Code.bind.inj shape).2.1.symm,(Code.bind.inj shape).2.2.symm⟩

theorem e16_focus : e16.focus = ⟨.app selectedHigher.initializer reader.initializer,.none,.nil⟩ := by
  change (⟨bindInput.past.contextCode,.none,.nil⟩ : Configuration) = _
  rw [bind_codes.1]

theorem bind_initializer : bindInput.past.initializer = 13 := by
  have site : bindInput.past.site = 18 := (CoreMachine.Control.evaluate.inj bindInput.control.symm).1
  have known := bindInput.past.known
  rw [site] at known
  have nodeSame : bindInput.past.node = bindReady.node := Option.some.inj (known.symm.trans bindReady.known)
  have kind := bindInput.past.kind
  rw [nodeSame,bindReady.kind] at kind
  exact (CoreSyntax.Kind.bind.inj kind).2.1.symm

theorem e16_control : e16.state.control = .evaluate 13 selectedHigher.environment := by
  change CoreMachine.Control.evaluate bindInput.past.initializer selectedHigher.environment = _
  rw [bind_initializer]

noncomputable def outerEntry : EntryInput e16 where
  ordered := CoreTranslationFuel.checkShape_postorder G initialInput.shape
  site := 13
  environment := selectedHigher.environment
  node := CoreTranslation.Examples.node 13 (.apply 11 12) .integer
  known := rfl
  nextIndex := 11
  frame := .applyFunction 12 selectedHigher.environment
  kind := .application rfl
  environmentSame := rfl
  control := e16_control
  maps := rfl
  stack := rfl
  interpreted := by
    rw [e16_control,e16_focus]
    exact .evaluate (fuel := 24) (by rfl) (bind_components bindReady.closing).1
noncomputable def e17 : Endpoint G := (entry_result outerEntry).after

theorem outer_saved : EnvCloses G [] [] selectedHigher.environment (.variable 13) selectedHigher.initializer ∧
    EnvCloses G [] [] selectedHigher.environment (.variable 12) reader.initializer :=
  ((bind_components bindReady.closing).1).app_components

def outerFunctionPlain : PlainData :=
  ⟨.appFunction reader.initializer,.none,selectedHigher.plain.input,.integer,[],rfl⟩

noncomputable def outerFunction : LiteralInput e17 where
  index := 11
  environment := selectedHigher.environment
  code := selectedHigher.initializer
  scope := .none
  literal := .lexicalVariable rfl rfl outer_saved.1 checkedHigher.closed
  control := rfl
  stack := by
    rw [show e17.focus = e16.focus from rfl,e16_focus]
    exact ⟨[([],.applyFunction 12 selectedHigher.environment)],[],rfl,
      .cons (plain := outerFunctionPlain) (by exact FrameRel.applyFunction (argument := 12) (fuel := 24) (by rfl) outer_saved.2) checkedHigher.closed .nil,.nil⟩
noncomputable def e18 : Endpoint G := (literal_result outerFunction).after

theorem outer_function_control : e18.state.control =
    .returned (.closure 11 9 reader.installedEnvironment) := by
  obtain ⟨value,lookup,control,_related⟩ := variable_output outerFunction rfl rfl outer_saved.1 checkedHigher.closed
  have same : value = .closure 11 9 reader.installedEnvironment := by
    simpa [HigherSelection.environment,Environment.lookup,selectedHigher] using Option.some.inj lookup.symm
  rw [same] at control
  exact control

theorem higher_runtime_value : ValueRel G [] [] (.closure 11 9 reader.installedEnvironment) selectedHigher.initializer :=
  higher_value selectedHigher initialInput checkedReader checkedHigher

noncomputable def outerSwap : SwapInput e18 where
  frameOwners := []
  beforeFrame := .applyFunction 12 selectedHigher.environment
  afterFrame := .applyArgument (.closure 11 9 reader.installedEnvironment)
  kind := .application
  value := .closure 11 9 reader.installedEnvironment
  nextIndex := 12
  environment := selectedHigher.environment
  frameBefore := Or.inl rfl
  frameAfter := Or.inl rfl
  code := selectedHigher.initializer
  related := higher_runtime_value
  interpreted := by
    refine ⟨rfl,selectedHigher.initializer,.none,?_,?_⟩
    · change ControlRel G [] [] e18.state.control selectedHigher.initializer
      rw [outer_function_control]
      exact .returned higher_runtime_value
    · change OrdinaryWithMaps G [] [([],.applyFunction 12 selectedHigher.environment)] selectedHigher.initializer .none
        e16.focus.expression e16.focus.scope e16.focus.stack
      simpa only [outerFunction,show e17.state.heap = [] from rfl,
        show e17.maps = [([],.applyFunction 12 selectedHigher.environment)] from rfl,
        show e17.focus = e16.focus from rfl,e16_focus] using outerFunction.stack
  control := outer_function_control
  maps := rfl
noncomputable def e19 : Endpoint G := (swap_result outerSwap).after

def outerArgumentPlain : PlainData :=
  ⟨.appArgument selectedHigher.initializer,.none,reader.inputType,.integer,[],rfl⟩
noncomputable def outerArgument : LiteralInput e19 where
  index := 12
  environment := selectedHigher.environment
  code := reader.initializer
  scope := .none
  literal := .lexicalVariable rfl rfl outer_saved.2 checkedReader.closed
  control := rfl
  stack := by
    change OrdinaryWithMaps G [] [([],.applyArgument (.closure 11 9 reader.installedEnvironment))] reader.initializer .none
      e16.focus.expression e16.focus.scope e16.focus.stack
    rw [e16_focus]
    exact ⟨[([],.applyArgument (.closure 11 9 reader.installedEnvironment))],[],rfl,
      .cons (plain := outerArgumentPlain) (.applyArgument higher_runtime_value) checkedReader.closed .nil,.nil⟩
noncomputable def e20 : Endpoint G := (literal_result outerArgument).after

theorem outer_argument_control : e20.state.control = .returned (.closure 10 5 selection.acquiredEnvironment) := by
  obtain ⟨value,lookup,control,_related⟩ := variable_output outerArgument rfl rfl outer_saved.2 checkedReader.closed
  have same : value = .closure 10 5 selection.acquiredEnvironment := by
    simpa [HigherSelection.environment,Environment.lookup,selectedHigher,
      ReaderSelection.installedEnvironment,reader] using Option.some.inj lookup.symm
  rw [same] at control
  exact control

noncomputable def outerBeta : BetaInput e20 where
  frameOwners := []
  parameter := 11
  body := 9
  environment := reader.installedEnvironment
  value := .closure 10 5 selection.acquiredEnvironment
  argument := reader.initializer
  bodyCode := selectedHigher.closedBody
  scope := .none
  function := higher_runtime_value
  operand := exact_closure_value
  control := outer_argument_control
  maps := rfl
  focus := by change e16.focus = _; exact e16_focus
noncomputable def e21 : Endpoint G := (beta_result outerBeta).after

abbrev higherBodyEnvironment : Environment :=
  .binding 11 (.closure 10 5 selection.acquiredEnvironment) reader.installedEnvironment

theorem first_beta_environment : e21.state.control = .evaluate 9 higherBodyEnvironment := rfl

theorem first_beta_closing : EnvCloses G [] [] higherBodyEnvironment
    (.app (.variable 11) .unit) (.app reader.initializer .unit) := by
  have certificate := checkAmbient_certificate checkedHigher.accepted
  rw [checkedHigher.parameterSame,checkedHigher.bodySame,checkedHigher.rawSame] at certificate
  have closing := (reader_chain selection reader initialInput checkedReader).2
  rw [selectedHigher.rawSame,selectedHigher.body_exact] at closing
  exact (bind_components closing).1.beta_argument exact_closure_value

noncomputable def innerEntry : EntryInput e21 where
  ordered := CoreTranslationFuel.checkShape_postorder G initialInput.shape
  site := 9
  environment := higherBodyEnvironment
  node := CoreTranslation.Examples.node 9 (.apply 7 8) .integer
  known := rfl
  nextIndex := 7
  frame := .applyFunction 8 higherBodyEnvironment
  kind := .application rfl
  environmentSame := rfl
  control := rfl
  maps := rfl
  stack := rfl
  interpreted := .evaluate (fuel := 24) (by rfl) first_beta_closing
noncomputable def e22 : Endpoint G := (entry_result innerEntry).after

def innerFunctionPlain : PlainData := ⟨.appFunction .unit,.none,reader.inputType,.integer,[],rfl⟩
noncomputable def innerFunction : LiteralInput e22 where
  index := 7
  environment := higherBodyEnvironment
  code := reader.initializer
  scope := .none
  literal := .lexicalVariable rfl rfl first_beta_closing.app_components.1 checkedReader.closed
  control := rfl
  stack := ⟨[([],.applyFunction 8 higherBodyEnvironment)],[],rfl,
    .cons (plain := innerFunctionPlain) (.applyFunction (fuel := 24) (by rfl) first_beta_closing.app_components.2)
      checkedReader.closed .nil,.nil⟩
noncomputable def e23 : Endpoint G := (literal_result innerFunction).after

theorem inner_function_control : e23.state.control = .returned (.closure 10 5 selection.acquiredEnvironment) := by
  obtain ⟨value,lookup,control,_⟩ := variable_output innerFunction rfl rfl first_beta_closing.app_components.1 checkedReader.closed
  have same : value = .closure 10 5 selection.acquiredEnvironment := Option.some.inj lookup.symm
  rw [same] at control
  exact control

noncomputable def innerSwap : SwapInput e23 where
  frameOwners := []
  beforeFrame := .applyFunction 8 higherBodyEnvironment
  afterFrame := .applyArgument (.closure 10 5 selection.acquiredEnvironment)
  kind := .application
  value := .closure 10 5 selection.acquiredEnvironment
  nextIndex := 8
  environment := higherBodyEnvironment
  frameBefore := Or.inl rfl
  frameAfter := Or.inl rfl
  code := reader.initializer
  related := exact_closure_value
  interpreted := by
    refine ⟨rfl,reader.initializer,.none,?_,?_⟩
    · change ControlRel G [] [] e23.state.control reader.initializer
      rw [inner_function_control]
      exact .returned exact_closure_value
    · exact innerFunction.stack
  control := inner_function_control
  maps := rfl
noncomputable def e24 : Endpoint G := (swap_result innerSwap).after

def innerArgumentPlain : PlainData := ⟨.appArgument reader.initializer,.none,.unit,.integer,[],rfl⟩
noncomputable def innerArgument : LiteralInput e24 where
  index := 8
  environment := higherBodyEnvironment
  code := .unit
  scope := .none
  literal := .unit rfl rfl first_beta_closing.app_components.2
  control := rfl
  stack := ⟨[([],.applyArgument (.closure 10 5 selection.acquiredEnvironment))],[],rfl,
    .cons (plain := innerArgumentPlain) (.applyArgument exact_closure_value) (ValueRel.unit (graph := G) (owners := []) (heap := [])).closed .nil,.nil⟩
noncomputable def e25 : Endpoint G := (literal_result innerArgument).after

theorem inner_argument_control : e25.state.control = .returned .unit := by
  have actual : CoreMachine.next G e24.state = .stepped
      {e24.state with control := .returned .unit,observations := e24.state.observations ++ [.entered 8]} := rfl
  exact congrArg CoreMachine.State.control (CoreMachine.Outcome.stepped.inj
    ((literal_result innerArgument).core.symm.trans actual))

noncomputable def innerBeta : BetaInput e25 where
  frameOwners := []
  parameter := 10
  body := 5
  environment := selection.acquiredEnvironment
  value := .unit
  argument := .unit
  bodyCode := reader.closedBody
  scope := .none
  function := exact_closure_value
  operand := .unit
  control := inner_argument_control
  maps := rfl
  focus := rfl
noncomputable def e26 : Endpoint G := (beta_result innerBeta).after

abbrev readerBodyEnvironment : Environment := .binding 10 .unit selection.acquiredEnvironment

theorem second_beta_environment : e26.state.control = .evaluate 5 readerBodyEnvironment := rfl

theorem second_beta_closing : EnvCloses G [] [] readerBodyEnvironment
    (.perform (.cell (.bound 3)) 0 (.variable 9)) (.perform (.cell (.activation 0)) 0 (.resourceRef (.activation 0))) :=
  (reader_closing selection reader initialInput).beta_argument ValueRel.unit

theorem callee_saved_environment_differs : readerBodyEnvironment ≠ selectedHigher.environment := by
  intro impossible
  have names := Environment.binding.inj impossible
  cases names.1

open CoreRequestFrames CoreCellWriteFrames CoreCaptureEntry CoreCellSteps
noncomputable def requestEntry : EntryInput e26 where
  ordered := CoreTranslationFuel.checkShape_postorder G initialInput.shape
  site := 5
  environment := readerBodyEnvironment
  node := CoreTranslation.Examples.node 5 (.request (.cell (.bound 3)) 0 4) .integer
  known := rfl
  nextIndex := 4
  frame := .request (.cell (.bound 3)) 0 readerBodyEnvironment
  kind := .request rfl
  environmentSame := rfl
  control := rfl
  maps := rfl
  stack := rfl
  interpreted := .evaluate (fuel := 24) (by rfl) second_beta_closing
noncomputable def e27 : Endpoint G := (entry_result requestEntry).after

def requestPlain : PlainData := ⟨.perform (.cell (.activation 0)) 0,.none,.reference 0,.integer,[],rfl⟩
theorem request_carrier : RequestRel G [] [] (.request (.cell (.bound 3)) 0 readerBodyEnvironment) requestPlain :=
  .operand (requested := .cell 0) (perform_header_at second_beta_closing
    (.cell (.bound 3)) 0 (.variable 9) (.cell (.activation 0)) (.resourceRef (.activation 0)) rfl rfl) rfl

theorem handle_closing : EnvCloses G [] [] readerBodyEnvironment (.variable 9) (.resourceRef (.activation 0)) :=
  (perform_components second_beta_closing).2

noncomputable def requestOperand : LiteralInput e27 where
  index := 4
  environment := readerBodyEnvironment
  code := .resourceRef (.activation 0)
  scope := .none
  literal := .lexicalVariable rfl rfl handle_closing (ValueRel.handle (graph := G) (owners := []) (heap := [])).closed
  control := rfl
  stack := ⟨[([],.request (.cell (.bound 3)) 0 readerBodyEnvironment)],[],rfl,
    .request request_carrier (ValueRel.handle (graph := G) (owners := []) (heap := [])).closed .nil,.nil⟩
noncomputable def e28 : Endpoint G := (literal_result requestOperand).after

theorem request_operand_control : e28.state.control = .returned (.handle 0) := by
  obtain ⟨value,lookup,control,_⟩ := variable_output requestOperand rfl rfl handle_closing
    (ValueRel.handle (graph := G) (owners := []) (heap := [])).closed
  have same : value = .handle 0 := Option.some.inj lookup.symm
  rw [same] at control
  exact control

/-- Nearest original bind5/cell0 cut is constructed from the saved installed
bind receipt and original resource declaration, not accepted as an input. -/
theorem read_cut : WriteCut G [] 0 0 0
    [([],.bind 5 17 selectedHigher.environment),([],.resourceBoundary 21 0 0)] e28.lexical
    [([],.bind 5 17 selectedHigher.environment),([],.resourceBoundary 21 0 0)] e28.lexical :=
  .push (.ordinary (by
      have frame := bindInput.past.saved.saved.related
      rw [bindInput.predecessor] at frame
      exact frame)) (by
        change (bindReady.plain.erase.target ≠ some (.cell 0))
        simp [PlainData.erase,Frame.target,bindReady])
    (.hit selection.resourceKnown selection.resourceKind .nil)

noncomputable def e29 : Endpoint G where
  state := readAfter e28.state 0 0 [([],.bind 5 17 selectedHigher.environment),([],.resourceBoundary 21 0 0)]
  focus := ⟨.integer 0,.none,.nil⟩
  owners := []; maps := []
  physical := e28.physical
  lexical := e28.lexical
  history := e28.history
  frames := rfl

theorem read_actual : CoreMachine.next G e28.state = .stepped e29.state ∧
    CoreUnwindRelation.Positive e28.point.machine e29.point.machine [] [] := by
  have actual := CoreCellSteps.read_complete (base := e28.state) request_carrier rfl
    (ValueRel.handle (graph := G) (owners := []) (heap := [])) read_cut Execution.Scope.none
  have before : requestBefore e28.state (.cell (.bound 3)) 0 readerBodyEnvironment (.handle 0)
      [([],.bind 5 17 selectedHigher.environment),([],.resourceBoundary 21 0 0)] = e28.state := by
    unfold requestBefore
    rw [← request_operand_control]
    rfl
  refine ⟨?_,?_⟩
  · change CoreMachine.next G e28.state = .stepped
      (readAfter e28.state 0 0 [([],.bind 5 17 selectedHigher.environment),([],.resourceBoundary 21 0 0)])
    simpa only [before] using actual.2.1
  · exact .one actual.2.2.1

theorem read_observation : e29.state.observations = e28.state.observations ++ [.read 0 0] := rfl

theorem read_history : CoreGeneralStack.GeneralSegment G e29.state.heap e29.physical e29.lexical :=
  e29.history.related

/-- The literal original suffix uses only existing causal Operation constructors. -/
noncomputable def calls_segment : CoreCallableInitialChronology.OperationSegment e15 e28 13 [] [] :=
  .next (.next (.next (.next (.next (.next (.next (.next (.next (.next (.next (.next (.next .initial
    (.bind bindInput)) (.entry outerEntry)) (.literal outerFunction)) (.swap outerSwap))
    (.literal outerArgument)) (.beta outerBeta)) (.entry innerEntry)) (.literal innerFunction))
    (.swap innerSwap)) (.literal innerArgument)) (.beta innerBeta)) (.entry requestEntry)) (.literal requestOperand)

theorem initial_to_higher : CoreAllocationHistory.Steps G 15 (CoreMachine.initial G) e15.state := by
  exact initial_to_reader.trans (chain_steps reader_to_higher)

theorem initial_to_read : CoreAllocationHistory.Steps G 29 (CoreMachine.initial G) e29.state :=
  .snoc (initial_to_higher.trans calls_segment.actual_steps) read_actual.1

theorem call_target_trace : CoreUnwindRelation.Trace e15.point.machine e29.point.machine [] [] :=
  (segment_target calls_segment).append read_actual.2.trace

/-- Positive/ranked matching from the SAME actual initial target. Owner lists
are produced by the inherited Raw links, never a requested trace premise. -/
theorem initial_target_trace : ∃ created discharged,
    CoreUnwindRelation.Trace (.eval selection.p0.target) e29.point.machine created discharged := by
  obtain ⟨created,discharged,first⟩ := chain_trace
    (installed_chain selection reader initialInput checkedReader)
  obtain ⟨laterCreated,laterDischarged,later⟩ := chain_trace reader_to_higher
  have final := call_target_trace
  exact ⟨_,_,(first.append later).append final⟩

theorem read_ticket_bound : CoreCallableReachableResume.TicketBound e29.state e29.lexical := by
  intro ticket
  change List.count ticket ((Stack.push (.plain bindReady.plain)
    (.push (.cell 0 0 .none .integer) .nil)).erase.ticketNames) ≤ _
  simp [Stack.erase,ExecFrame.erase,PlainData.erase,Control.ticketNames,bindReady,branchCode]

theorem read_current_sites : SiteOrigins e29 := by
  refine ⟨.empty G,?_,True.intro,?_⟩
  · intro mapped member; cases member
  · intro mapped member; cases member

theorem read_current_scopes : EvaluatedScopeOrigins e29 := by
  refine ⟨True.intro,?_⟩
  intro mapped member; cases member

theorem original_owner_ledger : selection.s8.nextActivation = 0 ∧ e29.state.nextActivation = 1 ∧
    CoreAllocationHistory.History e29.state :=
  ⟨rfl,rfl,CoreAllocationHistory.initial_steps_history G initial_to_read⟩

theorem read_result : e29.state.control = .returned (.integer 0) ∧
    e29.physical = [.bind 5 17 selectedHigher.environment,.resourceBoundary 21 0 0] := ⟨rfl,rfl⟩

open CoreCallableComposedResourceOrigins CoreCallableComposedResourceOrigins.Probes
open CoreCallableCapturedLambdaConstructor
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Full constructor provenance and its exact storage indices remain coupled
with the actual higher closure. The complete Current receipt is retained. -/
def HigherJoined {resource : Opened} (path : HigherPath resource)
    (receipt : Current path.path selection.s8.nextActivation (by simp)) : Prop :=
  CoreCallableGraphAnnotationChecks.typeB
      (Instantiation.Environment.empty.bind 3 selection.s8.nextActivation) selectedHigher.binder.type
      (CoreCallableCompositionalResourceRoot.higherPattern.value [(7,.integer)] selection.s8.nextActivation) = true ∧
  ∃ family, Origin receipt.source family ∧ family.Authentic ∧
    ValueRel G [] [] (.closure 11 9 reader.installedEnvironment) (.lambda 11 (.app (.variable 11) .unit)) ∧
    CallableContracts.Derives CoreCallableComposedResourceOrigins.Probes.Original.declarations
      (CoreCallableReturnStorageProducer.environment
        (CoreCallableCompositionalResourceStorage.realize selection.s8.nextActivation higherStorage))
      [selection.s8.nextActivation] .none (.lambda 11 (.app (.variable 11) .unit))
      (path.stored.value selection.s8.nextActivation)

noncomputable def join_higher {resource : Opened} (path : HigherPath resource)
    (receipt : Current path.path selection.s8.nextActivation (by simp)) :
    Except CoreCallableComposedRuntimeBindings.Error (PLift (HigherJoined path receipt)) :=
  if codeSame : codeEq selectedHigher.initializer
      ((CoreCallableCompositionalResourceRoot.codeOf CoreCallableCompositionalResourceRoot.higherOrder).instantiate
        (Instantiation.Environment.empty.bind 3 selection.s8.nextActivation)) = true then
    if typeSame : CoreCallableGraphAnnotationChecks.typeB
        (Instantiation.Environment.empty.bind 3 selection.s8.nextActivation) selectedHigher.binder.type
        (CoreCallableCompositionalResourceRoot.higherPattern.value [(7,.integer)] selection.s8.nextActivation) = true then
      .ok ⟨by
        obtain ⟨family,origin,auth,_known⟩ := CoreCallableCapturedLambdaConstructor.extract receipt.authenticated
        refine ⟨typeSame,family,origin,auth,?_,receipt.storage⟩
        have same := codeEq_sound _ _ codeSame
        have related := higher_runtime_value
        rw [same] at related
        exact related⟩
    else .error .selection
  else .error .selection

theorem join_higher_executed {resource : Opened} (path : HigherPath resource)
    (receipt : Current path.path selection.s8.nextActivation (by simp)) :
    ∃ joined, join_higher path receipt = .ok joined := by
  unfold join_higher
  rw [dif_pos (show codeEq selectedHigher.initializer _ = true from rfl)]
  rw [dif_pos (show CoreCallableGraphAnnotationChecks.typeB _ selectedHigher.binder.type _ = true from rfl)]
  exact ⟨_,rfl⟩

open CoreCallableComposedCapturedHandle

/-- Executed constructor receipts determine the actual beta operand proofs.
The entire reader/higher provenance remains indexed in this output. -/
structure CheckedCall {resource : Opened} (staticReader : ReaderPath resource)
    (readerReceipt : Current staticReader.path selection.s8.nextActivation (by simp))
    (handleReceipt : CapturedHandle staticReader.path selection.s8.nextActivation (by simp))
    (staticHigher : HigherPath resource)
    (higherReceipt : Current staticHigher.path selection.s8.nextActivation (by simp)) where
  readerJoined : PairedReader reader readerReceipt handleReceipt
  higherJoined : HigherJoined staticHigher higherReceipt
  outer : BetaInput e20
  inner : BetaInput e25
  outerSame : outer = outerBeta
  innerSame : inner = innerBeta

noncomputable def check_call {resource : Opened} (staticReader : ReaderPath resource)
    (readerReceipt : Current staticReader.path selection.s8.nextActivation (by simp))
    (handleReceipt : CapturedHandle staticReader.path selection.s8.nextActivation (by simp))
    (staticHigher : HigherPath resource)
    (higherReceipt : Current staticHigher.path selection.s8.nextActivation (by simp)) :
    Except CoreCallableComposedRuntimeBindings.Error
      (CheckedCall staticReader readerReceipt handleReceipt staticHigher higherReceipt) := do
  let paired ← pair_reader reader initialInput checkedReader readerReceipt handleReceipt
  let higher ← join_higher staticHigher higherReceipt
  have readerRelated : ValueRel G [] [] (.closure 10 5 selection.acquiredEnvironment) reader.initializer := by
    obtain ⟨_root,_type,nextCode,family,replacement,origin,same,auth,lower,related⟩ := paired.down
    rw [same] at related
    exact related
  have higherRelated : ValueRel G [] [] (.closure 11 9 reader.installedEnvironment) selectedHigher.initializer := by
    obtain ⟨_type,family,origin,auth,related,lower⟩ := higher.down
    exact related
  .ok ⟨paired.down,higher.down,{outerBeta with function := higherRelated,operand := readerRelated},
    {innerBeta with function := readerRelated},rfl,rfl⟩

theorem check_call_executed {resource : Opened} (staticReader : ReaderPath resource)
    (readerReceipt : Current staticReader.path selection.s8.nextActivation (by simp))
    (handleReceipt : CapturedHandle staticReader.path selection.s8.nextActivation (by simp))
    (staticHigher : HigherPath resource)
    (higherReceipt : Current staticHigher.path selection.s8.nextActivation (by simp)) :
    ∃ checked, check_call staticReader readerReceipt handleReceipt staticHigher higherReceipt = .ok checked := by
  obtain ⟨paired,pairAccepted⟩ := pair_reader_success reader initialInput checkedReader readerReceipt handleReceipt rfl rfl rfl
  obtain ⟨higher,higherAccepted⟩ := join_higher_executed staticHigher higherReceipt
  unfold check_call
  rw [pairAccepted]
  simp only [Bind.bind,Except.bind]
  rw [higherAccepted]
  exact ⟨_,rfl⟩

theorem checked_beta_endpoints {resource : Opened} {staticReader : ReaderPath resource}
    {readerReceipt : Current staticReader.path selection.s8.nextActivation (by simp)}
    {handleReceipt : CapturedHandle staticReader.path selection.s8.nextActivation (by simp)}
    {staticHigher : HigherPath resource}
    {higherReceipt : Current staticHigher.path selection.s8.nextActivation (by simp)}
    (checked : CheckedCall staticReader readerReceipt handleReceipt staticHigher higherReceipt) :
    (beta_result checked.outer).after = e21 ∧ (beta_result checked.inner).after = e26 := by
  rw [checked.outerSame,checked.innerSame]
  exact ⟨rfl,rfl⟩

theorem checked_call_actual {resource : Opened} {staticReader : ReaderPath resource}
    {readerReceipt : Current staticReader.path selection.s8.nextActivation (by simp)}
    {handleReceipt : CapturedHandle staticReader.path selection.s8.nextActivation (by simp)}
    {staticHigher : HigherPath resource}
    {higherReceipt : Current staticHigher.path selection.s8.nextActivation (by simp)}
    (checked : CheckedCall staticReader readerReceipt handleReceipt staticHigher higherReceipt) :
    CoreMachine.next G e20.state = .stepped e21.state ∧
    CoreMachine.next G e25.state = .stepped e26.state := by
  have outer := (Operation.actual (.beta checked.outer)).1
  have inner := (Operation.actual (.beta checked.inner)).1
  rw [(checked_beta_endpoints checked).1] at outer
  rw [(checked_beta_endpoints checked).2] at inner
  exact ⟨outer,inner⟩

abbrev higherTree : CoreCallableCompositionalResourceStorage.Tree :=
  .function [] readerResult (.storage [])

theorem higher_storage_domain {resource : Opened} (path : HigherPath resource) :
    path.stored = higherTree := by
  have accepted := path.path.accepted
  have result := congrArg (Option.map Sigma.fst) accepted
  have computed : (CoreCallableCompositionalResourceStorage.check
      CoreCallableComposedResourceOrigins.Probes.Original.api 3 [] higherStorage
      (.lambda 11 (.app (.variable 11) .unit)) higherRecipe).map Sigma.fst = some higherTree := by
    dsimp only [higherRecipe,higherTree,higherStorage,readerResult,readerStorage]
    repeat' (first
      | dsimp [CoreCallableCompositionalResourceStorage.lookup,CoreCallableCompositionalResourceStorage.Tree.valid,
          CoreCallableCompositionalResourceStorage.Atom.valid,CoreCallableCompositionalResourceStorage.template,
          CoreCallableCompositionalResourceStorage.template.bounds,CoreCallableCompositionalResourceStorage.captures,
          CoreCallableCompositionalResourceStorage.collect,CoreCallableCompositionalResourceStorage.Tree.storageOf,
          Code.dependencies,Code.freeNames,Syntax.without]
      | simp only [CoreCallableCompositionalResourceStorage.check])
    rfl
  rw [computed] at result
  exact (Option.some.inj result).symm

theorem retained_lower_domain {resource : Opened} (path : HigherPath resource) :
    path.stored.value 0 = .function [] (.function [0,0] (.storage []) (.storage [])) (.storage []) := by
  rw [higher_storage_domain path]
  rfl

#print axioms checked_call_actual
#print axioms higher_storage_domain
#print axioms retained_lower_domain

#print axioms check_call
#print axioms check_call_executed
#print axioms checked_beta_endpoints

#print axioms HigherJoined
#print axioms join_higher
#print axioms join_higher_executed

#print axioms bind_codes
#print axioms bind_initializer
#print axioms outer_function_control
#print axioms outer_argument_control
#print axioms first_beta_environment
#print axioms first_beta_closing
#print axioms inner_function_control
#print axioms inner_argument_control
#print axioms second_beta_environment
#print axioms second_beta_closing
#print axioms callee_saved_environment_differs
#print axioms request_carrier
#print axioms request_operand_control
#print axioms read_cut
#print axioms read_actual
#print axioms read_observation
#print axioms read_history
#print axioms initial_to_higher
#print axioms calls_segment
#print axioms initial_target_trace
#print axioms initial_to_read
#print axioms call_target_trace
#print axioms read_ticket_bound
#print axioms read_current_sites
#print axioms read_current_scopes
#print axioms original_owner_ledger
#print axioms read_result

end Original

#print axioms segment_target
#print axioms higher_current_point
#print axioms higher_value
#print axioms variable_output

#print axioms HigherSelection.body_exact
#print axioms produce_higher
#print axioms higher_chain
end Ash.OneShot.CoreCallableComposedRuntimeCalls
