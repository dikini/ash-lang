import CoreCallableRestoredBindContinuationConsumers
import CoreCallableRestoredBindConsumers
import CoreCallableStrictCallerHeadConsumers
import CoreCallableStrictOutsideHeadConsumers
import CoreCallableGeneratedBindConsumers
import CoreCallableGeneratedCleanupCompletion
namespace Ash.OneShot.RestoredBindContinuationInterfaces.Connected
open CoreCallableGeneratedChronology
open CoreSyntax CoreTranslation CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableGeneralHistory CoreCallableCallerBarriers CoreCallableRunningOccurrence CoreCallableReachableResume
open CoreCallableRunningCapture CoreCallableSiteLineage CoreCaptureEntry CoreRequestFrames CoreCallableCleanupOrigins
open CoreCallableCleanupReachableTransport CoreCleanupFrames

private def graph : Graph := ⟨[
  {originalId:=0,type:=.unit,effects:=[],source:=none,kind:=.unit},
  {originalId:=1,type:=.unit,effects:=[.user 0 []],source:=none,kind:=.request (.user 0 []) 0 0},
  {originalId:=2,type:=.unit,effects:=[],source:=none,kind:=.unit},
  {originalId:=3,type:=.unit,effects:=[],source:=none,kind:=.resume 0 0 .consumed 2},
  {originalId:=4,type:=.unit,effects:=[.user 1 []],source:=none,kind:=.request (.user 1 []) 0 0},
  {originalId:=5,type:=.product .unit .unit,effects:=[.user 1 []],source:=none,kind:=.tuple [4,4]},
  {originalId:=6,type:=.unit,effects:=[.user 1 []],source:=none,kind:=.bind ⟨20,.product .unit .unit⟩ 5 3},
  {originalId:=7,type:=.unit,effects:=[],source:=none,kind:=.resume 1 1 .consumed 2},
  {originalId:=8,type:=.unit,effects:=[],source:=none,kind:=.handler 1 (.user 1 []) 6 [⟨0,.binder ⟨14,.unit⟩,1,7⟩]},
  {originalId:=9,type:=.unit,effects:=[],source:=none,kind:=.handler 0 (.user 0 []) 1 [⟨0,.binder ⟨13,.unit⟩,0,8⟩]},
  {originalId:=10,type:=.function .unit .unit [],effects:=[],source:=none,kind:=.function ⟨12,.unit⟩ 9},
  {originalId:=11,type:=.function .unit .unit [],effects:=[],source:=none,kind:=.variable 9},
  {originalId:=12,type:=.unit,effects:=[],source:=none,kind:=.apply 11 0},
  {originalId:=13,type:=.unit,effects:=[],source:=none,kind:=.cleanup ⟨9,.function .unit .unit []⟩ 12 0},
  {originalId:=14,type:=.unit,effects:=[],source:=none,kind:=.bind ⟨9,.function .unit .unit []⟩ 10 13}
],14⟩
private def requestK : Code := .perform (.user 1 []) 0 .unit
private def kBody : Code := .bind 20 (.pair requestK requestK) (.resume (ticket graph 0) .unit)
private def kClauseBody : Code := .resume (ticket graph 1) .unit
private def kClauses : Clauses := .cons 0 14 (ticket graph 1) kClauseBody .nil
private def clauseBody : Code := .handle (.user 1 []) kBody kClauses
private def clauses : Clauses := .cons 0 13 (ticket graph 0) clauseBody .nil
private def body : Code := .handle (.user 0 []) (.perform (.user 0 []) 0 .unit) clauses
private def callback : Code := .lambda 12 body
private def closure : CoreMachine.Value := .closure 12 9 .empty
private def environment : Environment := .binding 9 closure .empty
private def base : CoreMachine.State := {control := .returned .unit}

private theorem callable : CallableCertificate graph 12 9 body := by
  refine ⟨⟨10,⟨12,.unit⟩,_,rfl,rfl,rfl⟩,⟨10,rfl⟩,?_⟩
  intro ticket
  simp [body,clauses,clauseBody,kBody,kClauses,kClauseBody,requestK,Code.dependencies,Clauses.dependencies,Syntax.without]

private theorem callback_value : ValueRel graph [] [] closure callback := by
  refine .closure (fuel := 10) (bodyCode := body) rfl callable .empty ?_
  simp [callback,body,clauses,clauseBody,kBody,kClauses,kClauseBody,requestK,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Clauses.freeNames,Instantiation.Effect.freeNames,Instantiation.Effect.resources,effectAtoms,Code.dependencies,Clauses.dependencies,Syntax.without]

private def action : ActionData := ⟨0,callback,callback_value.closed,.none,.unit,[]⟩

private theorem saved_callback : EnvCloses graph [] [] environment
    (.app (.variable 9) .unit) (.app callback .unit) := by
  refine .binding callback_value ?_
  simpa [Code.subst] using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .app callback .unit))

private theorem receipt : SavedCleanupOrigin graph [] [] 12 environment action [] := by
  refine ⟨?_,.inactive (CanonicalOwnerMap.empty graph)⟩
  exact .armed (site := 13) (node := graph.nodes[13]'(by decide)) rfl rfl rfl rfl saved_callback rfl callback_value

private noncomputable def start : RunningStartPast graph [] 12 environment action .unit .unit [] .nil := {
  predecessor := base,callerOwners := [],scope := .none
  installed := receipt,saved := .unit,originalHistory := .nil
  running := ⟨receipt,.unit⟩,sameInstalled := rfl
  actual := CoreGeneralRestoration.normal_start receipt.delayed (ValueRel.unit (owners := [])) (GeneralHistory.nil (graph := graph) (heap := [])).related .none }

private noncomputable def s0 : Endpoint graph := started start

private theorem ordered : CoreTranslationFuel.Postorder graph :=
  CoreTranslationFuel.checkShape_postorder graph (by rfl)

private noncomputable def enter : EntryInput s0 := {
  ordered := ordered,site := 12,environment := environment,node := graph.nodes[12]'(by decide),known := rfl
  nextIndex := 11,frame := .applyFunction 0 environment,kind := .application rfl,environmentSame := rfl
  control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl saved_callback }

private noncomputable def s1 := (entry_result enter).after
private noncomputable def literalFunction : LiteralInput s1 := {
  index := 11,environment := environment,code := callback,scope := .none
  literal := .lexicalVariable (node := graph.nodes[11]'(by decide)) rfl rfl (by
    refine .binding callback_value ?_
    simpa [s1,entry_result,enter,s0,started,start,base,startedState,Code.subst] using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := callback))) callback_value.closed
  control := rfl
  stack := by
    let plain : PlainData := ⟨.appFunction .unit,.none,.unit,.unit,[],rfl⟩
    have frame : PlainFrameRel graph [] [] (.applyFunction 0 environment) plain := by
      refine .applyFunction (fuel := 1) rfl ?_
      refine .binding callback_value ?_
      simpa [Code.subst] using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .unit))
    exact prepend_mapped frame callback_value.closed (pushed_mapped PushedWithMaps.nil) .none }

private noncomputable def s2 := (literal_result literalFunction).after


private theorem s2_exact : s2.state = { s1.state with
    control := .returned closure
    observations := s1.state.observations ++ [.entered 11] } := by
  have concrete : CoreMachine.next graph s1.state = .stepped { s1.state with
      control := .returned closure
      observations := s1.state.observations ++ [.entered 11] } := rfl
  exact CoreMachine.Outcome.stepped.inj ((literal_result literalFunction).core.symm.trans concrete)

private noncomputable def changeArgument : SwapInput s2 := {
  frameOwners := [],beforeFrame := .applyFunction 0 environment,afterFrame := .applyArgument closure
  kind := .application,value := closure,nextIndex := 0,environment := environment
  frameBefore := Or.inl rfl,frameAfter := Or.inl rfl,code := callback,related := callback_value
  interpreted := ⟨rfl,callback,.none,(by
    change ControlRel graph [] [] s2.state.control callback
    rw [s2_exact]
    exact .returned callback_value),literalFunction.stack⟩
  control := by rw [s2_exact]
  maps := rfl }

private noncomputable def s3 := (swap_result changeArgument).after

private noncomputable def literalArgument : LiteralInput s3 := {
  index := 0,environment := environment,code := .unit,scope := .none
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (by
    refine .binding callback_value ?_
    simpa [s3,swap_result,changeArgument,s2,literal_result,s1,entry_result,enter,s0,started,start,base,startedState,Code.subst]
      using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .unit)))
  control := rfl
  stack := by
    let plain : PlainData := ⟨.appArgument callback,.none,.unit,.unit,[],rfl⟩
    have frame : PlainFrameRel graph [] [] (.applyArgument closure) plain := .applyArgument callback_value
    exact prepend_mapped frame (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed
      (pushed_mapped PushedWithMaps.nil) .none }

private noncomputable def s4 := (literal_result literalArgument).after

private theorem s4_exact : s4.state = { s3.state with
    control := .returned .unit
    observations := s3.state.observations ++ [.entered 0] } := by
  have concrete : CoreMachine.next graph s3.state = .stepped { s3.state with
      control := .returned .unit
      observations := s3.state.observations ++ [.entered 0] } := rfl
  exact CoreMachine.Outcome.stepped.inj ((literal_result literalArgument).core.symm.trans concrete)

private noncomputable def apply : BetaInput s4 := {
  frameOwners := [],parameter := 12,body := 9,environment := .empty,value := .unit
  argument := .unit,bodyCode := body,scope := .none,function := callback_value,operand := .unit
  control := by rw [s4_exact]
  maps := rfl,focus := rfl }

private noncomputable def s5 := (beta_result apply).after


private def outerData : HandlerData := ⟨0,.user 0 [],clauses,.none,.unit,by
  simp [clauses,clauseBody,kBody,kClauses,kClauseBody,requestK,Clauses.dependencies,Code.dependencies,Syntax.ticketDependencies,Syntax.without,
    effectAtoms,Instantiation.Effect.resources]⟩

private noncomputable def outerPast : GeneralHandlerPast graph [] 9 (.binding 12 .unit .empty) outerData := {
  predecessor := s5.state,originalSuffix := s5.physical,originalMaps := none
  mapsSame := by intro maps impossible; cases impossible
  node := graph.nodes[9]'(by decide),handler := 0,effect := .user 0 [],body := 1
  clauses := [⟨0,.binder ⟨13,.unit⟩,0,8⟩],known := rfl,kind := rfl
  lineage := .inactive (.empty graph),origin := .inactive (.empty graph)
  header := .handler (fuel := 11) rfl rfl rfl (by
    exact .binding ValueRel.unit .empty)
  actual := rfl }

private noncomputable def enterOuter : HandlerInput s5 := {
  owners := [],ownersSame := rfl,site := 9,environment := .binding 12 .unit .empty
  data := outerData,installation := outerPast,predecessor := rfl,suffix := rfl
  code := .perform (.user 0 []) 0 .unit,raw := .perform (.user 0 []) 0 .unit
  rawClauses := clauses,fuel := 10,translated := rfl,siteTranslated := rfl
  lexical := .binding ValueRel.unit .empty
  control := rfl,empty := ⟨rfl,rfl⟩ }

private noncomputable def s6 := (handler_result enterOuter).after
private noncomputable def enterRequest : EntryInput s6 := {
  ordered := ordered,site := 1,environment := .binding 12 .unit .empty,node := graph.nodes[1]'(by decide),known := rfl
  nextIndex := 0,frame := .request (.user 0 []) 0 (.binding 12 .unit .empty)
  kind := .request rfl,environmentSame := rfl,control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl (.binding ValueRel.unit .empty) }
private noncomputable def s7 := (entry_result enterRequest).after
private def requestPlain : PlainData := ⟨.perform (.user 0 []) 0,.none,.unit,.unit,[],rfl⟩
private noncomputable def requestOperand : LiteralInput s7 := {
  index := 0,environment := .binding 12 .unit .empty,code := .unit,scope := .none
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (.binding ValueRel.unit .empty)
  control := rfl
  stack := by
    have frame : RequestRel graph [] [] (.request (.user 0 []) 0 (.binding 12 .unit .empty)) requestPlain :=
      .operand (requested := .user 0 []) (.binding ValueRel.unit .empty) rfl
    exact prepend_request frame (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed (pushed_mapped .nil) .none }
private noncomputable def s8 := (literal_result requestOperand).after
private theorem s8_returned : s8.state.control = .returned .unit := by
  have concrete : CoreMachine.next graph s7.state = .stepped {s7.state with
    control := .returned .unit,observations := s7.state.observations ++ [.entered 0]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((literal_result requestOperand).core.symm.trans concrete)
  change (literal_result requestOperand).after.state.control = .returned .unit
  rw [same]

private noncomputable def captureRequest : CaptureInput s8 := {
  index := ⟨0,by decide⟩,requested := .user 0 [],effect := .user 0 [],operation := 0
  selectedClause := ⟨0,.binder ⟨13,.unit⟩,0,8⟩,value := .unit,code := .unit
  environment := .binding 12 .unit .empty,plain := requestPlain,context := [],outward := [.user 0 []],result := .unit
  same := rfl,prefixScope := .nil,route := .outside (by simp)
  lookup := rfl,selected := rfl,operand := .unit
  requestCarrier := .binding ValueRel.unit .empty,plainContext := rfl
  ready := by
    intro parameter binder body atClause
    cases atClause with
    | hit =>
      simp [ClosedExcept,clauseBody,kBody,kClauses,kClauseBody,requestK,Code.dependencies,Clauses.dependencies,effectAtoms,Instantiation.Effect.resources]
    | pass different rest => exact False.elim (different rfl)
  control := s8_returned,maps := rfl,focus := rfl }
private noncomputable def s9 := (capture_result captureRequest).after

private noncomputable def capturedData := capture_data captureRequest
private theorem captured_argument : capturedData.argument.id = 13 := by
  have same : capturedData.argument = ⟨13,.unit⟩ := (CoreSyntax.Pattern.binder.inj capturedData.pattern).symm
  exact congrArg CoreSyntax.Binder.id same
private theorem one_clause_body {parameter binder : Nat} {code : Code}
    (selected : ClauseAt 0 clauses parameter binder code) : code = clauseBody := by
  cases selected with
  | hit => rfl
  | pass different rest => exact False.elim (different rfl)
private theorem captured_body : capturedData.body = clauseBody :=
  one_clause_body capturedData.clauseAt

private theorem s9_control : s9.state.control = .evaluate 8 (.binding 13 .unit (.binding 12 .unit .empty)) := by
  change CoreMachine.Control.evaluate 8 (.binding capturedData.argument.id .unit (.binding 12 .unit .empty)) = _
  rw [captured_argument]
private theorem s9_focus : s9.focus = ⟨clauseBody,.ticket (ticket graph 0) 0,.nil⟩ := by
  change (⟨capturedData.body.subst capturedData.argument.id .unit,.ticket (ticket graph 0) 0,.nil⟩ : Configuration) = _
  rw [captured_body,captured_argument]
  rfl

private def frontData : HandlerData := ⟨1,.user 1 [],kClauses,.ticket (ticket graph 0) 0,.unit,by simp [kClauses,kClauseBody,Clauses.dependencies,Code.dependencies,Syntax.ticketDependencies,Syntax.without]⟩
private noncomputable def frontPast : GeneralHandlerPast graph [⟨0,0,ticket graph 0⟩] 8
    (.binding 13 .unit (.binding 12 .unit .empty)) frontData := {
  predecessor := s9.state,originalSuffix := s9.physical,originalMaps := none
  mapsSame := by intro maps impossible; cases impossible
  node := graph.nodes[8]'(by decide),handler := 1,effect := .user 1 [],body := 6,clauses := [⟨0,.binder ⟨14,.unit⟩,1,7⟩]
  known := rfl,kind := rfl
  lineage := .clause (.empty graph) (handlerSite := 9) (node := graph.nodes[9]'(by decide)) rfl rfl (by decide)
  origin := .clause (.empty graph) (.hit _)
  header := .handler (fuel := 8) rfl rfl rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty))
  actual := rfl }

private noncomputable def enterFront : HandlerInput s9 := {
  owners := [⟨0,0,ticket graph 0⟩],ownersSame := rfl,site := 8
  environment := .binding 13 .unit (.binding 12 .unit .empty),data := frontData,installation := frontPast
  predecessor := rfl,suffix := rfl,code := kBody,raw := kBody
  rawClauses := kClauses,fuel := 8,translated := rfl,siteTranslated := rfl
  lexical := .binding ValueRel.unit (.binding ValueRel.unit .empty)
  control := s9_control,empty := ⟨rfl,s9_focus⟩ }
private noncomputable def s10 := (handler_result enterFront).after


open CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers CoreCallableStrictCaptureOrigins
open CoreCallableStrictOutsideHeadOrigins CoreCallableStrictOutsideHeadConsumers CoreCallableGeneratedBindProducers CoreCallableGeneratedBindConsumers
private noncomputable def captured_trace : Generated start s9 9 [.ticket 0] [] := by
  have g0 : Generated start s0 0 [] [] := .initial
  have g1 := Generated.next g0 (Operation.entry enter)
  have g2 := Generated.next g1 (Operation.literal literalFunction)
  have g3 := Generated.next g2 (Operation.swap changeArgument)
  have g4 := Generated.next g3 (Operation.literal literalArgument)
  have g5 := Generated.next g4 (Operation.beta apply)
  have g6 := Generated.next g5 (Operation.handler enterOuter)
  have g7 := Generated.next g6 (Operation.entry enterRequest)
  have g8 := Generated.next g7 (Operation.literal requestOperand)
  exact Generated.next g8 (Operation.capture captureRequest)

private noncomputable def installed_trace : Generated start s10 10 [.ticket 0] [] := Generated.next captured_trace (.handler enterFront)
private def callerScope : Execution.Scope := .ticket (ticket graph 0) 0
private def callerOwners : OwnerMap := [⟨0,0,ticket graph 0⟩]
private def callerEnv : CoreMachine.Environment := .binding 13 .unit (.binding 12 .unit .empty)
private def bindPlain : PlainData := ⟨.bind 20 (.resume (ticket graph 0) .unit),callerScope,.product .unit .unit,.unit,[0],rfl⟩
private noncomputable def bindingReady : BindReady s10 := {
  site := 6,binder := ⟨20,.product .unit .unit⟩,initializer := 5,body := 3
  environment := callerEnv,plain := bindPlain,node := graph.nodes[6]'(by decide)
  known := rfl,kind := rfl,fuel := 4
  rawInitializer := .pair requestK requestK,rawBody := .resume (ticket graph 0) .unit
  initializerCode := .pair requestK requestK,suffix := .resume (ticket graph 0) .unit
  initializerTranslated := rfl,bodyTranslated := rfl,closing := .binding ValueRel.unit (.binding ValueRel.unit .empty)
  notValue := by simp [requestK,Code.IsValue]
  closed := by simp [ClosedExcept,Code.dependencies]
  context := rfl,control := rfl,empty := ⟨rfl,rfl⟩ }
private noncomputable def bindingInput := bind_from_generated ordered installed_trace bindingReady
private noncomputable def bound := (bind_result bindingInput).after
private noncomputable def bound_trace : Generated start bound 11 [.ticket 0] [] := Generated.next installed_trace (.bind bindingInput)
private theorem bound_control : bound.state.control = .evaluate 5 callerEnv := by
  have actual : CoreMachine.next graph s10.state = .stepped {s10.state with
    control := .evaluate 5 callerEnv,frames := .bind 20 3 callerEnv :: s10.physical,
    observations := s10.state.observations ++ [.entered 6]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((bind_result bindingInput).core.symm.trans actual)
  change (bind_result bindingInput).after.state.control = _
  rw [same]
private theorem bound_code : bound.focus = ⟨.pair requestK requestK,callerScope,.nil⟩ := by
  have shapes := congrArg Configuration.expression bindingInput.empty.focus
  have code : bindingInput.past.contextCode = .pair requestK requestK := (Code.bind.inj shapes).2.1.symm
  change (⟨bindingInput.past.contextCode,callerScope,.nil⟩ : Configuration) = _
  rw [code]
private noncomputable def original_prefix : Prefix graph bound := .generated ordered bound_trace
private def pairPlain : PlainData := ⟨.pairLeft requestK,callerScope,.unit,.product .unit .unit,[],rfl⟩
private noncomputable def strictReady : EntryReady .pair bound := {
  site := 5,left := 4,right := 4,environment := callerEnv,plain := pairPlain
  node := graph.nodes[5]'(by decide),known := rfl,shape := rfl
  fuel := 2,rawLeft := requestK,rawRight := requestK,leftCode := requestK,rightCode := requestK
  leftTranslated := rfl,rightTranslated := rfl,closing := .binding ValueRel.unit (.binding ValueRel.unit .empty)
  notValue := by simp [requestK,Code.IsValue]
  context := rfl,control := bound_control,empty := ⟨rfl,bound_code⟩ }
private noncomputable def e0 := entry_after strictReady (original_prefix.receipt strictReady)
private noncomputable def b0 : BeforeCapture original_prefix strictReady e0 1 := .entered
private noncomputable def enterKRequest : EntryInput e0 := {
  ordered := ordered,site := 4,environment := callerEnv,node := graph.nodes[4]'(by decide),known := rfl
  nextIndex := 0,frame := .request (.user 1 []) 0 callerEnv
  kind := .request rfl,environmentSame := rfl,control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty)) }
private noncomputable def e1 := (entry_result enterKRequest).after
private noncomputable def b1 : BeforeCapture original_prefix strictReady e1 2 := .stable b0 (.entry enterKRequest)
private def kRequestPlain : PlainData := ⟨.perform (.user 1 []) 0,callerScope,.unit,.unit,[],rfl⟩
private noncomputable def kRequestOperand : LiteralInput e1 := {
  index := 0,environment := callerEnv,code := .unit,scope := callerScope
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty))
  control := rfl
  stack := by
    have frame : RequestRel graph callerOwners [] (.request (.user 1 []) 0 callerEnv) kRequestPlain :=
      .operand (requested := .user 1 []) (.binding ValueRel.unit (.binding ValueRel.unit .empty)) rfl
    exact prepend_request frame (ValueRel.unit (graph := graph) (owners := callerOwners) (heap := [])).closed (pushed_mapped .nil) callerScope }
private noncomputable def e2 := (literal_result kRequestOperand).after
private noncomputable def b2 : BeforeCapture original_prefix strictReady e2 3 := .stable b1 (.literal kRequestOperand)
private theorem e2_returned : e2.state.control = .returned .unit := by
  have actual : CoreMachine.next graph e1.state = .stepped {e1.state with
    control := .returned .unit,observations := e1.state.observations ++ [.entered 0]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((literal_result kRequestOperand).core.symm.trans actual)
  change (literal_result kRequestOperand).after.state.control = _
  rw [same]
private noncomputable def captureK : CaptureInput e2 := {
  index := ⟨0,by decide⟩,requested := .user 1 [],effect := .user 1 [],operation := 0
  selectedClause := ⟨0,.binder ⟨14,.unit⟩,1,7⟩,value := .unit,code := .unit
  environment := callerEnv,plain := kRequestPlain,context := [],outward := [.user 1 []],result := .unit
  same := rfl,prefixScope := .skip rfl (.skip rfl .nil),route := .outside (by simp)
  lookup := rfl,selected := rfl,operand := .unit
  requestCarrier := .binding ValueRel.unit (.binding ValueRel.unit .empty),plainContext := rfl
  ready := by
    intro parameter binder code atClause
    cases atClause with
    | hit => simp [ClosedExcept,kClauseBody,Code.dependencies]
    | pass different rest => exact False.elim (different rfl)
  control := e2_returned,maps := rfl,focus := rfl }
private noncomputable def e3 := (capture_result captureK).after
private noncomputable def a0 : AfterCapture captureK e3 1 := .captured
private noncomputable def kData := capture_data captureK
private theorem k_argument : kData.argument.id = 14 := by
  have same : kData.argument = ⟨14,.unit⟩ := (CoreSyntax.Pattern.binder.inj kData.pattern).symm
  exact congrArg CoreSyntax.Binder.id same
private theorem one_k_body {parameter binder : Nat} {code : Code}
    (selected : ClauseAt 0 kClauses parameter binder code) : code = kClauseBody := by
  cases selected with
  | hit => rfl
  | pass different rest => exact False.elim (different rfl)
private theorem k_body : kData.body = kClauseBody := one_k_body kData.clauseAt
private def kEnv : CoreMachine.Environment := .binding 14 .unit callerEnv
private theorem e3_control : e3.state.control = .evaluate 7 kEnv := by
  change CoreMachine.Control.evaluate 7 (.binding kData.argument.id .unit callerEnv) = _
  rw [k_argument]; rfl
private theorem e3_focus : e3.focus = ⟨kClauseBody,.ticket (ticket graph 1) 1,.nil⟩ := by
  change (⟨kData.body.subst kData.argument.id .unit,.ticket (ticket graph 1) 1,.nil⟩ : Configuration) = _
  rw [k_body,k_argument]; rfl
private noncomputable def enterKResume : EntryInput e3 := {
  ordered := ordered,site := 7,environment := kEnv,node := graph.nodes[7]'(by decide),known := rfl
  nextIndex := 2,frame := .resume 1 1,kind := .resume rfl,environmentSame := trivial
  control := e3_control,maps := rfl,stack := rfl
  interpreted := by
    rw [e3_focus]
    exact .evaluate (fuel := 2) rfl (.binding ValueRel.unit (.binding ValueRel.unit (.binding ValueRel.unit .empty))) }
private noncomputable def e4 := (entry_result enterKResume).after
private def kResumePlain : PlainData := ⟨.resume (ticket graph 1),.ticket (ticket graph 1) 1,.unit,.unit,[1],rfl⟩
private theorem kResumeFrame : CoreResumeFrames.ResumeRel graph (⟨1,1,ticket graph 1⟩::callerOwners) [] (.resume 1 1) kResumePlain :=
  .operand (environment := kEnv) (site := 7) (node := graph.nodes[7]'(by decide)) (fuel := 2) rfl rfl rfl rfl
    (.binding ValueRel.unit (.binding ValueRel.unit (.binding ValueRel.unit .empty))) rfl
private noncomputable def kResumeOperand : LiteralInput e4 := {
  index := 2,environment := kEnv,code := .unit,scope := .ticket (ticket graph 1) 1
  literal := .unit (node := graph.nodes[2]'(by decide)) rfl rfl (.binding ValueRel.unit (.binding ValueRel.unit (.binding ValueRel.unit .empty)))
  control := rfl
  stack := by
    change OrdinaryWithMaps graph [] [(⟨1,1,ticket graph 1⟩::callerOwners,.resume 1 1)]
      .unit (.ticket (ticket graph 1) 1) e3.focus.expression e3.focus.scope e3.focus.stack
    rw [e3_focus]
    exact prepend_resume kResumeFrame
      (ValueRel.unit (graph := graph) (owners := ⟨1,1,ticket graph 1⟩::callerOwners) (heap := [])).closed
      (pushed_mapped .nil) (.ticket (ticket graph 1) 1) }
private noncomputable def e5 := (literal_result kResumeOperand).after
private theorem e5_returned : e5.state.control = .returned .unit := by
  have actual : CoreMachine.next graph e4.state = .stepped {e4.state with
    control := .returned .unit,observations := e4.state.observations ++ [.entered 2]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((literal_result kResumeOperand).core.symm.trans actual)
  change (literal_result kResumeOperand).after.state.control = _
  rw [same]
private noncomputable def a1 : AfterCapture captureK e4 2 := .stable a0 (.entry enterKResume)
private noncomputable def a2 : AfterCapture captureK e5 3 := .stable a1 (.literal kResumeOperand)
private noncomputable def resumeReady : ResumeReady captureK e5 := {
  frameOwners := ⟨1,1,ticket graph 1⟩::callerOwners,plain := kResumePlain,binder := ticket graph 1
  frame := kResumeFrame,context := rfl,value := .unit,code := .unit,operand := .unit
  resolve := by
    have counter : e2.state.nextOwner = 1 := (Execution.Scope.ticket.inj (congrArg Configuration.scope e3_focus)).2
    simp [kResumePlain,Execution.Scope.resolve,counter]
  control := e5_returned,maps := rfl,focus := by
    change e3.focus = _
    exact e3_focus }
private def returnPlain : PlainData := ⟨.pairRight .unit,callerScope,.unit,.product .unit .unit,[],rfl⟩
private theorem kept_exact : (dormant b2 captureK).kept =
    [.bind 20 3 callerEnv,.handlerBoundary 8 callerEnv 1] := by
  have same := dormant_original_tail b2 captureK
  have split : [.bind 20 3 callerEnv,.handlerBoundary 8 callerEnv 1] ++ s9.physical =
      (dormant b2 captureK).kept ++ s9.physical := same
  exact (List.append_cancel_right split).symm
open CoreCallableStrictCallerHeadCompatibility
private noncomputable def returned : CoreCallableStrictCallerHeadConsumers.ReturnedReady b2 captureK a2 resumeReady := {
  afterPlain := returnPlain,context := rfl,sameScope := rfl,notValue := by simp [strictReady,requestK,Code.IsValue]
  unique := checkHandlerSites_sound (graph := graph) rfl
  metadata := rfl
  position := by rw [kept_exact]; rfl }
private noncomputable def right := CoreCallableStrictCallerHeadConsumers.right_after returned

open CoreCallableRestoredTupleHeads CoreCallableRestoredTupleDischarge

private noncomputable def secondExpectedMark : HandlerMark graph [] := {
  owners := (location e2 captureK.index).owners,site := (location e2 captureK.index).site
  environment := (location e2 captureK.index).environment,data := (location e2 captureK.index).data
  installation := (location e2 captureK.index).installation
  inside := [.tupleRight .unit,.bind 20 3 callerEnv],front := .push (.plain returnPlain) (.push (.plain bindPlain) .nil)
  outside := [.clauseBoundary 1 1 1 1 none] ++ (location e2 captureK.index).outside
  tail := .spent 1 (location e2 captureK.index).data.answer (location e2 captureK.index).data.scope
    (location e2 captureK.index).tail }

private theorem right_marks : (handler_locations right.history).map handlerMark = [secondExpectedMark] := by
  have below := CoreCallableRestoredTupleHeads.HeadMember.below_handler_marks (restored_member b2 captureK a2 resumeReady)
  have oldMarks : (handler_locations (resume_result (resume_input a2 resumeReady)).after.history).map handlerMark =
      [(secondExpectedMark.unhead).head (.tupleLeft 4 callerEnv) pairPlain] := rfl
  rw [oldMarks] at below
  have belowExact : (handler_locations (CoreCallableStrictCaptureOrigins.restored_tail b2 captureK a2)).map handlerMark =
      [secondExpectedMark.unhead] := by
    have collapse : [(secondExpectedMark.unhead).head (.tupleLeft 4 callerEnv) pairPlain].map HandlerMark.unhead =
        [secondExpectedMark.unhead] := rfl
    exact below.trans collapse
  have head := CoreCallableRestoredTupleHeads.HeadMember.handler_marks
    (HeadMember.here (CoreCallableRestoredTupleHeads.installed_related returned) (by trivial)
      (CoreCallableStrictCaptureOrigins.restored_tail b2 captureK a2))
  have headExact : (handler_locations right.history).map handlerMark =
        ((handler_locations (CoreCallableStrictCaptureOrigins.restored_tail b2 captureK a2)).map handlerMark).map
          (fun mark => mark.head (.tupleRight .unit) returnPlain) := head
  exact headExact.trans (congrArg (fun marks => marks.map (fun mark => mark.head (.tupleRight .unit) returnPlain)) belowExact)

private noncomputable def secondB0 : RightBefore returned right 0 := .installed
private noncomputable def enterSecondKRequest : EntryInput right := {
  ordered := ordered,site := 4,environment := callerEnv,node := graph.nodes[4]'(by decide),known := rfl
  nextIndex := 0,frame := .request (.user 1 []) 0 callerEnv
  kind := .request rfl,environmentSame := rfl,control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty)) }
private noncomputable def f1 := (entry_result enterSecondKRequest).after
private noncomputable def secondB1 : RightBefore returned f1 1 := .stable secondB0 (.entry enterSecondKRequest)
private def secondRequestPlain : PlainData := ⟨.perform (.user 1 []) 0,callerScope,.unit,.unit,[],rfl⟩
private noncomputable def secondKRequestOperand : LiteralInput f1 := {
  index := 0,environment := callerEnv,code := .unit,scope := callerScope
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty))
  control := rfl
  stack := by
    have frame : RequestRel graph callerOwners [] (.request (.user 1 []) 0 callerEnv) secondRequestPlain :=
      .operand (requested := .user 1 []) (.binding ValueRel.unit (.binding ValueRel.unit .empty)) rfl
    exact prepend_request frame (ValueRel.unit (graph := graph) (owners := callerOwners) (heap := [])).closed (pushed_mapped .nil) callerScope }
private noncomputable def f2 := (literal_result secondKRequestOperand).after
private noncomputable def secondB2 : RightBefore returned f2 2 := .stable secondB1 (.literal secondKRequestOperand)
private theorem f2_returned : f2.state.control = .returned .unit := by
  have actual : CoreMachine.next graph f1.state = .stepped {f1.state with
    control := .returned .unit,observations := f1.state.observations ++ [.entered 0]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((literal_result secondKRequestOperand).core.symm.trans actual)
  change (literal_result secondKRequestOperand).after.state.control = _
  rw [same]
private theorem f2_marks : (handler_locations f2.history).map handlerMark = [secondExpectedMark] := right_marks
private theorem second_locations_length : (handler_locations f2.history).length = 1 := by
  have length := congrArg List.length f2_marks
  rw [List.length_map] at length
  exact length
private def secondIndex : Fin (handler_locations f2.history).length := ⟨0,by rw [second_locations_length]; decide⟩
private theorem second_mark : handlerMark (location f2 secondIndex) = secondExpectedMark := by
  have same := congrArg (fun xs => xs[0]?) f2_marks
  have atZero : (handler_locations f2.history)[0]? = some ((handler_locations f2.history)[secondIndex]) := by
    simp [secondIndex]
  simp only [List.getElem?_map,atZero,Option.map_some] at same
  exact Option.some.inj same
private theorem second_site : (location f2 secondIndex).site = 8 := congrArg HandlerMark.site second_mark
private theorem second_environment : (location f2 secondIndex).environment = callerEnv := congrArg HandlerMark.environment second_mark
private theorem second_owners : (location f2 secondIndex).owners = callerOwners := congrArg HandlerMark.owners second_mark
private theorem second_data : (location f2 secondIndex).data = (location e2 captureK.index).data := congrArg HandlerMark.data second_mark
private theorem second_inside : (location f2 secondIndex).inside = [.tupleRight .unit,.bind 20 3 callerEnv] := congrArg HandlerMark.inside second_mark
private theorem second_outside : (location f2 secondIndex).outside = [.clauseBoundary 1 1 1 1 none] ++ (location e2 captureK.index).outside := congrArg HandlerMark.outside second_mark
private theorem second_front : (location f2 secondIndex).front = .push (.plain returnPlain) (.push (.plain bindPlain) .nil) := congrArg HandlerMark.front second_mark
private theorem second_clauses : (location f2 secondIndex).installation.clauses = (location e2 captureK.index).installation.clauses :=
  congrArg (fun mark => mark.installation.clauses) second_mark
private theorem second_handler : (location f2 secondIndex).installation.handler = 1 :=
  congrArg (fun mark => mark.installation.handler) second_mark

private noncomputable def secondCaptureK : CaptureInput f2 := {
  index := secondIndex,requested := .user 1 [],effect := .user 1 [],operation := 0
  selectedClause := ⟨0,.binder ⟨14,.unit⟩,1,7⟩,value := .unit,code := .unit
  environment := callerEnv,plain := secondRequestPlain,context := [],outward := [.user 1 []],result := .unit
  same := by rw [second_data]; rfl
  prefixScope := by rw [second_front]; exact .skip rfl (.skip rfl .nil),route := .outside (by simp)
  lookup := by
    have physical := RightBefore.physical returned secondB2
    rw [second_inside,second_site,second_environment,second_data,second_outside,physical]
    change CoreMachine.findInterpreter graph (.user 1 []) (.tupleRight .unit :: (dormant b2 captureK).kept ++ _) = _
    rw [kept_exact]
    rfl
  selected := by rw [second_clauses]; rfl,operand := .unit
  requestCarrier := .binding ValueRel.unit (.binding ValueRel.unit .empty),plainContext := rfl
  ready := by
    intro parameter binder code atClause
    rw [second_data] at atClause
    cases atClause with
    | hit => simp [ClosedExcept,kClauseBody,Code.dependencies]
    | pass different rest => exact False.elim (different rfl)
  control := f2_returned,maps := rfl,focus := rfl }
private noncomputable def f3 := (capture_result secondCaptureK).after
private noncomputable def secondA0 : AfterCapture secondCaptureK f3 1 := .captured
private noncomputable def secondData := capture_data secondCaptureK
private theorem second_argument : secondData.argument.id = 14 := by
  have same : secondData.argument = ⟨14,.unit⟩ := (CoreSyntax.Pattern.binder.inj secondData.pattern).symm
  exact congrArg CoreSyntax.Binder.id same
private theorem one_second_body {parameter binder : Nat} {code : Code}
    (selected : ClauseAt 0 kClauses parameter binder code) : code = kClauseBody := by
  cases selected with
  | hit => rfl
  | pass different rest => exact False.elim (different rfl)
private theorem second_body : secondData.body = kClauseBody := by
  have atClause := secondData.clauseAt
  change ClauseAt 0 (location f2 secondIndex).data.clauses secondData.argument.id (ticket graph 1) secondData.body at atClause
  rw [second_data] at atClause
  exact one_second_body atClause
private def secondEnv : CoreMachine.Environment := .binding 14 .unit callerEnv
private theorem f3_control : f3.state.control = .evaluate 7 secondEnv := by
  change CoreMachine.Control.evaluate 7 (.binding secondData.argument.id .unit (location f2 secondIndex).environment) = _
  rw [second_environment]
  rw [second_argument]; rfl
private theorem f3_focus : f3.focus = ⟨kClauseBody,.ticket (ticket graph 1) 2,.nil⟩ := by
  change (⟨secondData.body.subst secondData.argument.id .unit,.ticket (ticket graph 1) 2,.nil⟩ : Configuration) = _
  rw [second_body,second_argument]; rfl
private theorem f3_owners : f3.owners = ⟨1,1,ticket graph 1⟩::callerOwners := by
  change ⟨(location f2 secondIndex).installation.handler,1,ticket graph 1⟩ :: (location f2 secondIndex).owners = _
  rw [second_handler,second_owners]
private noncomputable def enterSecondKResume : EntryInput f3 := {
  ordered := ordered,site := 7,environment := secondEnv,node := graph.nodes[7]'(by decide),known := rfl
  nextIndex := 2,frame := .resume 1 1,kind := .resume rfl,environmentSame := trivial
  control := f3_control,maps := rfl,stack := rfl
  interpreted := by
    rw [f3_focus,f3_control,f3_owners]
    exact .evaluate (fuel := 2) rfl (.binding ValueRel.unit (.binding ValueRel.unit (.binding ValueRel.unit .empty))) }
private noncomputable def f4 := (entry_result enterSecondKResume).after
private def secondKResumePlain : PlainData := ⟨.resume (ticket graph 1),.ticket (ticket graph 1) 2,.unit,.unit,[2],rfl⟩
private theorem secondKResumeFrame : CoreResumeFrames.ResumeRel graph (⟨1,1,ticket graph 1⟩::callerOwners) [] (.resume 1 1) secondKResumePlain :=
  .operand (environment := secondEnv) (site := 7) (node := graph.nodes[7]'(by decide)) (fuel := 2) rfl rfl rfl rfl
    (.binding ValueRel.unit (.binding ValueRel.unit (.binding ValueRel.unit .empty))) rfl
private noncomputable def secondKResumeOperand : LiteralInput f4 := {
  index := 2,environment := secondEnv,code := .unit,scope := .ticket (ticket graph 1) 2
  literal := .unit (node := graph.nodes[2]'(by decide)) rfl rfl (.binding ValueRel.unit (.binding ValueRel.unit (.binding ValueRel.unit .empty)))
  control := rfl
  stack := by
    change OrdinaryWithMaps graph [] [(f3.owners,.resume 1 1)]
      .unit (.ticket (ticket graph 1) 2) f3.focus.expression f3.focus.scope f3.focus.stack
    rw [f3_focus,f3_owners]
    exact prepend_resume secondKResumeFrame
      (ValueRel.unit (graph := graph) (owners := ⟨1,1,ticket graph 1⟩::callerOwners) (heap := [])).closed
      (pushed_mapped .nil) (.ticket (ticket graph 1) 2) }
private noncomputable def f5 := (literal_result secondKResumeOperand).after
private theorem f5_returned : f5.state.control = .returned .unit := by
  have actual : CoreMachine.next graph f4.state = .stepped {f4.state with
    control := .returned .unit,observations := f4.state.observations ++ [.entered 2]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((literal_result secondKResumeOperand).core.symm.trans actual)
  change (literal_result secondKResumeOperand).after.state.control = _
  rw [same]
private noncomputable def secondA1 : AfterCapture secondCaptureK f4 2 := .stable secondA0 (.entry enterSecondKResume)
private noncomputable def secondA2 : AfterCapture secondCaptureK f5 3 := .stable secondA1 (.literal secondKResumeOperand)
private noncomputable def secondResumeReady : ResumeReady secondCaptureK f5 := {
  frameOwners := ⟨1,1,ticket graph 1⟩::callerOwners,plain := secondKResumePlain,binder := ticket graph 1
  frame := by change CoreResumeFrames.ResumeRel graph _ [] (.resume (location f2 secondIndex).installation.handler 1) _; rw [second_handler]; exact secondKResumeFrame
  context := rfl,value := .unit,code := .unit,operand := .unit
  resolve := by
    have counter : f2.state.nextOwner = 2 := (Execution.Scope.ticket.inj (congrArg Configuration.scope f3_focus)).2
    simp [secondKResumePlain,Execution.Scope.resolve,counter]
  control := f5_returned
  maps := by
    change [(f3.owners,CoreMachine.Frame.resume 1 1)] = [(⟨1,1,ticket graph 1⟩::callerOwners,CoreMachine.Frame.resume (location f2 secondIndex).installation.handler 1)]
    rw [f3_owners,second_handler]
  focus := by
    change f3.focus = _
    exact f3_focus }

private noncomputable def discharged := tuple_after returned secondB2 secondCaptureK secondA2 secondResumeReady

theorem second_capture_selects_same_installation : HEq secondData.installation.installation kData.installation.installation := by
  exact secondData.sameInstallation.trans ((HandlerMark.same_installation _ _ second_mark).trans kData.sameInstallation.symm)

theorem second_actual_discharge : CoreMachine.next graph (resume_result (resume_input secondA2 secondResumeReady)).after.state =
    .stepped discharged.state := tuple_actual returned secondB2 secondCaptureK secondA2 secondResumeReady

theorem second_positive_discharge : CoreUnwindRelation.Positive (resume_result (resume_input secondA2 secondResumeReady)).after.point.machine
    discharged.point.machine [] [] := tuple_positive returned secondB2 secondCaptureK secondA2 secondResumeReady

theorem fresh_pair : ValueRel graph callerOwners discharged.state.heap (.location 0) (.pair .unit .unit) :=
  tuple_value returned secondB2 secondCaptureK secondA2 secondResumeReady

private theorem second_kept : (CoreCallableRestoredTupleHeads.dormant returned secondB2 secondCaptureK).kept =
    [.bind 20 3 callerEnv,.handlerBoundary 8 callerEnv 1] := by
  have same := CoreCallableRestoredTupleHeads.dormant_original_tail returned secondB2 secondCaptureK
  change (CoreCallableStrictCaptureOrigins.dormant b2 captureK).kept ++
      .clauseBoundary 1 1 1 1 none :: (location e2 captureK.index).outside = _ at same
  rw [kept_exact] at same
  change [.bind 20 3 callerEnv,.handlerBoundary 8 callerEnv 1] ++
      (.clauseBoundary 1 1 1 1 none :: (location e2 captureK.index).outside) = _ at same
  change _ = (CoreCallableRestoredTupleHeads.dormant returned secondB2 secondCaptureK).kept ++
      (location f2 secondIndex).outside at same
  rw [second_outside] at same
  exact (List.append_cancel_right same).symm

private noncomputable def ownScopeReady : ScopeReady returned secondB2 secondCaptureK :=
  .outside returned.unique (by change savedCallerHeadCheck _ _ (location f2 secondIndex).owners (location f2 secondIndex).data.scope = true; rw [second_owners,second_data]; rfl)
    (by rw [second_kept]; rfl)

theorem original_to_discharged : CoreAllocationHistory.Steps graph 26 s0.state discharged.state := by
  have first := (CoreCallableStrictCallerHeadConsumers.complete_original_prefix returned).1
  exact .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc first
    (entry_result enterSecondKRequest).core) (literal_result secondKRequestOperand).core)
    (capture_result secondCaptureK).core) (entry_result enterSecondKResume).core)
    (literal_result secondKResumeOperand).core) (resume_result (resume_input secondA2 secondResumeReady)).core)
    (tuple_actual returned secondB2 secondCaptureK secondA2 secondResumeReady)

theorem original_target_trace : CoreUnwindRelation.Trace s0.point.machine discharged.point.machine
    [.ticket 0,.ticket 1,.ticket 2] [.ticket 2,.ticket 1] := by
  have first := (CoreCallableStrictCallerHeadConsumers.complete_original_prefix returned).2
  have t1 := first.append (entry_result enterSecondKRequest).matching.target_trace
  have t2 := t1.append (literal_result secondKRequestOperand).matching.target_trace
  have t3 := t2.append (capture_result secondCaptureK).matching.target_trace
  have t4 := t3.append (entry_result enterSecondKResume).matching.target_trace
  have t5 := t4.append (literal_result secondKResumeOperand).matching.target_trace
  have t6 := t5.append (resume_result (resume_input secondA2 secondResumeReady)).matching.target_trace
  exact t6.append (tuple_positive returned secondB2 secondCaptureK secondA2 secondResumeReady).trace

theorem exposed_older_bind : discharged.physical =
    [.bind 20 3 callerEnv,.handlerBoundary 8 callerEnv 1,
      .clauseBoundary 1 1 1 2 none,.clauseBoundary 1 1 1 1 none,
      .clauseBoundary 0 0 0 0 (some [.handlerBoundary 9 (.binding 12 .unit .empty) 0]),
      .cleanupCompletion 0 .unit] := by
  change (CoreCallableRestoredTupleHeads.dormant returned secondB2 secondCaptureK).kept ++
      (secondA2.carrier.front ++ .clauseBoundary (location f2 secondIndex).installation.handler 1
        (location f2 secondIndex).data.activation f2.state.nextOwner none :: (location f2 secondIndex).outside) = _
  rw [second_kept,second_handler,second_data,second_outside]
  rfl

theorem active_H_ticket_preserved : CurrentScopeOrigin graph callerOwners callerScope discharged.physical :=
  tuple_scope returned secondB2 secondCaptureK secondA2 secondResumeReady ownScopeReady

theorem result_map_scope : discharged.owners = callerOwners ∧ discharged.maps = [] ∧
    discharged.focus = ⟨.pair .unit .unit,callerScope,.nil⟩ := ⟨rfl,rfl,rfl⟩

theorem exact_pair_heap : discharged.state.control = .returned (.location 0) ∧
    discharged.state.heap = [.pair .unit .unit] := ⟨rfl,rfl⟩

/-- Wrong actual selection/occurrence checks; no malformed AfterCapture is manufactured. -/
theorem wrong_H_selection : (location f2 secondIndex).installation.handler ≠ 0 := by rw [second_handler]; decide

theorem wrong_K_activation : (location f2 secondIndex).data.activation ≠ 0 := by rw [second_data]; decide

theorem wrong_old_capture_ticket : f2.state.nextOwner ≠ e2.state.nextOwner := by decide

theorem original_right_not_returned (value : CoreMachine.Value) : right.state.control ≠ .returned value := by
  intro same
  cases same

/-- Conditional first-static-pair barrier remains a separate coverage boundary. -/
theorem same_pair_spent_still_blocks {handler owner oldOccurrence oldTicket newOccurrence newTicket : Nat}
    {oldSaved : Option (List CoreMachine.Frame)} {physical front outside : List CoreMachine.Frame}
    (different : oldTicket ≠ newTicket) :
    ¬ OwnerPath handler owner oldOccurrence oldTicket oldSaved
      (.clauseBoundary handler owner newOccurrence newTicket none :: physical) front outside :=
  CoreCallableCleanupReachableTransport.outside_static_shadow_obstruction different

theorem unchanged_unit_metadata : (graph.nodes[6]'(by decide)).type = .unit ∧
    (graph.nodes[8]'(by decide)).type = .unit ∧ (graph.nodes[9]'(by decide)).type = .unit ∧
    (graph.nodes[10]'(by decide)).type = .function .unit .unit [] := ⟨rfl,rfl,rfl,rfl⟩


open CoreCallableRestoredBindOrigins CoreCallableRestoredBindConsumers

private noncomputable def actualBindBelow := discharged_bind bindingInput strictReady original_prefix b2 captureK a2 resumeReady returned secondB2 secondCaptureK secondA2 secondResumeReady
private noncomputable def completedBind := CoreCallableRestoredBindConsumers.bind_after bindingInput strictReady original_prefix b2 captureK a2 resumeReady returned secondB2 secondCaptureK secondA2 secondResumeReady

private theorem first_own_kept : (first_kept_bind bindingInput strictReady original_prefix b2 captureK).physical = [.handlerBoundary 8 callerEnv 1] := by
  have head := (first_kept_bind bindingInput strictReady original_prefix b2 captureK).member.physical
  change (dormant b2 captureK).kept = .bind 20 3 callerEnv :: _ at head
  rw [kept_exact] at head
  exact (List.cons.inj head).2.symm

private theorem second_own_kept : (second_kept_bind bindingInput strictReady original_prefix b2 captureK a2 resumeReady returned secondB2 secondCaptureK).physical = [.handlerBoundary 8 callerEnv 1] := by
  have head := (second_kept_bind bindingInput strictReady original_prefix b2 captureK a2 resumeReady returned secondB2 secondCaptureK).member.physical
  change (CoreCallableRestoredTupleHeads.dormant returned secondB2 secondCaptureK).kept = .bind 20 3 callerEnv :: _ at head
  rw [second_kept] at head
  exact (List.cons.inj head).2.symm

private noncomputable def firstOwnScope : BindScopeReady graph bindingInput.owners bindingInput.plain.scope
    (first_kept_bind bindingInput strictReady original_prefix b2 captureK).physical (location e2 captureK.index).owners (location e2 captureK.index).data.scope :=
  .outside returned.unique (by rfl) (by rw [first_own_kept]; rfl)

private noncomputable def secondOwnScope : BindScopeReady graph bindingInput.owners bindingInput.plain.scope
    (second_kept_bind bindingInput strictReady original_prefix b2 captureK a2 resumeReady returned secondB2 secondCaptureK).physical (location f2 secondCaptureK.index).owners (location f2 secondCaptureK.index).data.scope :=
  .outside returned.unique (by change savedCallerHeadCheck _ _ (location f2 secondIndex).owners (location f2 secondIndex).data.scope = true; rw [second_owners,second_data]; rfl)
    (by rw [second_own_kept]; rfl)

theorem actual_changed_tail_bind : CoreMachine.next graph discharged.state = .stepped completedBind.state :=
  CoreCallableRestoredBindConsumers.bind_actual bindingInput strictReady original_prefix b2 captureK a2 resumeReady returned secondB2 secondCaptureK secondA2 secondResumeReady

theorem actual_two_raw_bind : CoreUnwindRelation.Positive discharged.point.machine completedBind.point.machine [] [] :=
  CoreCallableRestoredBindConsumers.bind_positive bindingInput strictReady original_prefix b2 captureK a2 resumeReady returned secondB2 secondCaptureK secondA2 secondResumeReady

theorem original_to_completed_bind : CoreAllocationHistory.Steps graph 27 s0.state completedBind.state :=
  .snoc original_to_discharged actual_changed_tail_bind

theorem original_bind_target_trace : CoreUnwindRelation.Trace s0.point.machine completedBind.point.machine
    [.ticket 0,.ticket 1,.ticket 2] [.ticket 2,.ticket 1] := by
  simpa using original_target_trace.append actual_two_raw_bind.trace

theorem exact_changed_bind_tail : completedBind.physical =
    [.handlerBoundary 8 callerEnv 1,.clauseBoundary 1 1 1 2 none,.clauseBoundary 1 1 1 1 none,
      .clauseBoundary 0 0 0 0 (some [.handlerBoundary 9 (.binding 12 .unit .empty) 0]),.cleanupCompletion 0 .unit] := by
  have head := actualBindBelow.member.physical
  change discharged.physical = .bind 20 3 callerEnv :: completedBind.physical at head
  rw [exposed_older_bind] at head
  exact (List.cons.inj head).2.symm

theorem own_saved_H_restored : CurrentScopeOrigin graph callerOwners callerScope completedBind.physical :=
  CoreCallableRestoredBindConsumers.bind_scope bindingInput strictReady original_prefix b2 captureK a2 resumeReady returned secondB2 secondCaptureK secondA2 secondResumeReady firstOwnScope secondOwnScope

theorem original_body_environment : ∃ fuel rawBody,
    CoreTranslation.translateFuel graph fuel callerOwners 3 = .ok rawBody ∧
    EnvCloses graph callerOwners completedBind.state.heap (.binding 20 (.location 0) callerEnv)
      rawBody (.resume (ticket graph 0) .unit) := by
  have shapes := congrArg Configuration.expression bindingInput.empty.focus
  change Code.bind 20 (.pair requestK requestK) (.resume (ticket graph 0) .unit) =
    .bind 20 bindingInput.past.contextCode bindingInput.past.suffixCode at shapes
  have suffix := (Code.bind.inj shapes).2.2.symm
  have produced := CoreCallableRestoredBindConsumers.bind_closing bindingInput strictReady original_prefix b2 captureK a2 resumeReady returned secondB2 secondCaptureK secondA2 secondResumeReady
  change ∃ fuel rawBody, CoreTranslation.translateFuel graph fuel callerOwners 3 = .ok rawBody ∧
    EnvCloses graph callerOwners completedBind.state.heap (.binding 20 (.location 0) callerEnv)
      rawBody (bindingInput.past.suffixCode.subst 20 (.pair .unit .unit)) at produced
  rw [suffix] at produced
  exact produced

theorem original_body_site : SiteLineage graph callerOwners callerScope 3 :=
  CoreCallableRestoredBindConsumers.bind_site bindingInput strictReady original_prefix b2 captureK a2 resumeReady returned secondB2 secondCaptureK secondA2 secondResumeReady

theorem receiver_preserved : completedBind.state.control = .evaluate 3 (.binding 20 (.location 0) callerEnv) ∧
    completedBind.owners = callerOwners ∧ completedBind.maps = [] ∧
    completedBind.state.heap = [.pair .unit .unit] := ⟨rfl,rfl,rfl,rfl⟩

theorem bind_not_earlier_receiver : bindingInput.binder.id ≠ 9 := by decide

theorem tuple_current_is_returned : discharged.state.control ≠ .evaluate 3 callerEnv := by
  intro impossible
  rw [exact_pair_heap.1] at impossible
  cases impossible

theorem original_tail_not_reused : completedBind.physical ≠ s10.physical := by
  rw [exact_changed_bind_tail]
  intro same
  have lengths := congrArg List.length same
  change 5 = 3 at lengths
  cases lengths

theorem preserved_annotation_boundary : bindPlain.input = .product .unit .unit ∧ returnPlain.output = .product .unit .unit ∧
    (graph.nodes[6]'(by decide)).kind = .bind ⟨20,.product .unit .unit⟩ 5 3 := ⟨rfl,rfl,rfl⟩

open CoreCallableRestoredBindContinuationOrigins CoreCallableRestoredBindContinuationConsumers
private theorem completedBind_focus : completedBind.focus = ⟨.resume (ticket graph 0) .unit,callerScope,.nil⟩ := by
  have shapes := congrArg Configuration.expression bindingInput.empty.focus
  change Code.bind 20 (.pair requestK requestK) (.resume (ticket graph 0) .unit) =
    .bind 20 bindingInput.past.contextCode bindingInput.past.suffixCode at shapes
  have suffix := (Code.bind.inj shapes).2.2.symm
  change (⟨bindingInput.past.suffixCode.subst 20 (.pair .unit .unit),callerScope,.nil⟩ : Configuration) = _
  rw [suffix]
  rfl
private def hResumePlain : PlainData := ⟨.resume (ticket graph 0),callerScope,.unit,.unit,[0],rfl⟩
private theorem current_body_closing : EnvCloses graph callerOwners completedBind.state.heap
    (.binding 20 (.location 0) callerEnv) (.resume (ticket graph 0) .unit) (.resume (ticket graph 0) .unit) :=
  .binding fresh_pair (.binding ValueRel.unit (.binding ValueRel.unit .empty))
private noncomputable def hEntry : EntryInput completedBind := {
  ordered := ordered,site := 3,environment := .binding 20 (.location 0) callerEnv
  node := graph.nodes[3]'(by decide),known := rfl,nextIndex := 2,frame := .resume 0 0
  kind := .resume rfl,environmentSame := trivial,control := receiver_preserved.1
  maps := receiver_preserved.2.2.1,stack := rfl
  interpreted := by
    rw [receiver_preserved.1,completedBind_focus]
    exact .evaluate (fuel := 2) rfl current_body_closing }
private noncomputable def h0 := (entry_result hEntry).after
private theorem hFrame : CoreResumeFrames.ResumeRel graph callerOwners h0.state.heap (.resume 0 0) hResumePlain :=
  .operand (site := 3) (raw := .unit) (node := graph.nodes[3]'(by decide)) (fuel := 2) rfl rfl rfl rfl current_body_closing rfl
private noncomputable def hOperand : LiteralInput h0 := {
  index := 2,environment := .binding 20 (.location 0) callerEnv,code := .unit,scope := callerScope
  literal := .unit (node := graph.nodes[2]'(by decide)) rfl rfl
    (.binding fresh_pair (.binding ValueRel.unit (.binding ValueRel.unit .empty)))
  control := rfl
  stack := by
    change OrdinaryWithMaps graph h0.state.heap [(callerOwners,.resume 0 0)] .unit callerScope completedBind.focus.expression completedBind.focus.scope completedBind.focus.stack
    rw [completedBind_focus]
    exact prepend_resume hFrame (ValueRel.unit (graph := graph) (owners := callerOwners) (heap := h0.state.heap)).closed (pushed_mapped .nil) callerScope }
private noncomputable def h1 := (literal_result hOperand).after
private theorem h1_returned : h1.state.control = .returned .unit := by
  have concrete : CoreMachine.next graph h0.state = .stepped {h0.state with
    control := .returned .unit,observations := h0.state.observations ++ [.entered 2]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((literal_result hOperand).core.symm.trans concrete)
  change (literal_result hOperand).after.state.control = .returned .unit
  rw [same]
private theorem retained_H_path : OwnerPath 0 0 0 0
    (some [.handlerBoundary 9 (.binding 12 .unit .empty) 0]) h1.physical
    [.handlerBoundary 8 callerEnv 1,.clauseBoundary 1 1 1 2 none,.clauseBoundary 1 1 1 1 none]
    [.cleanupCompletion 0 .unit] := by
  change OwnerPath _ _ _ _ _ completedBind.physical _ _
  rw [exact_changed_bind_tail]
  refine .skip _ (by intro c s a t cap impossible; cases impossible) ?_
  refine .skip _ (by intro c s a t cap same; cases same; exact Or.inl (by decide)) ?_
  refine .skip _ (by intro c s a t cap same; cases same; exact Or.inl (by decide)) ?_
  exact .hit _
private noncomputable def hSelected := owner_from_live_path h1.history retained_H_path
private noncomputable def hResume := resume_live_result retained_H_path hResumePlain callerOwners hFrame rfl rfl
  (ValueRel.unit (graph := graph) (owners := callerOwners) (heap := h1.state.heap)) h1_returned rfl (by change completedBind.focus = _; exact completedBind_focus)
private noncomputable def h2 := hResume.after

theorem computed_H_ticket : hSelected.dynamicTicket = 0 := owner_from_live_path_ticket h1.history retained_H_path

theorem actual_H_resume : CoreMachine.next graph h1.state = .stepped h2.state := hResume.core

theorem actual_H_positive : CoreUnwindRelation.Positive h1.point.machine h2.point.machine [] [.ticket 0] := by
  cases matched : hResume.matching with
  | positive proof => exact proof

private theorem first_restored_H_capture :
    searchOutcome (owner_search (CoreCallableStrictCaptureOrigins.restored_tail b2 captureK a2) 0 0) =
      searchOutcome (owner_search s9.history 0 0) := by
  have stripped := searchOutcome_head_below (restored_member b2 captureK a2 resumeReady) 0 0
  have preserved := searchOutcome_resume_other (resume_input a2 resumeReady) 0 0 (by rfl) (by rfl) (by decide)
  exact stripped.symm.trans preserved

private theorem second_original_H_capture :
    searchOutcome (owner_search (location f2 secondCaptureK.index).after 0 0) =
      searchOutcome (owner_search s9.history 0 0) := by
  have extracted := searchOutcome_handler_after f2.history (location f2 secondCaptureK.index)
    (List.getElem_mem secondCaptureK.index.isLt) (handler := 0) (owner := 0) (by
      change CoreMachine.findOwner 0 0 (location f2 secondIndex).inside = _
      rw [second_inside]
      rfl)
  change searchOutcome (owner_search right.history 0 0) = _ at extracted
  have stripped := searchOutcome_head_below
    (HeadMember.here (CoreCallableRestoredTupleHeads.installed_related returned) (by trivial)
      (CoreCallableStrictCaptureOrigins.restored_tail b2 captureK a2)) 0 0
  exact extracted.symm.trans (stripped.trans first_restored_H_capture)


private theorem second_restored_H_capture :
    searchOutcome (owner_search (CoreCallableRestoredTupleHeads.restored_tail returned secondB2 secondCaptureK secondA2) 0 0) =
      searchOutcome (owner_search s9.history 0 0) := by
  have stripped := searchOutcome_head_below
    (CoreCallableRestoredTupleHeads.restored_member returned secondB2 secondCaptureK secondA2 secondResumeReady) 0 0
  have preserved := searchOutcome_resume_other (resume_input secondA2 secondResumeReady) 0 0
    (by
      change CoreMachine.findOwner 0 0 ((location f2 secondIndex).inside ++
        [.handlerBoundary (location f2 secondIndex).site (location f2 secondIndex).environment (location f2 secondIndex).data.activation]) = _
      rw [second_inside,second_site,second_environment,second_data]
      rfl)
    (by rfl) (by
      change ¬ (0 = (location f2 secondIndex).installation.handler ∧ 0 = 1)
      rw [second_handler]
      decide)
  exact stripped.symm.trans (preserved.trans second_original_H_capture)

private theorem h_current_original_capture :
    searchOutcome (owner_search h1.history 0 0) =
      (searchOutcome (owner_search s9.history 0 0)).map
        (fun receipt => receipt.heap_weaken (CoreValueRelation.heap_append [] [.pair .unit .unit])) := by
  have stripped := searchOutcome_bind_below actualBindBelow.member 0 0
  change searchOutcome (owner_search discharged.history 0 0) =
    searchOutcome (owner_search h1.history 0 0) at stripped
  rw [← stripped]
  change searchOutcome (owner_search
    ((CoreCallableRestoredTupleHeads.restored_tail returned secondB2 secondCaptureK secondA2).heap_weaken
      (CoreValueRelation.heap_append [] [.pair .unit .unit])) 0 0) = _
  have weakened := searchOutcome_heap_weaken
    (CoreCallableRestoredTupleHeads.restored_tail returned secondB2 secondCaptureK secondA2)
    (CoreValueRelation.heap_append f5.state.heap [.pair .unit .unit]) 0 0
  exact weakened.trans (congrArg (fun outcome => outcome.map
    (fun receipt => receipt.heap_weaken (CoreValueRelation.heap_append [] [.pair .unit .unit]))) second_restored_H_capture)

private noncomputable def originalHReceipt : CapturedReceipt graph [] 0 0 := {
  owners := (location s8 captureRequest.index).owners
  occurrence := (location s8 captureRequest.index).data.activation
  dynamicTicket := s8.state.nextOwner
  captured := (location s8 captureRequest.index).inside ++
    [.handlerBoundary (location s8 captureRequest.index).site (location s8 captureRequest.index).environment (location s8 captureRequest.index).data.activation]
  data := (location s8 captureRequest.index).data
  result := captureRequest.result
  capturedTarget := (location s8 captureRequest.index).front.append (.push (.handler (location s8 captureRequest.index).data) .nil)
  installation := by with_unfolding_all exact capturedData.installation
  header := by with_unfolding_all exact capturedData.header
  history := (location s8 captureRequest.index).before.append
    (.handler (location s8 captureRequest.index).installation (location s8 captureRequest.index).header .nil) }

private theorem original_capture_H_receipt :
    searchOutcome (owner_search s9.history 0 0) = .ok originalHReceipt := by
  with_unfolding_all
    exact searchOutcome_live_here capturedData.installation capturedData.header
      ((location s8 captureRequest.index).before.append
        (.handler (location s8 captureRequest.index).installation (location s8 captureRequest.index).header .nil))
      (location s8 captureRequest.index).after

private theorem selected_H_original_receipt :
    capturedReceipt hSelected = originalHReceipt.heap_weaken (CoreValueRelation.heap_append [] [.pair .unit .unit]) := by
  have causal := h_current_original_capture
  rw [owner_from_live_path_picked h1.history retained_H_path,original_capture_H_receipt] at causal
  exact Except.ok.inj causal

private noncomputable def original_H_head : SavedHandler originalHReceipt := {
  site := (location s8 captureRequest.index).site
  environment := (location s8 captureRequest.index).environment
  installation := (location s8 captureRequest.index).installation
  header := (location s8 captureRequest.index).header
  tailPhysical := [],tailTarget := .nil,tail := .nil
  head := by
    with_unfolding_all
      exact .emptyPrefix _ _ (.here .nil) }

private noncomputable def selected_H_head : SavedHandler (capturedReceipt hSelected) :=
  SavedHandler.transport selected_H_original_receipt
    (original_H_head.heap_weaken (CoreValueRelation.heap_append [] [.pair .unit .unit]))

private noncomputable def HReturn : HandlerReturnInput h2 := {
  owners := hSelected.owners,site := selected_H_head.site,environment := selected_H_head.environment
  data := hSelected.data,installation := selected_H_head.installation,header := selected_H_head.header
  suffixPhysical := selected_H_head.tailPhysical ++ (hSelected.front ++
    .clauseBoundary 0 0 hSelected.occurrence hSelected.dynamicTicket none :: hSelected.outside)
  suffixTarget := selected_H_head.tailTarget.append (hSelected.frontTarget.append
    (.spent hSelected.dynamicTicket hSelected.data.answer hSelected.data.scope hSelected.tail))
  suffix := selected_H_head.tail.append (hSelected.frontHistory.append
    (.spent hSelected.installation hSelected.header hSelected.outsideHistory))
  value := .unit,code := .unit,scope := callerScope,operand := .unit
  control := rfl,empty := ⟨rfl,rfl⟩
  physical := by
    change hSelected.captured ++ _ = _
    have physical := selected_H_head.head.physical
    change hSelected.captured = _ at physical
    rw [physical]
    rfl
  lexical := by
    change hSelected.capturedTarget.append _ = _
    have lexical := selected_H_head.head.lexical
    change hSelected.capturedTarget = _ at lexical
    rw [lexical]
    rfl
  head := by
    with_unfolding_all
      exact .append _ _ _ selected_H_head.head }
private noncomputable def h3 := (handler_return_result HReturn).after

theorem actual_H_return : CoreMachine.next graph h2.state = .stepped h3.state :=
  (handler_return_result HReturn).core

theorem actual_H_return_positive : CoreUnwindRelation.Positive h2.point.machine h3.point.machine [] [] := by
  cases matched : (handler_return_result HReturn).matching with
  | positive proof => exact proof
  | administrative proof =>
    change LexicalUnwind.Machine.eval ⟨.unit,callerScope,h2.lexical⟩ =
      .eval ⟨.unit,hSelected.data.scope,HReturn.suffixTarget⟩ at proof
    have lengths := congrArg (fun configuration => CoreCallableRestoredBindOrigins.stackLength configuration.stack)
      (LexicalUnwind.Machine.eval.inj proof)
    rw [HReturn.lexical] at lengths
    simp [CoreCallableRestoredBindOrigins.stackLength] at lengths

private theorem second_kept_lexical :
    (CoreCallableRestoredTupleHeads.dormant returned secondB2 secondCaptureK).keptTarget =
      .push (.plain bindPlain) (.push (.handler (location f2 secondIndex).data) .nil) := by
  have shape := (CoreCallableRestoredTupleHeads.dormant returned secondB2 secondCaptureK).captured.lexical
  change (location f2 secondIndex).front.append (.push (.handler (location f2 secondIndex).data) .nil) =
    .push (.plain returnPlain) (CoreCallableRestoredTupleHeads.dormant returned secondB2 secondCaptureK).keptTarget at shape
  rw [second_front] at shape
  exact (Stack.push.inj shape).2.symm

private theorem h1_concrete_lexical : h1.lexical =
    .push (.handler (location f2 secondIndex).data)
      (.spent 2 (location f2 secondIndex).data.answer (location f2 secondIndex).data.scope (location f2 secondIndex).tail) := by
  have shape := actualBindBelow.member.lexical
  change discharged.lexical = .push (.plain bindPlain) h1.lexical at shape
  change (CoreCallableRestoredTupleHeads.dormant returned secondB2 secondCaptureK).keptTarget.append
    (secondA2.carrier.frontTarget.append (.spent f2.state.nextOwner (location f2 secondIndex).data.answer
      (location f2 secondIndex).data.scope (location f2 secondIndex).tail)) = _ at shape
  rw [second_kept_lexical] at shape
  exact (Stack.push.inj shape).2.symm

private def runningStack : Stack := .push (.running action .unit (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed) .nil

private theorem append_live_ne_running (first : Stack) :
    first.append (.live dynamicTicket result answer captured scope tail) ≠ runningStack := by
  intro same
  cases first with
  | nil => cases same
  | push frame rest =>
    have ends := (Stack.push.inj same).2
    have lengths := congrArg CoreCallableRestoredBindOrigins.stackLength ends
    simp only [CoreCallableRestoredBindOrigins.stackLength_append,CoreCallableRestoredBindOrigins.stackLength] at lengths
    omega
  | live => cases same
  | spent => cases same

private theorem split_three_literal (first : Stack) (last : Stack)
    (same : first.append (.live 0 .unit outerData.answer (.push (.handler outerData) .nil) outerData.scope last) =
      .push (.handler (location f2 secondIndex).data)
        (.spent 2 (location f2 secondIndex).data.answer (location f2 secondIndex).data.scope
          (.spent 1 (location e2 captureK.index).data.answer (location e2 captureK.index).data.scope
            (.live 0 .unit outerData.answer (.push (.handler outerData) .nil) outerData.scope runningStack)))) :
    first = .push (.handler (location f2 secondIndex).data)
      (.spent 2 (location f2 secondIndex).data.answer (location f2 secondIndex).data.scope
        (.spent 1 (location e2 captureK.index).data.answer (location e2 captureK.index).data.scope .nil)) ∧ last = runningStack := by
  cases first with
  | nil => cases same
  | live => cases same
  | spent => cases same
  | push frame rest =>
    simp only [Stack.append,Stack.push.injEq] at same
    obtain ⟨rfl,same⟩ := same
    cases rest with
    | nil => cases same
    | push => cases same
    | live => cases same
    | spent dynamicTicket answer scope rest =>
      simp only [Stack.append,Stack.spent.injEq] at same
      obtain ⟨rfl,rfl,rfl,same⟩ := same
      cases rest with
      | nil => cases same
      | push => cases same
      | live => cases same
      | spent dynamicTicket answer scope rest =>
        simp only [Stack.append,Stack.spent.injEq] at same
        obtain ⟨rfl,rfl,rfl,same⟩ := same
        cases rest with
        | nil => exact ⟨rfl,(Stack.live.inj same).2.2.2.2.2⟩
        | push => cases same
        | spent => cases same
        | live dynamicTicket result answer saved scope rest =>
          simp only [Stack.append,Stack.live.injEq] at same
          exact False.elim (append_live_ne_running rest same.2.2.2.2.2)

private theorem selected_H_current_split : hSelected.frontTarget =
    .push (.handler (location f2 secondIndex).data)
      (.spent 2 (location f2 secondIndex).data.answer (location f2 secondIndex).data.scope
        (.spent 1 (location e2 captureK.index).data.answer (location e2 captureK.index).data.scope .nil)) ∧
    hSelected.tail = runningStack := by
  have same := hSelected.targetSame.symm
  have data := congrArg CapturedReceipt.data selected_H_original_receipt
  have captured := congrArg CapturedReceipt.capturedTarget selected_H_original_receipt
  have result := congrArg CapturedReceipt.result selected_H_original_receipt
  change hSelected.data = outerData at data
  change hSelected.capturedTarget = .push (.handler outerData) .nil at captured
  change hSelected.result = .unit at result
  rw [computed_H_ticket,data,captured,result] at same
  have concrete := same.trans h1_concrete_lexical
  have tail := congrArg HandlerMark.tail second_mark
  change (location f2 secondIndex).tail = .spent 1 (location e2 captureK.index).data.answer
    (location e2 captureK.index).data.scope (location e2 captureK.index).tail at tail
  rw [tail] at concrete
  with_unfolding_all exact split_three_literal hSelected.frontTarget hSelected.tail concrete

private theorem h3_physical : h3.physical =
    [.handlerBoundary 8 callerEnv 1,.clauseBoundary 1 1 1 2 none,.clauseBoundary 1 1 1 1 none,
      .clauseBoundary 0 0 0 0 none,.cleanupCompletion 0 .unit] := by
  have empty := SavedHandler.transport_tailPhysical selected_H_original_receipt
    (original_H_head.heap_weaken (CoreValueRelation.heap_append [] [.pair .unit .unit]))
  change selected_H_head.tailPhysical = [] at empty
  have actual := (owner_search_lookup h1.history (owner_from_live_path_picked h1.history retained_H_path)).1
  have same := Except.ok.inj (actual.symm.trans retained_H_path.lookup)
  have front := congrArg CoreMachine.OwnerCut.inside same
  have outside := congrArg CoreMachine.OwnerCut.outside same
  have occurrence := congrArg CoreMachine.OwnerCut.occurrence same
  change hSelected.front = _ at front
  change hSelected.outside = _ at outside
  change hSelected.occurrence = 0 at occurrence
  change selected_H_head.tailPhysical ++ (hSelected.front ++
    .clauseBoundary 0 0 hSelected.occurrence hSelected.dynamicTicket none :: hSelected.outside) = _
  rw [empty,front,outside,occurrence,computed_H_ticket]
  rfl

private theorem h3_lexical : h3.lexical =
    .push (.handler (location f2 secondIndex).data)
      (.spent 2 (location f2 secondIndex).data.answer (location f2 secondIndex).data.scope
        (.spent 1 (location e2 captureK.index).data.answer (location e2 captureK.index).data.scope
          (.spent 0 outerData.answer outerData.scope runningStack))) := by
  have empty := SavedHandler.transport_tailTarget selected_H_original_receipt
    (original_H_head.heap_weaken (CoreValueRelation.heap_append [] [.pair .unit .unit]))
  change selected_H_head.tailTarget = .nil at empty
  have data := congrArg CapturedReceipt.data selected_H_original_receipt
  change hSelected.data = outerData at data
  change selected_H_head.tailTarget.append (hSelected.frontTarget.append
    (.spent hSelected.dynamicTicket hSelected.data.answer hSelected.data.scope hSelected.tail)) = _
  rw [empty,selected_H_current_split.1,selected_H_current_split.2,computed_H_ticket,data]
  rfl

private theorem KSelection : ∃ selected ∈ handler_locations h3.history, selected.inside = [] ∧
    selected.site = 8 ∧ selected.environment = callerEnv ∧ selected.data.activation = 1 := handler_at_physical_head h3.history h3_physical
private noncomputable def KLocation := Classical.choose KSelection
private theorem KLocation_actual : KLocation ∈ handler_locations h3.history ∧ KLocation.inside = [] ∧
    KLocation.site = 8 ∧ KLocation.environment = callerEnv ∧ KLocation.data.activation = 1 :=
  Classical.choose_spec KSelection

private theorem append_handler_ne_running (first : Stack) :
    first.append (.push (.handler data) last) ≠ runningStack := by
  intro same
  cases first with
  | nil => cases (Stack.push.inj same).1
  | push frame rest =>
    have ends := (Stack.push.inj same).2
    have lengths := congrArg CoreCallableRestoredBindOrigins.stackLength ends
    simp only [CoreCallableRestoredBindOrigins.stackLength_append,CoreCallableRestoredBindOrigins.stackLength] at lengths
    omega
  | live => cases same
  | spent => cases same

private theorem append_handler_ne_spents (first : Stack) :
    first.append (.push (.handler data) last) ≠
      .spent 2 answer2 scope2 (.spent 1 answer1 scope1 (.spent 0 answer0 scope0 runningStack)) := by
  intro same
  cases first with
  | nil => cases same
  | push => cases same
  | live => cases same
  | spent dynamicTicket answer scope rest =>
    have next := (Stack.spent.inj same).2.2.2
    cases rest with
    | nil => cases next
    | push => cases next
    | live => cases next
    | spent dynamicTicket answer scope rest =>
      have next := (Stack.spent.inj next).2.2.2
      cases rest with
      | nil => cases next
      | push => cases next
      | live => cases next
      | spent dynamicTicket answer scope rest =>
        exact append_handler_ne_running rest (Stack.spent.inj next).2.2.2

private theorem K_front_empty : KLocation.front = .nil := by
  have same := KLocation.targetSame.symm.trans h3_lexical
  generalize known : KLocation.front = first at same
  cases first with
  | nil => rfl
  | live => cases same
  | spent => cases same
  | push frame rest =>
    have next := (Stack.push.inj same).2
    exact False.elim (append_handler_ne_spents rest next)

private theorem K_index_exists : ∃ index : Fin (handler_locations h3.history).length,
    location h3 index = KLocation := by
  obtain ⟨index,lt,same⟩ := List.mem_iff_getElem.mp KLocation_actual.1
  exact ⟨⟨index,lt⟩,same⟩
private noncomputable def KIndex := Classical.choose K_index_exists
private theorem K_index_actual : location h3 KIndex = KLocation := Classical.choose_spec K_index_exists
private noncomputable def KReturn := handler_inventory_result KIndex
  (by rw [K_index_actual]; exact KLocation_actual.2.1)
  (by rw [K_index_actual]; exact K_front_empty)
  (ValueRel.unit (graph := graph) (owners := h3.owners) (heap := h3.state.heap)) (by rfl) ⟨rfl,rfl⟩
private noncomputable def h4 := KReturn.after

theorem actual_K_return : CoreMachine.next graph h3.state = .stepped h4.state := KReturn.core

private theorem h4_physical : h4.physical =
    [.clauseBoundary 1 1 1 2 none,.clauseBoundary 1 1 1 1 none,
      .clauseBoundary 0 0 0 0 none,.cleanupCompletion 0 .unit] := by
  with_unfolding_all change (location h3 KIndex).outside = _
  rw [K_index_actual]
  have same := KLocation.physicalSame.symm.trans h3_physical
  rw [KLocation_actual.2.1,KLocation_actual.2.2.1,KLocation_actual.2.2.2.1,KLocation_actual.2.2.2.2] at same
  exact (List.cons.inj same).2

private theorem h4_lexical : h4.lexical =
    .spent 2 (location f2 secondIndex).data.answer (location f2 secondIndex).data.scope
      (.spent 1 (location e2 captureK.index).data.answer (location e2 captureK.index).data.scope
        (.spent 0 outerData.answer outerData.scope runningStack)) := by
  with_unfolding_all change (location h3 KIndex).tail = _
  rw [K_index_actual]
  have same := KLocation.targetSame.symm.trans h3_lexical
  rw [K_front_empty] at same
  exact (Stack.push.inj same).2

private theorem append_spent_ne_running (first : Stack) :
    first.append (.spent dynamicTicket answer scope last) ≠ runningStack := by
  intro same
  cases first with
  | nil => cases same
  | push frame rest =>
    have ends := (Stack.push.inj same).2
    have lengths := congrArg CoreCallableRestoredBindOrigins.stackLength ends
    simp only [CoreCallableRestoredBindOrigins.stackLength_append,CoreCallableRestoredBindOrigins.stackLength] at lengths
    omega
  | live => cases same
  | spent => cases same

private theorem append_spent_ne_one (first : Stack) (different : dynamicTicket ≠ lower) :
    first.append (.spent dynamicTicket answer scope last) ≠ .spent lower answer0 scope0 runningStack := by
  intro same
  cases first with
  | nil => exact different (Stack.spent.inj same).1
  | push => cases same
  | live => cases same
  | spent dynamicTicket answer scope rest =>
    exact append_spent_ne_running rest (Stack.spent.inj same).2.2.2

private theorem append_spent_ne_two (first : Stack) (different1 : dynamicTicket ≠ lower1) (different0 : dynamicTicket ≠ lower0) :
    first.append (.spent dynamicTicket answer scope last) ≠
      .spent lower1 answer1 scope1 (.spent lower0 answer0 scope0 runningStack) := by
  intro same
  cases first with
  | nil => exact different1 (Stack.spent.inj same).1
  | push => cases same
  | live => cases same
  | spent dynamicTicket answer scope rest =>
    exact append_spent_ne_one rest different0 (Stack.spent.inj same).2.2.2

private noncomputable def K2Position := spent_position h4.history h4_physical
private theorem K2_prefix_empty : K2Position.prefixTarget = .nil := by
  have same := K2Position.targetSame.symm.trans h4_lexical
  generalize known : K2Position.prefixTarget = first at same
  cases first with
  | nil => rfl
  | push => cases same
  | live => cases same
  | spent dynamicTicket answer scope rest =>
    exact False.elim (append_spent_ne_two rest (by decide : 2 ≠ 1) (by decide : 2 ≠ 0) (Stack.spent.inj same).2.2.2)
private noncomputable def K2Return := spent_physical_result h4_physical K2_prefix_empty
  (ValueRel.unit (graph := graph) (owners := h4.owners) (heap := h4.state.heap)) (by rfl) ⟨rfl,rfl⟩
private noncomputable def h5 := K2Return.after

theorem actual_K2_return : CoreMachine.next graph h4.state = .stepped h5.state := K2Return.core

private theorem h5_physical : h5.physical =
    [.clauseBoundary 1 1 1 1 none,.clauseBoundary 0 0 0 0 none,.cleanupCompletion 0 .unit] := by
  with_unfolding_all change K2Position.tailPhysical = _
  exact (List.cons.inj (K2Position.physicalSame.symm.trans h4_physical)).2
private theorem h5_lexical : h5.lexical =
    .spent 1 (location e2 captureK.index).data.answer (location e2 captureK.index).data.scope
      (.spent 0 outerData.answer outerData.scope runningStack) := by
  with_unfolding_all change K2Position.tailTarget = _
  have same := K2Position.targetSame.symm.trans h4_lexical
  rw [K2_prefix_empty] at same
  exact (Stack.spent.inj same).2.2.2

private noncomputable def K1Position := spent_position h5.history h5_physical
private theorem K1_prefix_empty : K1Position.prefixTarget = .nil := by
  have same := K1Position.targetSame.symm.trans h5_lexical
  generalize known : K1Position.prefixTarget = first at same
  cases first with
  | nil => rfl
  | push => cases same
  | live => cases same
  | spent dynamicTicket answer scope rest =>
    exact False.elim (append_spent_ne_one rest (by decide : 1 ≠ 0) (Stack.spent.inj same).2.2.2)
private noncomputable def K1Return := spent_physical_result h5_physical K1_prefix_empty
  (ValueRel.unit (graph := graph) (owners := h5.owners) (heap := h5.state.heap)) (by rfl) ⟨rfl,rfl⟩
private noncomputable def h6 := K1Return.after

theorem actual_K1_return : CoreMachine.next graph h5.state = .stepped h6.state := K1Return.core

private theorem h6_physical : h6.physical = [.clauseBoundary 0 0 0 0 none,.cleanupCompletion 0 .unit] := by
  with_unfolding_all change K1Position.tailPhysical = _
  exact (List.cons.inj (K1Position.physicalSame.symm.trans h5_physical)).2
private theorem h6_lexical : h6.lexical = .spent 0 outerData.answer outerData.scope runningStack := by
  with_unfolding_all change K1Position.tailTarget = _
  have same := K1Position.targetSame.symm.trans h5_lexical
  rw [K1_prefix_empty] at same
  exact (Stack.spent.inj same).2.2.2

private noncomputable def HPosition := spent_position h6.history h6_physical
private theorem H_prefix_empty : HPosition.prefixTarget = .nil := by
  have same := HPosition.targetSame.symm.trans h6_lexical
  generalize known : HPosition.prefixTarget = first at same
  cases first with
  | nil => rfl
  | push => cases same
  | live => cases same
  | spent dynamicTicket answer scope rest =>
    exact False.elim (append_spent_ne_running rest (Stack.spent.inj same).2.2.2)
private noncomputable def HSpentReturn := spent_physical_result h6_physical H_prefix_empty
  (ValueRel.unit (graph := graph) (owners := h6.owners) (heap := h6.state.heap)) (by rfl) ⟨rfl,rfl⟩
private noncomputable def h7 := HSpentReturn.after

theorem actual_spent_H_return : CoreMachine.next graph h6.state = .stepped h7.state := HSpentReturn.core

private theorem h7_physical : h7.physical = [.cleanupCompletion 0 .unit] := by
  with_unfolding_all change HPosition.tailPhysical = _
  exact (List.cons.inj (HPosition.physicalSame.symm.trans h6_physical)).2
private theorem h7_lexical : h7.lexical = runningStack := by
  with_unfolding_all change HPosition.tailTarget = _
  have same := HPosition.targetSame.symm.trans h6_lexical
  rw [H_prefix_empty] at same
  exact (Stack.spent.inj same).2.2.2


private theorem h7_heap : h7.state.heap = [.pair .unit .unit] := rfl
private theorem h7_bound : TicketBound h7.state h7.lexical := by
  intro dynamicTicket
  rw [h7_lexical]
  simp [runningStack,Stack.erase,ExecFrame.erase,Control.ticketNames]
private theorem original_running_physical : h7.physical =
    .cleanupCompletion action.identity .unit :: ([] : List CoreMachine.Frame) := h7_physical
private theorem original_running_lexical : h7.lexical =
    .push (.running action .unit start.running.value.closed) .nil := h7_lexical
private noncomputable def cleanupReturn := finish_original_result start
  (by rw [h7_heap]; exact CoreValueRelation.heap_append [] [.pair .unit .unit])
  original_running_physical original_running_lexical h7_bound (by rfl) ⟨rfl,rfl⟩
private noncomputable def h8 := cleanupReturn.after

theorem actual_cleanup_finish : CoreMachine.next graph h7.state = .stepped h8.state := cleanupReturn.core

theorem final_empty_physical_lexical : h8.physical = [] ∧ h8.lexical = .nil := ⟨rfl,rfl⟩

theorem final_saved_unit : h8.state.control = .returned .unit ∧
    h8.focus = ⟨.unit,.none,.nil⟩ ∧ h8.state.frames = [] := ⟨rfl,rfl,rfl⟩

theorem final_pair_heap : h8.state.heap = [.pair .unit .unit] := h7_heap

/-- The restored-bind endpoint has nine actual successor edges. This is an
operational result for the unchanged graph and inherited metadata. -/
theorem nine_edge_suffix : CoreAllocationHistory.Steps graph 9 completedBind.state h8.state := by
  exact .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.refl _)
    (entry_result hEntry).core) (literal_result hOperand).core) hResume.core) (handler_return_result HReturn).core)
    KReturn.core) K2Return.core) K1Return.core) HSpentReturn.core) cleanupReturn.core

theorem original_running_to_done : CoreAllocationHistory.Steps graph 36 s0.state h8.state := by
  have earlier := original_to_discharged.snoc actual_changed_tail_bind
  exact earlier.trans nine_edge_suffix


theorem nine_edge_target_trace : CoreUnwindRelation.Trace completedBind.point.machine h8.point.machine
    [] [.cleanup 0,.ticket 0] := by
  have t0 := (entry_result hEntry).matching.target_trace
  have t1 := t0.append (literal_result hOperand).matching.target_trace
  have t2 := t1.append hResume.matching.target_trace
  have t3 := t2.append (handler_return_result HReturn).matching.target_trace
  have t4 := t3.append KReturn.matching.target_trace
  have t5 := t4.append K2Return.matching.target_trace
  have t6 := t5.append K1Return.matching.target_trace
  have t7 := t6.append HSpentReturn.matching.target_trace
  exact t7.append cleanupReturn.matching.target_trace

theorem original_target_to_done : CoreUnwindRelation.Trace s0.point.machine h8.point.machine
    [.ticket 0,.ticket 1,.ticket 2] [.cleanup 0,.ticket 0,.ticket 2,.ticket 1] := by
  simpa only [List.cons_append,List.append_nil,List.nil_append] using original_bind_target_trace.append nine_edge_target_trace

/-- Derive finite runner equality from the already proved actual steps, so
observations do not depend on reduction of private chosen proof metadata. -/
private theorem steps_run {graph : Graph} {count : Nat} {before after : CoreMachine.State}
    (steps : CoreAllocationHistory.Steps graph count before after) (fuel : Nat) :
    CoreMachine.run graph (count + fuel) before = CoreMachine.run graph fuel after := by
  induction steps generalizing fuel with
  | refl => simp only [Nat.zero_add]
  | @snoc count before middle after earlier step ih =>
    calc
      CoreMachine.run graph ((count + 1) + fuel) before = CoreMachine.run graph (count + (fuel + 1)) before := by congr 1; omega
      _ = CoreMachine.run graph (fuel + 1) middle := ih (fuel + 1)
      _ = CoreMachine.run graph fuel after := by
        unfold CoreMachine.Step at step
        simp only [CoreMachine.run,step]

private theorem final_run_state : h8.state =
    CoreAllocationHistory.resultState (CoreMachine.run graph 36 s0.state) := by
  have same := congrArg CoreAllocationHistory.resultState (steps_run original_running_to_done 0)
  simpa only [Nat.add_zero,CoreMachine.run,CoreAllocationHistory.resultState] using same.symm

theorem final_captured_ticket_history : CoreTicketHistory.capturedTickets h8.state.observations = [0,1,2] := by
  rw [final_run_state]
  rfl

theorem final_resumed_ticket_history : h8.state.observations.filterMap
    (fun event => match event with | .resumed owner => some owner | _ => none) = [1,2,0] := by
  rw [final_run_state]
  rfl

theorem final_returned_ticket_history : h8.state.observations.filterMap
    (fun event => match event with | .clauseReturned owner => some owner | _ => none) = [2,1,0] := by
  rw [final_run_state]
  rfl

theorem exactly_one_cleanup_finish : h8.state.observations.count (.cleanupFinished 0) = 1 := by
  rw [final_run_state]
  rfl

theorem final_done : CoreMachine.next graph h8.state = .done .unit := by
  rw [final_run_state]
  rfl

theorem spent_H_blocks_second_resume : CoreMachine.returnResume h3.state 0 0 .unit =
    .rejected (.consumedOwner 0 0) := by
  have frames : h3.state.frames = h3.physical := rfl
  unfold CoreMachine.returnResume
  rw [frames,h3_physical]
  rfl

theorem wrong_H_owner_not_found : CoreMachine.findOwner 0 9 h1.physical = .error (.missingOwner 0 9) := by
  change CoreMachine.findOwner 0 9 completedBind.physical = _
  rw [exact_changed_bind_tail]
  rfl

theorem post_bind_not_returned (value : CoreMachine.Value) : completedBind.state.control ≠ .returned value := by
  rw [receiver_preserved.1]
  intro impossible
  cases impossible

theorem spent_returns_restore_own_maps_scopes :
    h5.owners = K2Position.owners ∧ h5.focus.scope = K2Position.data.scope ∧
    h6.owners = K1Position.owners ∧ h6.focus.scope = K1Position.data.scope ∧
    h7.owners = HPosition.owners ∧ h7.focus.scope = HPosition.data.scope := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem final_original_saved_ownership : CurrentOwnership graph [] h8.state .none .nil := by
  let receipt := start.running.heap_weaken
    (show HeapExtends start.predecessor.heap h7.state.heap from by rw [h7_heap]; exact CoreValueRelation.heap_append [] [.pair .unit .unit])
  have bound : TicketBound h7.state (.push (.running action .unit receipt.value.closed) .nil) := by
    simpa only [original_running_lexical] using h7_bound
  exact (normal_finish_history (base := h7.state) receipt
    (start.originalHistory.heap_weaken (by rw [h7_heap]; exact CoreValueRelation.heap_append [] [.pair .unit .unit]))
    bound h7.owners HPosition.data.scope).2.1


/-- Count36 begins at the original running-start output s0. Including its
already authenticated cleanup-start edge gives 37 edges, not initial Core admission. -/
theorem original_start_edge_to_done : CoreAllocationHistory.Steps graph 37
    (CoreCallableGeneratedChronology.start_before start).state h8.state := by
  have initial : CoreAllocationHistory.Steps graph 1
      (CoreCallableGeneratedChronology.start_before start).state s0.state := .snoc (.refl _) start.actual.core
  exact initial.trans original_running_to_done

theorem final_original_nil_history : HEq h8.history
    (GeneralHistory.nil (graph := graph) (heap := h8.state.heap)) := HEq.rfl

theorem complete_original_owner_retirement :
    (s0.point.machine.stack.erase.owners ++ [Owner.ticket 0,Owner.ticket 1,Owner.ticket 2]).Perm
      (h8.point.machine.stack.erase.owners ++ [Owner.cleanup 0,Owner.ticket 0,Owner.ticket 2,Owner.ticket 1]) := by
  change ([Owner.cleanup 0] ++ [Owner.ticket 0,Owner.ticket 1,Owner.ticket 2]).Perm
    ([] ++ [Owner.cleanup 0,Owner.ticket 0,Owner.ticket 2,Owner.ticket 1])
  decide

#print axioms original_start_edge_to_done
#print axioms final_original_nil_history
#print axioms complete_original_owner_retirement

#print axioms nine_edge_target_trace
#print axioms original_target_to_done
#print axioms final_captured_ticket_history
#print axioms final_resumed_ticket_history
#print axioms final_returned_ticket_history
#print axioms exactly_one_cleanup_finish
#print axioms final_done
#print axioms spent_H_blocks_second_resume
#print axioms wrong_H_owner_not_found
#print axioms post_bind_not_returned
#print axioms spent_returns_restore_own_maps_scopes
#print axioms final_original_saved_ownership

#print axioms actual_cleanup_finish
#print axioms final_empty_physical_lexical
#print axioms final_saved_unit
#print axioms final_pair_heap
#print axioms nine_edge_suffix
#print axioms original_running_to_done

#print axioms actual_K2_return
#print axioms actual_K1_return
#print axioms actual_spent_H_return

#print axioms h4_lexical
#print axioms h4_physical

#print axioms actual_K_return

#print axioms h3_lexical
#print axioms h3_physical

#print axioms selected_H_current_split

#print axioms h1_concrete_lexical

#print axioms actual_H_return

#print axioms selected_H_head

#print axioms selected_H_original_receipt

#print axioms h_current_original_capture

#print axioms computed_H_ticket
#print axioms actual_H_resume
#print axioms actual_H_positive
end Ash.OneShot.RestoredBindContinuationInterfaces.Connected

namespace Ash.OneShot.RestoredBindContinuationInterfaces.Connected
open CoreCallableRestoredBindContinuationOrigins CoreCallableRestoredBindContinuationConsumers
open CoreCallableGeneratedChronology
open CoreSyntax CoreTranslation CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableGeneralHistory CoreCallableCallerBarriers CoreCallableRunningOccurrence CoreCallableReachableResume
open CoreCallableRunningCapture CoreCallableSiteLineage CoreCaptureEntry CoreRequestFrames CoreCallableCleanupOrigins
open CoreCallableCleanupReachableTransport CoreCleanupFrames

/-- The finite local operation ports are projected from the SAME actual H/K
request receipts. This is not a validated whole-program registry or admission. -/
private noncomputable def originalSignature : ScopedPorts.Signature := fun effect operation =>
  if effect = captureRequest.requested ∧ operation = captureRequest.operation then
    some (ScopedPorts.eraseType captureRequest.plain.input,ScopedPorts.eraseType captureRequest.result)
  else if effect = captureK.requested ∧ operation = captureK.operation then
    some (ScopedPorts.eraseType captureK.plain.input,ScopedPorts.eraseType captureK.result)
  else none

/-- Historical ticket ports retain each actual allocated owner and original
selected handler answer, including spent owners. Presence is not live readiness. -/
private noncomputable def originalTicketPorts : ScopedPorts.TicketSignatures := fun owner =>
  if owner = s8.state.nextOwner then
    some (ScopedPorts.eraseType captureRequest.result,ScopedPorts.eraseType outerData.answer)
  else if owner = e2.state.nextOwner then
    some (ScopedPorts.eraseType captureK.result,ScopedPorts.eraseType frontData.answer)
  else if owner = f2.state.nextOwner then
    some (ScopedPorts.eraseType secondCaptureK.result,ScopedPorts.eraseType frontData.answer)
  else none

private def originalHTicket : ScopedPorts.Ticket := .bound (ticket graph 0) .unit .unit [] []

/-- All ports come from the original literal request/handler annotations; the
Core tuple and binder remain Product while their result remains Unit. -/
theorem original_product_annotations :
    bindPlain.input = .product .unit .unit ∧ bindPlain.output = .unit ∧
    pairPlain.input = .unit ∧ pairPlain.output = .product .unit .unit ∧
    returnPlain.input = .unit ∧ returnPlain.output = .product .unit .unit ∧
    (graph.nodes[5]'(by decide)).type = .product .unit .unit ∧
    (graph.nodes[6]'(by decide)).kind = .bind ⟨20,.product .unit .unit⟩ 5 3 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem original_capture_port_projection :
    captureRequest.plain.input = .unit ∧ captureRequest.result = .unit ∧ outerData.answer = .unit ∧
    captureK.plain.input = .unit ∧ captureK.result = .unit ∧ frontData.answer = .unit ∧
    secondCaptureK.plain.input = .unit ∧ secondCaptureK.result = .unit ∧
    originalSignature (.user 0 []) 0 = some (.unit,.unit) ∧
    originalSignature (.user 1 []) 0 = some (.unit,.unit) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem original_allocated_ticket_ports :
    s8.state.nextOwner = 0 ∧ e2.state.nextOwner = 1 ∧ f2.state.nextOwner = 2 ∧
    originalTicketPorts 0 = some (.unit,.unit) ∧
    originalTicketPorts 1 = some (.unit,.unit) ∧
    originalTicketPorts 2 = some (.unit,.unit) := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem original_H_scope_typed :
    ScopedPorts.ScopeTyped originalTicketPorts callerScope originalHTicket :=
  .bound original_allocated_ticket_ports.2.2.2.1

private theorem original_K_request_port :
    ScopedPorts.Typed originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []] requestK .unit := by
  exact .perform original_capture_port_projection.2.2.2.2.2.2.2.2.2 (by simp) .unit
    (by simp [ScopedPorts.InWorld,ScopedPorts.Port.resources])

theorem original_product_initializer_port :
    ScopedPorts.Typed originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []]
      bindingReady.initializerCode (.product .unit .unit) :=
  .pair original_K_request_port original_K_request_port

theorem original_bind_suffix_port :
    ScopedPorts.Typed originalSignature []
      (ScopedPorts.TypeEnv.empty.extend 20 (.product .unit .unit)) originalHTicket [.user 1 []]
      bindingReady.suffix .unit := by
  exact .resume .unit (by simp) (by simp [ScopedPorts.InWorld,ScopedPorts.Port.resources])

theorem original_product_contexts :
    ScopedPorts.ContextTyped originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []]
      bindPlain.context (ScopedPorts.eraseType bindPlain.input) (ScopedPorts.eraseType bindPlain.output) ∧
    ScopedPorts.ContextTyped originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []]
      pairPlain.context (ScopedPorts.eraseType pairPlain.input) (ScopedPorts.eraseType pairPlain.output) ∧
    ScopedPorts.ContextTyped originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []]
      returnPlain.context (ScopedPorts.eraseType returnPlain.input) (ScopedPorts.eraseType returnPlain.output) :=
  ⟨product_bind_resume_context (by simp),pair_left_product_context original_K_request_port,pair_right_product_context⟩

theorem original_product_plain_frames :
    ScopedPorts.FrameTyped originalSignature originalTicketPorts [] (.plain bindPlain) ∧
    ScopedPorts.FrameTyped originalSignature originalTicketPorts [] (.plain pairPlain) ∧
    ScopedPorts.FrameTyped originalSignature originalTicketPorts [] (.plain returnPlain) :=
  ⟨plain_frame_at_current_ports original_H_scope_typed original_product_contexts.1,
   plain_frame_at_current_ports original_H_scope_typed original_product_contexts.2.1,
   plain_frame_at_current_ports original_H_scope_typed original_product_contexts.2.2⟩

theorem original_pair_value_port :
    ValueRel graph callerOwners discharged.state.heap (.location 0) (.pair .unit .unit) ∧
    ScopedPorts.AtType originalSignature originalTicketPorts [] callerScope (.pair .unit .unit) (.product .unit .unit) :=
  related_unit_pair_port fresh_pair original_H_scope_typed

theorem original_bind_actual_typed_composition :
    ScopedPorts.Typed originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []]
      kBody .unit := .bind original_product_initializer_port original_bind_suffix_port

/-- Pair contexts intrinsically cannot claim Unit output. -/
theorem original_wrong_unit_pair_output :
    ¬ ScopedPorts.ContextTyped originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []]
      pairPlain.context .unit .unit ∧
    ¬ ScopedPorts.ContextTyped originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []]
      returnPlain.context .unit .unit :=
  ⟨pair_left_context_output_not_unit,pair_right_context_output_not_unit⟩

/-- The unused suffix can type under Unit, but the SAME actual Product
initializer cannot compose at that input. The graph's original binder is retained. -/
theorem original_wrong_unit_bind_input :
    bindingReady.binder = ⟨20,.product .unit .unit⟩ ∧
    ¬ (ScopedPorts.Typed originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []]
        bindingReady.initializerCode .unit ∧
       ScopedPorts.ContextTyped originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []]
        bindPlain.context .unit .unit) :=
  ⟨rfl,fun inconsistent => pair_output_not_unit inconsistent.1⟩

private theorem K2_saved_scope : K2Position.data.scope = frontData.scope := by
  have same := K2Position.targetSame.symm.trans h4_lexical
  rw [K2_prefix_empty] at same
  exact ((Stack.spent.inj same).2.2.1).trans (congrArg HandlerData.scope second_data)
private theorem K1_saved_scope : K1Position.data.scope = frontData.scope := by
  have same := K1Position.targetSame.symm.trans h5_lexical
  rw [K1_prefix_empty] at same
  exact (Stack.spent.inj same).2.2.1
private theorem H_saved_scope : HPosition.data.scope = outerData.scope := by
  have same := HPosition.targetSame.symm.trans h6_lexical
  rw [H_prefix_empty] at same
  exact (Stack.spent.inj same).2.2.1

/-- These scopes are derived from actual full history selections. Historical
port presence for consumed H is not an evaluating CurrentScopeOrigin. -/
theorem original_spent_saved_scopes_typed :
    ScopedPorts.ScopeKnown originalTicketPorts K2Position.data.scope ∧
    ScopedPorts.ScopeKnown originalTicketPorts K1Position.data.scope ∧
    ScopedPorts.ScopeKnown originalTicketPorts HPosition.data.scope := by
  rw [K2_saved_scope,K1_saved_scope,H_saved_scope]
  exact ⟨⟨originalHTicket,original_H_scope_typed⟩,⟨originalHTicket,original_H_scope_typed⟩,⟨.none,.none⟩⟩

/-- Corrected annotations retain the SAME graph/runtime36/37 path, endpoint
pair heap and all exact observations/ownership proofs. This is local port typing. -/
theorem original_corrected_connected_trace :
    CoreAllocationHistory.Steps graph 36 s0.state h8.state ∧
    CoreAllocationHistory.Steps graph 37 (CoreCallableGeneratedChronology.start_before start).state h8.state ∧
    h8.state.control = .returned .unit ∧ h8.state.heap = [.pair .unit .unit] :=
  ⟨original_running_to_done,original_start_edge_to_done,final_saved_unit.1,final_pair_heap⟩

#print axioms original_product_annotations
#print axioms original_capture_port_projection
#print axioms original_allocated_ticket_ports
#print axioms original_product_initializer_port
#print axioms original_bind_suffix_port
#print axioms original_product_contexts
#print axioms original_product_plain_frames
#print axioms original_pair_value_port
#print axioms original_bind_actual_typed_composition
#print axioms original_wrong_unit_pair_output
#print axioms original_wrong_unit_bind_input
#print axioms original_spent_saved_scopes_typed
#print axioms original_corrected_connected_trace

/-- Parameter20 is unused, so a Unit-input suffix context is locally typable.
This does not type the actual Product initializer at Unit. -/
theorem unused_bind_unit_context_still_types :
    ScopedPorts.ContextTyped originalSignature [] ScopedPorts.TypeEnv.empty originalHTicket [.user 1 []]
      bindPlain.context .unit .unit := by
  exact .bind (.resume .unit (by simp) (by simp [ScopedPorts.InWorld,ScopedPorts.Port.resources]))

#print axioms unused_bind_unit_context_still_types
end Ash.OneShot.RestoredBindContinuationInterfaces.Connected
