import CoreCallableStrictCallerHeadConsumers
import CoreCallableStrictOutsideHeadConsumers
import CoreCallableGeneratedBindConsumers
import CoreCallableGeneratedCleanupCompletion
namespace Ash.OneShot.StrictCallerHeadCompatibilityInterfaces.Connected
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
private def bindPlain : PlainData := ⟨.bind 20 (.resume (ticket graph 0) .unit),callerScope,.unit,.unit,[0],rfl⟩
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
private def pairPlain : PlainData := ⟨.pairLeft requestK,callerScope,.unit,.unit,[],rfl⟩
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
private def returnPlain : PlainData := ⟨.pairRight .unit,callerScope,.unit,.unit,[],rfl⟩
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

theorem active_saved_map_and_scope : right.owners = callerOwners ∧ right.focus.scope = callerScope := ⟨rfl,rfl⟩
theorem original_selected_metadata : savedCallerHeadCheck bound.owners strictReady.plain.scope
    (location e2 captureK.index).owners (location e2 captureK.index).data.scope = true := returned.metadata

theorem original_outside_position : callerOutsideCheck bound.owners strictReady.plain.scope
    (dormant b2 captureK).kept = true := returned.position

theorem changed_tail_actual : CoreMachine.next graph (resume_result (resume_input a2 resumeReady)).after.state =
    .stepped right.state := CoreCallableStrictCallerHeadConsumers.right_actual returned

theorem changed_tail_positive : CoreUnwindRelation.Positive (resume_result (resume_input a2 resumeReady)).after.point.machine
    right.point.machine [] [] := CoreCallableStrictCallerHeadConsumers.right_positive returned

theorem original_to_changed_right : CoreAllocationHistory.Steps graph 19 s0.state right.state ∧
    CoreUnwindRelation.Trace s0.point.machine right.point.machine [.ticket 0,.ticket 1] [.ticket 1] :=
  CoreCallableStrictCallerHeadConsumers.complete_original_prefix returned

theorem physical_changed_tail : right.physical =
    [.tupleRight .unit,.bind 20 3 callerEnv,.handlerBoundary 8 callerEnv 1,
      .clauseBoundary 1 1 1 1 none,
      .clauseBoundary 0 0 0 0 (some [.handlerBoundary 9 (.binding 12 .unit .empty) 0]),
      .cleanupCompletion 0 .unit] := by
  change .tupleRight .unit :: ((dormant b2 captureK).kept ++ _) = _
  rw [kept_exact]
  rfl

theorem current_active_origin : EvaluatedScopeOrigins right := CoreCallableStrictCallerHeadConsumers.right_scopes returned

theorem full_selected_installation : HEq (resume_input a2 resumeReady).installation kData.installation := HEq.rfl

/-- Conditional classifier checks, not different admitted executions. -/
theorem active_empty_selected_map_refuses : savedCallerHeadCheck callerOwners callerScope [] callerScope = false := rfl

theorem selected_reset_scope_refuses : savedCallerHeadCheck callerOwners callerScope callerOwners .none = false := rfl

theorem different_enclosing_handler_refuses : savedCallerHeadCheck callerOwners callerScope
    [⟨1,1,ticket graph 1⟩] (.ticket (ticket graph 1) 1) = false := rfl

/-- Independently indexed saved metadata is accepted. This is an interface
countercheck to the old equality requirement, not a second reachable run. -/
theorem independent_saved_metadata_accepts : savedCallerHeadCheck callerOwners callerScope
    [⟨0,1,ticket graph 1⟩,⟨1,1,ticket graph 1⟩] (.ticket (ticket graph 1) 99) = true := rfl

theorem old_full_equality_refuses_same_metadata : selectedCallerCheck callerOwners callerScope
    [⟨0,1,ticket graph 1⟩,⟨1,1,ticket graph 1⟩] (.ticket (ticket graph 1) 99) = false := rfl

/-- The SAME original caller would be inside the complete original suffix; this
is a classifier countercheck, not a different capture execution. -/
theorem wrong_inside_classification : callerOutsideCheck callerOwners callerScope
    ((dormant b2 captureK).kept ++ s9.physical) = false := by
  rw [kept_exact]
  rfl

/-- Conditional first-static-pair barrier evidence; not an admitted run. -/
theorem same_pair_spent_blocks_original {handler owner oldOccurrence oldTicket newOccurrence newTicket : Nat}
    {oldSaved : Option (List CoreMachine.Frame)} {physical front outside : List CoreMachine.Frame}
    (different : oldTicket ≠ newTicket) :
    ¬ OwnerPath handler owner oldOccurrence oldTicket oldSaved
      (.clauseBoundary handler owner newOccurrence newTicket none :: physical) front outside :=
  CoreCallableCleanupReachableTransport.outside_static_shadow_obstruction different

theorem unit_result_metadata : (graph.nodes[6]'(by decide)).type = .unit ∧
    (graph.nodes[8]'(by decide)).type = .unit ∧ (graph.nodes[9]'(by decide)).type = .unit ∧
    (graph.nodes[10]'(by decide)).type = .function .unit .unit [] ∧
    (graph.nodes[5]'(by decide)).type = .product .unit .unit := ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms active_saved_map_and_scope
#print axioms original_selected_metadata
#print axioms original_outside_position
#print axioms changed_tail_actual
#print axioms changed_tail_positive
#print axioms original_to_changed_right
#print axioms physical_changed_tail
#print axioms current_active_origin
#print axioms full_selected_installation
#print axioms active_empty_selected_map_refuses
#print axioms selected_reset_scope_refuses
#print axioms different_enclosing_handler_refuses
#print axioms independent_saved_metadata_accepts
#print axioms old_full_equality_refuses_same_metadata
#print axioms wrong_inside_classification
#print axioms same_pair_spent_blocks_original
#print axioms unit_result_metadata
end Ash.OneShot.StrictCallerHeadCompatibilityInterfaces.Connected
