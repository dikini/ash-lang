import CoreCallableStrictCaptureConsumers
import CoreCallableGeneratedBindConsumers
namespace Ash.OneShot.StrictCaptureOriginInterfaces
open CoreCallableGeneratedChronology CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers CoreCallableStrictCaptureOrigins
open CoreSyntax CoreTranslation CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableGeneralHistory CoreCallableCallerBarriers CoreCallableRunningOccurrence CoreCallableReachableResume
open CoreCallableRunningCapture CoreCallableSiteLineage CoreCaptureEntry CoreRequestFrames CoreCallableCleanupOrigins
open CoreCallableCleanupReachableTransport CoreCleanupFrames

open CoreCallableGeneratedBindProducers CoreCallableGeneratedBindConsumers
namespace Connected
private def graph : Graph := ⟨[
  {originalId:=0,type:=.unit,effects:=[],source:=none,kind:=.unit},
  {originalId:=1,type:=.unit,effects:=[.user 0 []],source:=none,kind:=.request (.user 0 []) 0 0},
  {originalId:=2,type:=.unit,effects:=[],source:=none,kind:=.unit},
  {originalId:=3,type:=.unit,effects:=[],source:=none,kind:=.resume 0 0 .consumed 2},
  {originalId:=4,type:=.unit,effects:=[],source:=none,kind:=.handler 1 (.user 1 []) 3 []},
  {originalId:=5,type:=.product .unit .unit,effects:=[.user 0 []],source:=none,kind:=.tuple [1,1]},
  {originalId:=6,type:=.unit,effects:=[.user 0 []],source:=none,kind:=.bind ⟨12,.product .unit .unit⟩ 5 0},
  {originalId:=7,type:=.unit,effects:=[],source:=none,kind:=.handler 0 (.user 0 []) 6 [⟨0,.binder ⟨9,.unit⟩,0,4⟩]},
  {originalId:=8,type:=.function .unit .unit [],effects:=[],source:=none,kind:=.function ⟨8,.unit⟩ 7},
  {originalId:=9,type:=.function .unit .unit [],effects:=[],source:=none,kind:=.variable 5},
  {originalId:=10,type:=.unit,effects:=[],source:=none,kind:=.apply 9 0},
  {originalId:=11,type:=.unit,effects:=[],source:=none,kind:=.cleanup ⟨5,.function .unit .unit []⟩ 10 0},
  {originalId:=12,type:=.unit,effects:=[],source:=none,kind:=.bind ⟨5,.function .unit .unit []⟩ 8 11}
],12⟩
private def clauseBody : Code := .handle (.user 1 []) (.resume (ticket graph 0) .unit) .nil
private def clauses : Clauses := .cons 0 9 (ticket graph 0) clauseBody .nil
private def body : Code := .handle (.user 0 []) (.bind 12 (.pair (.perform (.user 0 []) 0 .unit) (.perform (.user 0 []) 0 .unit)) .unit) clauses
private def callback : Code := .lambda 8 body
private def closure : CoreMachine.Value := .closure 8 7 .empty
private def environment : Environment := .binding 5 closure .empty
private def base : CoreMachine.State := {control := .returned .unit}

private theorem callable : CallableCertificate graph 8 7 body := by
  refine ⟨⟨8,⟨8,.unit⟩,_,rfl,rfl,rfl⟩,⟨8,rfl⟩,?_⟩
  intro ticket
  simp [body,clauses,clauseBody,Code.dependencies,Clauses.dependencies,Syntax.without]

private theorem callback_value : ValueRel graph [] [] closure callback := by
  refine .closure (fuel := 6) (bodyCode := body) rfl callable .empty ?_
  simp [callback,body,clauses,clauseBody,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Clauses.freeNames,Instantiation.Effect.freeNames,Instantiation.Effect.resources,effectAtoms,Code.dependencies,Clauses.dependencies,Syntax.without]

private def action : ActionData := ⟨0,callback,callback_value.closed,.none,.unit,[]⟩

private theorem saved_callback : EnvCloses graph [] [] environment
    (.app (.variable 5) .unit) (.app callback .unit) := by
  refine .binding callback_value ?_
  simpa [Code.subst] using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .app callback .unit))

private theorem receipt : SavedCleanupOrigin graph [] [] 10 environment action [] := by
  refine ⟨?_,.inactive (CanonicalOwnerMap.empty graph)⟩
  exact .armed (site := 11) (node := graph.nodes[11]'(by decide)) rfl rfl rfl rfl saved_callback rfl callback_value

private noncomputable def start : RunningStartPast graph [] 10 environment action .unit .unit [] .nil := {
  predecessor := base,callerOwners := [],scope := .none
  installed := receipt,saved := .unit,originalHistory := .nil
  running := ⟨receipt,.unit⟩,sameInstalled := rfl
  actual := CoreGeneralRestoration.normal_start receipt.delayed (ValueRel.unit (owners := [])) (GeneralHistory.nil (graph := graph) (heap := [])).related .none }

private noncomputable def s0 : Endpoint graph := started start

private theorem ordered : CoreTranslationFuel.Postorder graph :=
  CoreTranslationFuel.checkShape_postorder graph (by rfl)

private noncomputable def enter : EntryInput s0 := {
  ordered := ordered,site := 10,environment := environment,node := graph.nodes[10]'(by decide),known := rfl
  nextIndex := 9,frame := .applyFunction 0 environment,kind := .application rfl,environmentSame := rfl
  control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl saved_callback }

private noncomputable def s1 := (entry_result enter).after
private noncomputable def literalFunction : LiteralInput s1 := {
  index := 9,environment := environment,code := callback,scope := .none
  literal := .lexicalVariable (node := graph.nodes[9]'(by decide)) rfl rfl (by
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
    observations := s1.state.observations ++ [.entered 9] } := by
  have concrete : CoreMachine.next graph s1.state = .stepped { s1.state with
      control := .returned closure
      observations := s1.state.observations ++ [.entered 9] } := rfl
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
  frameOwners := [],parameter := 8,body := 7,environment := .empty,value := .unit
  argument := .unit,bodyCode := body,scope := .none,function := callback_value,operand := .unit
  control := by rw [s4_exact]
  maps := rfl,focus := rfl }

private noncomputable def s5 := (beta_result apply).after


private def outerData : HandlerData := ⟨0,.user 0 [],clauses,.none,.unit,by
  simp [clauses,clauseBody,Clauses.dependencies,Code.dependencies,Syntax.ticketDependencies,Syntax.without,
    effectAtoms,Instantiation.Effect.resources]⟩

private noncomputable def outerPast : GeneralHandlerPast graph [] 7 (.binding 8 .unit .empty) outerData := {
  predecessor := s5.state,originalSuffix := s5.physical,originalMaps := none
  mapsSame := by intro maps impossible; cases impossible
  node := graph.nodes[7]'(by decide),handler := 0,effect := .user 0 [],body := 6
  clauses := [⟨0,.binder ⟨9,.unit⟩,0,4⟩],known := rfl,kind := rfl
  lineage := .inactive (.empty graph),origin := .inactive (.empty graph)
  header := .handler (fuel := 7) rfl rfl rfl (by
    exact .binding ValueRel.unit .empty)
  actual := rfl }

private noncomputable def enterOuter : HandlerInput s5 := {
  owners := [],ownersSame := rfl,site := 7,environment := .binding 8 .unit .empty
  data := outerData,installation := outerPast,predecessor := rfl,suffix := rfl
  code := .bind 12 (.pair (.perform (.user 0 []) 0 .unit) (.perform (.user 0 []) 0 .unit)) .unit,raw := .bind 12 (.pair (.perform (.user 0 []) 0 .unit) (.perform (.user 0 []) 0 .unit)) .unit
  rawClauses := clauses,fuel := 6,translated := rfl,siteTranslated := rfl
  lexical := .binding ValueRel.unit .empty
  control := rfl,empty := ⟨rfl,rfl⟩ }

private noncomputable def s6 := (handler_result enterOuter).after
private noncomputable def original_trace : Generated start s6 6 [] [] := by
  have g0 : Generated start s0 0 [] [] := .initial
  have g1 := Generated.next g0 (Operation.entry enter)
  have g2 := Generated.next g1 (Operation.literal literalFunction)
  have g3 := Generated.next g2 (Operation.swap changeArgument)
  have g4 := Generated.next g3 (Operation.literal literalArgument)
  have g5 := Generated.next g4 (Operation.beta apply)
  exact Generated.next g5 (Operation.handler enterOuter)

private def bindPlain : PlainData := ⟨.bind 12 .unit,.none,.unit,.unit,[],rfl⟩
private noncomputable def bindingReady : BindReady s6 := {
  site := 6,binder := ⟨12,.product .unit .unit⟩,initializer := 5,body := 0
  environment := .binding 8 .unit .empty,plain := bindPlain,node := graph.nodes[6]'(by decide)
  known := rfl,kind := rfl,fuel := 4
  rawInitializer := .pair (.perform (.user 0 []) 0 .unit) (.perform (.user 0 []) 0 .unit),rawBody := .unit
  initializerCode := .pair (.perform (.user 0 []) 0 .unit) (.perform (.user 0 []) 0 .unit),suffix := .unit
  initializerTranslated := rfl,bodyTranslated := rfl,closing := .binding ValueRel.unit .empty
  notValue := by simp [Code.IsValue]
  closed := by simp [ClosedExcept,Code.dependencies]
  context := rfl,control := rfl,empty := ⟨rfl,rfl⟩ }
private noncomputable def bindingInput := bind_from_generated ordered original_trace bindingReady
private noncomputable def bound := (bind_result bindingInput).after
private noncomputable def bound_trace : Generated start bound 7 [] [] := Generated.next original_trace (.bind bindingInput)
private theorem bound_control : bound.state.control = .evaluate 5 (.binding 8 .unit .empty) := by
  have actual : CoreMachine.next graph s6.state = .stepped {s6.state with
    control := .evaluate 5 (.binding 8 .unit .empty),frames := .bind 12 0 (.binding 8 .unit .empty) :: s6.physical,
    observations := s6.state.observations ++ [.entered 6]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((bind_result bindingInput).core.symm.trans actual)
  change (bind_result bindingInput).after.state.control = _
  rw [same]
private theorem bound_code : bound.focus = ⟨.pair (.perform (.user 0 []) 0 .unit) (.perform (.user 0 []) 0 .unit),.none,.nil⟩ := by
  have shapes := congrArg Configuration.expression bindingInput.empty.focus
  have code : bindingInput.past.contextCode = .pair (.perform (.user 0 []) 0 .unit) (.perform (.user 0 []) 0 .unit) := by
    exact (Code.bind.inj shapes).2.1.symm
  change (⟨bindingInput.past.contextCode,.none,.nil⟩ : Configuration) = _
  rw [code]
private noncomputable def original_prefix : Prefix graph bound := .generated ordered bound_trace
private def requestCode : Code := .perform (.user 0 []) 0 .unit
private def pairPlain : PlainData := ⟨.pairLeft requestCode,.none,.unit,.unit,[],rfl⟩
private noncomputable def strictReady : EntryReady .pair bound := {
  site := 5,left := 1,right := 1,environment := .binding 8 .unit .empty,plain := pairPlain
  node := graph.nodes[5]'(by decide),known := rfl,shape := rfl
  fuel := 2,rawLeft := requestCode,rawRight := requestCode,leftCode := requestCode,rightCode := requestCode
  leftTranslated := rfl,rightTranslated := rfl,closing := .binding ValueRel.unit .empty
  notValue := by simp [requestCode,Code.IsValue]
  context := rfl,control := bound_control,empty := ⟨rfl,bound_code⟩ }
private noncomputable def e0 := entry_after strictReady (original_prefix.receipt strictReady)
private noncomputable def b0 : BeforeCapture original_prefix strictReady e0 1 := .entered
private noncomputable def enterRequest : EntryInput e0 := {
  ordered := ordered,site := 1,environment := .binding 8 .unit .empty,node := graph.nodes[1]'(by decide),known := rfl
  nextIndex := 0,frame := .request (.user 0 []) 0 (.binding 8 .unit .empty)
  kind := .request rfl,environmentSame := rfl,control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl (.binding ValueRel.unit .empty) }
private noncomputable def e1 := (entry_result enterRequest).after
private noncomputable def b1 : BeforeCapture original_prefix strictReady e1 2 := .stable b0 (.entry enterRequest)
private def requestPlain : PlainData := ⟨.perform (.user 0 []) 0,.none,.unit,.unit,[],rfl⟩
private noncomputable def requestOperand : LiteralInput e1 := {
  index := 0,environment := .binding 8 .unit .empty,code := .unit,scope := .none
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (.binding ValueRel.unit .empty)
  control := rfl
  stack := by
    have frame : RequestRel graph [] [] (.request (.user 0 []) 0 (.binding 8 .unit .empty)) requestPlain :=
      .operand (requested := .user 0 []) (.binding ValueRel.unit .empty) rfl
    exact prepend_request frame (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed (pushed_mapped .nil) .none }
private noncomputable def e2 := (literal_result requestOperand).after
private noncomputable def b2 : BeforeCapture original_prefix strictReady e2 3 := .stable b1 (.literal requestOperand)
private theorem e2_returned : e2.state.control = .returned .unit := by
  have concrete : CoreMachine.next graph e1.state = .stepped {e1.state with
    control := .returned .unit,observations := e1.state.observations ++ [.entered 0]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((literal_result requestOperand).core.symm.trans concrete)
  change (literal_result requestOperand).after.state.control = .returned .unit
  rw [same]
private noncomputable def captureRequest : CaptureInput e2 := {
  index := ⟨0,by decide⟩,requested := .user 0 [],effect := .user 0 [],operation := 0
  selectedClause := ⟨0,.binder ⟨9,.unit⟩,0,4⟩,value := .unit,code := .unit
  environment := .binding 8 .unit .empty,plain := requestPlain,context := [],outward := [.user 0 []],result := .unit
  same := rfl,prefixScope := .skip rfl (.skip rfl .nil),route := .outside (by simp)
  lookup := rfl,selected := rfl,operand := .unit
  requestCarrier := .binding ValueRel.unit .empty,plainContext := rfl
  ready := by
    intro parameter binder body atClause
    cases atClause with
    | hit => simp [ClosedExcept,clauseBody,Code.dependencies,Clauses.dependencies,effectAtoms,Instantiation.Effect.resources]
    | pass different rest => exact False.elim (different rfl)
  control := e2_returned,maps := rfl,focus := rfl }
private noncomputable def capturedData := capture_data captureRequest
private noncomputable def e3 := (capture_result captureRequest).after
private noncomputable def a0 : AfterCapture captureRequest e3 1 := .captured
private theorem captured_argument : capturedData.argument.id = 9 := by
  have same : capturedData.argument = ⟨9,.unit⟩ := (CoreSyntax.Pattern.binder.inj capturedData.pattern).symm
  exact congrArg CoreSyntax.Binder.id same
private theorem one_clause_body {parameter binder : Nat} {code : Code}
    (selected : ClauseAt 0 clauses parameter binder code) : code = clauseBody := by
  cases selected with
  | hit => rfl
  | pass different rest => exact False.elim (different rfl)
private theorem captured_body : capturedData.body = clauseBody :=
  one_clause_body capturedData.clauseAt

private theorem e3_control : e3.state.control = .evaluate 4 (.binding 9 .unit (.binding 8 .unit .empty)) := by
  change CoreMachine.Control.evaluate 4 (.binding capturedData.argument.id .unit (.binding 8 .unit .empty)) = _
  rw [captured_argument]
private theorem e3_focus : e3.focus = ⟨clauseBody,.ticket (ticket graph 0) 0,.nil⟩ := by
  change (⟨capturedData.body.subst capturedData.argument.id .unit,.ticket (ticket graph 0) 0,.nil⟩ : Configuration) = _
  rw [captured_body,captured_argument]
  rfl

private def frontData : HandlerData := ⟨1,.user 1 [],.nil,.ticket (ticket graph 0) 0,.unit,rfl⟩
private noncomputable def frontPast : GeneralHandlerPast graph [⟨0,0,ticket graph 0⟩] 4
    (.binding 9 .unit (.binding 8 .unit .empty)) frontData := {
  predecessor := e3.state,originalSuffix := e3.physical,originalMaps := none
  mapsSame := by intro maps impossible; cases impossible
  node := graph.nodes[4]'(by decide),handler := 1,effect := .user 1 [],body := 3,clauses := []
  known := rfl,kind := rfl
  lineage := .clause (.empty graph) (handlerSite := 7) (node := graph.nodes[7]'(by decide)) rfl rfl (by decide)
  origin := .clause (.empty graph) (.hit _)
  header := .handler (fuel := 4) rfl rfl rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty))
  actual := rfl }

private noncomputable def enterFront : HandlerInput e3 := {
  owners := [⟨0,0,ticket graph 0⟩],ownersSame := rfl,site := 4
  environment := .binding 9 .unit (.binding 8 .unit .empty),data := frontData,installation := frontPast
  predecessor := rfl,suffix := rfl,code := .resume (ticket graph 0) .unit,raw := .resume (ticket graph 0) .unit
  rawClauses := .nil,fuel := 3,translated := rfl,siteTranslated := rfl
  lexical := .binding ValueRel.unit (.binding ValueRel.unit .empty)
  control := e3_control,empty := ⟨rfl,e3_focus⟩ }
private noncomputable def e4 := (handler_result enterFront).after

private noncomputable def enterResume : EntryInput e4 := {
  ordered := ordered,site := 3,environment := .binding 9 .unit (.binding 8 .unit .empty)
  node := graph.nodes[3]'(by decide),known := rfl,nextIndex := 2,frame := .resume 0 0
  kind := .resume rfl,environmentSame := trivial,control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty)) }
private noncomputable def e5 := (entry_result enterResume).after
private def resumePlain : PlainData := ⟨.resume (ticket graph 0),.ticket (ticket graph 0) 0,.unit,.unit,
  [0],rfl⟩
private theorem resumeFrame : CoreResumeFrames.ResumeRel graph [⟨0,0,ticket graph 0⟩] [] (.resume 0 0) resumePlain :=
  .operand (environment := .binding 9 .unit (.binding 8 .unit .empty)) (site := 3) (node := graph.nodes[3]'(by decide)) (fuel := 2) rfl rfl rfl rfl
    (.binding ValueRel.unit (.binding ValueRel.unit .empty)) rfl
private noncomputable def resumeOperand : LiteralInput e5 := {
  index := 2,environment := .binding 9 .unit (.binding 8 .unit .empty),code := .unit
  scope := .ticket (ticket graph 0) 0
  literal := .unit (node := graph.nodes[2]'(by decide)) rfl rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty))
  control := rfl
  stack := prepend_resume resumeFrame
    (ValueRel.unit (graph := graph) (owners := [⟨0,0,ticket graph 0⟩]) (heap := [])).closed
    (pushed_mapped .nil) (.ticket (ticket graph 0) 0) }
private noncomputable def e6 := (literal_result resumeOperand).after
private theorem e6_returned : e6.state.control = .returned .unit := by
  have concrete : CoreMachine.next graph e5.state = .stepped {e5.state with
    control := .returned .unit,observations := e5.state.observations ++ [.entered 2]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((literal_result resumeOperand).core.symm.trans concrete)
  change (literal_result resumeOperand).after.state.control = .returned .unit
  rw [same]

private noncomputable def a1 : AfterCapture captureRequest e4 2 := .handler a0 enterFront
private noncomputable def a2 : AfterCapture captureRequest e5 3 := .stable a1 (.entry enterResume)
private noncomputable def a3 : AfterCapture captureRequest e6 4 := .stable a2 (.literal resumeOperand)
private noncomputable def resumeReady : ResumeReady captureRequest e6 := {
  frameOwners := [⟨0,0,ticket graph 0⟩],plain := resumePlain,binder := ticket graph 0,frame := resumeFrame
  context := rfl,value := .unit,code := .unit,operand := .unit,resolve := rfl
  control := e6_returned,maps := rfl,focus := rfl }
private def returnPlain : PlainData := ⟨.pairRight .unit,.none,.unit,.unit,[],rfl⟩
private noncomputable def returnReady : CoreCallableStrictCaptureConsumers.ReturnedReady b2 captureRequest a3 resumeReady := {
  afterPlain := returnPlain,context := rfl,sameScope := rfl
  notValue := by simp [strictReady,requestCode,Code.IsValue]
  checked := rfl }
private noncomputable def resumed := (resume_result (resume_input a3 resumeReady)).after
private noncomputable def right := CoreCallableStrictCaptureConsumers.right_after returnReady

theorem actual_capture_has_pair_head :
    (capture_data captureRequest).installation.originalInside =
      [.tupleLeft 1 (.binding 8 .unit .empty),.bind 12 0 (.binding 8 .unit .empty)] :=
  (capture_data captureRequest).sameInside

noncomputable def actual_restored_head : HeadMember bound.owners (.tupleLeft 1 (.binding 8 .unit .empty)) pairPlain
    resumed.history (restored_tail b2 captureRequest a3) := restored_member b2 captureRequest a3 resumeReady

theorem changed_tail_actual : CoreMachine.next graph resumed.state = .stepped right.state :=
  CoreCallableStrictCaptureConsumers.right_actual returnReady

theorem changed_tail_positive : CoreUnwindRelation.Positive resumed.point.machine right.point.machine [] [] :=
  CoreCallableStrictCaptureConsumers.right_positive returnReady

theorem original_to_changed_right :
    CoreAllocationHistory.Steps graph 16 s0.state right.state ∧
    CoreUnwindRelation.Trace s0.point.machine right.point.machine [.ticket 0] [.ticket 0] :=
  CoreCallableStrictCaptureConsumers.complete_original_prefix returnReady

theorem saved_map_and_scope_restored : right.owners = [] ∧ right.focus.scope = .none := ⟨rfl,rfl⟩

theorem wrong_dynamic_occurrence (different : candidate ≠ e2.state.nextOwner)
    (wrong : resumeReady.plain.scope.resolve resumeReady.binder = some candidate) : False :=
  different (Option.some.inj (wrong.symm.trans resumeReady.resolve))

theorem wrong_selected_handler (different : candidate ≠ (location e2 captureRequest.index).installation.handler)
    (wrong : (resume_input a3 resumeReady).handler = candidate) : False := different wrong.symm

theorem wrong_selected_activation (different : candidate ≠ (location e2 captureRequest.index).data.activation)
    (wrong : (resume_input a3 resumeReady).occurrence = candidate) : False := different wrong.symm

private theorem kept_exact : (dormant b2 captureRequest).kept =
    [.bind 12 0 (.binding 8 .unit .empty),.handlerBoundary 7 (.binding 8 .unit .empty) 0] := by
  have same := dormant_original_tail b2 captureRequest
  have split : [.bind 12 0 (.binding 8 .unit .empty),.handlerBoundary 7 (.binding 8 .unit .empty) 0] ++
      [.cleanupCompletion 0 .unit] = (dormant b2 captureRequest).kept ++ [.cleanupCompletion 0 .unit] := same
  exact (List.append_cancel_right split).symm

theorem physical_changed_tail : right.physical =
    [.tupleRight .unit,.bind 12 0 (.binding 8 .unit .empty),.handlerBoundary 7 (.binding 8 .unit .empty) 0,
      .handlerBoundary 4 (.binding 9 .unit (.binding 8 .unit .empty)) 1,
      .clauseBoundary 0 0 0 0 none,.cleanupCompletion 0 .unit] := by
  change .tupleRight .unit :: ((dormant b2 captureRequest).kept ++ _) = _
  rw [kept_exact]
  rfl

theorem metadata_unit_result_retained :
    graph.nodes[8].type = .function .unit .unit [] ∧ graph.nodes[7].type = .unit ∧
    graph.nodes[6].kind = .bind ⟨12,.product .unit .unit⟩ 5 0 ∧
    graph.nodes[5].type = .product .unit .unit := ⟨rfl,rfl,rfl,rfl⟩

theorem actual_installation_membership : Nonempty
    (OrdinaryMember bound.owners (.tupleLeft 1 (.binding 8 .unit .empty)) pairPlain resumed.history) :=
  ⟨(restored_member b2 captureRequest a3 resumeReady).membership⟩

theorem same_full_selected_installation : HEq (resume_input a3 resumeReady).installation capturedData.installation := HEq.rfl

theorem wrong_original_capture_suffix (wrong : (resume_input a3 resumeReady).installation.originalInside = []) : False := by
  have actual : (resume_input a3 resumeReady).installation.originalInside =
      [.tupleLeft 1 (.binding 8 .unit .empty),.bind 12 0 (.binding 8 .unit .empty)] := actual_capture_has_pair_head
  have impossible := wrong.symm.trans actual
  cases impossible

#print axioms same_full_selected_installation
#print axioms wrong_original_capture_suffix
#print axioms physical_changed_tail
#print axioms metadata_unit_result_retained
#print axioms actual_installation_membership
#print axioms actual_capture_has_pair_head
#print axioms actual_restored_head
#print axioms changed_tail_actual
#print axioms changed_tail_positive
#print axioms original_to_changed_right
#print axioms saved_map_and_scope_restored
#print axioms wrong_dynamic_occurrence
#print axioms wrong_selected_handler
#print axioms wrong_selected_activation
end Connected
end Ash.OneShot.StrictCaptureOriginInterfaces
