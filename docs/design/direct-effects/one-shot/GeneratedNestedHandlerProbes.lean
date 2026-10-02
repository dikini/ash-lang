import CoreCallableGeneratedCleanupCompletion
namespace Ash.OneShot.CoreCallableGeneratedCleanupCompletion.Nested
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
  {originalId:=4,type:=.unit,effects:=[],source:=none,kind:=.handler 1 (.user 1 []) 3 []},
  {originalId:=5,type:=.unit,effects:=[],source:=none,kind:=.handler 0 (.user 0 []) 1 [⟨0,.binder ⟨9,.unit⟩,0,4⟩]},
  {originalId:=6,type:=.function .unit .unit [],effects:=[],source:=none,kind:=.function ⟨8,.unit⟩ 5},
  {originalId:=7,type:=.function .unit .unit [],effects:=[],source:=none,kind:=.variable 5},
  {originalId:=8,type:=.unit,effects:=[],source:=none,kind:=.apply 7 0},
  {originalId:=9,type:=.unit,effects:=[],source:=none,kind:=.cleanup ⟨5,.function .unit .unit []⟩ 8 0},
  {originalId:=10,type:=.unit,effects:=[],source:=none,kind:=.bind ⟨5,.function .unit .unit []⟩ 6 9}
],10⟩
private def clauseBody : Code := .handle (.user 1 []) (.resume (ticket graph 0) .unit) .nil
private def clauses : Clauses := .cons 0 9 (ticket graph 0) clauseBody .nil
private def body : Code := .handle (.user 0 []) (.perform (.user 0 []) 0 .unit) clauses
private def callback : Code := .lambda 8 body
private def closure : CoreMachine.Value := .closure 8 5 .empty
private def environment : Environment := .binding 5 closure .empty
private def base : CoreMachine.State := {control := .returned .unit}

private theorem callable : CallableCertificate graph 8 5 body := by
  refine ⟨⟨6,⟨8,.unit⟩,_,rfl,rfl,rfl⟩,⟨6,rfl⟩,?_⟩
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

private theorem receipt : SavedCleanupOrigin graph [] [] 8 environment action [] := by
  refine ⟨?_,.inactive (CanonicalOwnerMap.empty graph)⟩
  exact .armed (site := 9) (node := graph.nodes[9]'(by decide)) rfl rfl rfl rfl saved_callback rfl callback_value

private noncomputable def start : RunningStartPast graph [] 8 environment action .unit .unit [] .nil := {
  predecessor := base,callerOwners := [],scope := .none
  installed := receipt,saved := .unit,originalHistory := .nil
  running := ⟨receipt,.unit⟩,sameInstalled := rfl
  actual := CoreGeneralRestoration.normal_start receipt.delayed (ValueRel.unit (owners := [])) (GeneralHistory.nil (graph := graph) (heap := [])).related .none }

private noncomputable def s0 : Endpoint graph := started start

private theorem ordered : CoreTranslationFuel.Postorder graph :=
  CoreTranslationFuel.checkShape_postorder graph (by rfl)

private noncomputable def enter : EntryInput s0 := {
  ordered := ordered,site := 8,environment := environment,node := graph.nodes[8]'(by decide),known := rfl
  nextIndex := 7,frame := .applyFunction 0 environment,kind := .application rfl,environmentSame := rfl
  control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl saved_callback }

private noncomputable def s1 := (entry_result enter).after
private noncomputable def literalFunction : LiteralInput s1 := {
  index := 7,environment := environment,code := callback,scope := .none
  literal := .lexicalVariable (node := graph.nodes[7]'(by decide)) rfl rfl (by
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
    observations := s1.state.observations ++ [.entered 7] } := by
  have concrete : CoreMachine.next graph s1.state = .stepped { s1.state with
      control := .returned closure
      observations := s1.state.observations ++ [.entered 7] } := rfl
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
  frameOwners := [],parameter := 8,body := 5,environment := .empty,value := .unit
  argument := .unit,bodyCode := body,scope := .none,function := callback_value,operand := .unit
  control := by rw [s4_exact]
  maps := rfl,focus := rfl }

private noncomputable def s5 := (beta_result apply).after


private def outerData : HandlerData := ⟨0,.user 0 [],clauses,.none,.unit,by
  simp [clauses,clauseBody,Clauses.dependencies,Code.dependencies,Syntax.ticketDependencies,Syntax.without,
    effectAtoms,Instantiation.Effect.resources]⟩

private noncomputable def outerPast : GeneralHandlerPast graph [] 5 (.binding 8 .unit .empty) outerData := {
  predecessor := s5.state,originalSuffix := s5.physical,originalMaps := none
  mapsSame := by intro maps impossible; cases impossible
  node := graph.nodes[5]'(by decide),handler := 0,effect := .user 0 [],body := 1
  clauses := [⟨0,.binder ⟨9,.unit⟩,0,4⟩],known := rfl,kind := rfl
  lineage := .inactive (.empty graph),origin := .inactive (.empty graph)
  header := .handler (fuel := 7) rfl rfl rfl (by
    exact .binding ValueRel.unit .empty)
  actual := rfl }

private noncomputable def enterOuter : HandlerInput s5 := {
  owners := [],ownersSame := rfl,site := 5,environment := .binding 8 .unit .empty
  data := outerData,installation := outerPast,predecessor := rfl,suffix := rfl
  code := .perform (.user 0 []) 0 .unit,raw := .perform (.user 0 []) 0 .unit
  rawClauses := clauses,fuel := 6,translated := rfl,siteTranslated := rfl
  lexical := .binding ValueRel.unit .empty
  control := rfl,empty := ⟨rfl,rfl⟩ }

private noncomputable def s6 := (handler_result enterOuter).after
private noncomputable def enterRequest : EntryInput s6 := {
  ordered := ordered,site := 1,environment := .binding 8 .unit .empty,node := graph.nodes[1]'(by decide),known := rfl
  nextIndex := 0,frame := .request (.user 0 []) 0 (.binding 8 .unit .empty)
  kind := .request rfl,environmentSame := rfl,control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl (.binding ValueRel.unit .empty) }
private noncomputable def s7 := (entry_result enterRequest).after
private def requestPlain : PlainData := ⟨.perform (.user 0 []) 0,.none,.unit,.unit,[],rfl⟩
private noncomputable def requestOperand : LiteralInput s7 := {
  index := 0,environment := .binding 8 .unit .empty,code := .unit,scope := .none
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (.binding ValueRel.unit .empty)
  control := rfl
  stack := by
    have frame : RequestRel graph [] [] (.request (.user 0 []) 0 (.binding 8 .unit .empty)) requestPlain :=
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
  selectedClause := ⟨0,.binder ⟨9,.unit⟩,0,4⟩,value := .unit,code := .unit
  environment := .binding 8 .unit .empty,plain := requestPlain,context := [],outward := [.user 0 []],result := .unit
  same := rfl,prefixScope := .nil,route := .outside (by simp)
  lookup := rfl,selected := rfl,operand := .unit
  requestCarrier := .binding ValueRel.unit .empty,plainContext := rfl
  ready := by
    intro parameter binder body atClause
    cases atClause with
    | hit =>
      simp [ClosedExcept,clauseBody,Code.dependencies,Clauses.dependencies,effectAtoms,Instantiation.Effect.resources]
    | pass different rest => exact False.elim (different rfl)
  control := s8_returned,maps := rfl,focus := rfl }
private noncomputable def s9 := (capture_result captureRequest).after

private noncomputable def capturedData := capture_data captureRequest
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

private theorem s9_control : s9.state.control = .evaluate 4 (.binding 9 .unit (.binding 8 .unit .empty)) := by
  change CoreMachine.Control.evaluate 4 (.binding capturedData.argument.id .unit (.binding 8 .unit .empty)) = _
  rw [captured_argument]
private theorem s9_focus : s9.focus = ⟨clauseBody,.ticket (ticket graph 0) 0,.nil⟩ := by
  change (⟨capturedData.body.subst capturedData.argument.id .unit,.ticket (ticket graph 0) 0,.nil⟩ : Configuration) = _
  rw [captured_body,captured_argument]
  rfl

private def frontData : HandlerData := ⟨1,.user 1 [],.nil,.ticket (ticket graph 0) 0,.unit,rfl⟩
private noncomputable def frontPast : GeneralHandlerPast graph [⟨0,0,ticket graph 0⟩] 4
    (.binding 9 .unit (.binding 8 .unit .empty)) frontData := {
  predecessor := s9.state,originalSuffix := s9.physical,originalMaps := none
  mapsSame := by intro maps impossible; cases impossible
  node := graph.nodes[4]'(by decide),handler := 1,effect := .user 1 [],body := 3,clauses := []
  known := rfl,kind := rfl
  lineage := .clause (.empty graph) (handlerSite := 5) (node := graph.nodes[5]'(by decide)) rfl rfl (by decide)
  origin := .clause (.empty graph) (.hit _)
  header := .handler (fuel := 4) rfl rfl rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty))
  actual := rfl }

private noncomputable def enterFront : HandlerInput s9 := {
  owners := [⟨0,0,ticket graph 0⟩],ownersSame := rfl,site := 4
  environment := .binding 9 .unit (.binding 8 .unit .empty),data := frontData,installation := frontPast
  predecessor := rfl,suffix := rfl,code := .resume (ticket graph 0) .unit,raw := .resume (ticket graph 0) .unit
  rawClauses := .nil,fuel := 3,translated := rfl,siteTranslated := rfl
  lexical := .binding ValueRel.unit (.binding ValueRel.unit .empty)
  control := s9_control,empty := ⟨rfl,s9_focus⟩ }
private noncomputable def s10 := (handler_result enterFront).after

private noncomputable def enterResume : EntryInput s10 := {
  ordered := ordered,site := 3,environment := .binding 9 .unit (.binding 8 .unit .empty)
  node := graph.nodes[3]'(by decide),known := rfl,nextIndex := 2,frame := .resume 0 0
  kind := .resume rfl,environmentSame := trivial,control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty)) }
private noncomputable def s11 := (entry_result enterResume).after
private def resumePlain : PlainData := ⟨.resume (ticket graph 0),.ticket (ticket graph 0) 0,.unit,.unit,
  [0],rfl⟩
private theorem resumeFrame : CoreResumeFrames.ResumeRel graph [⟨0,0,ticket graph 0⟩] [] (.resume 0 0) resumePlain :=
  .operand (environment := .binding 9 .unit (.binding 8 .unit .empty)) (site := 3) (node := graph.nodes[3]'(by decide)) (fuel := 2) rfl rfl rfl rfl
    (.binding ValueRel.unit (.binding ValueRel.unit .empty)) rfl
private noncomputable def resumeOperand : LiteralInput s11 := {
  index := 2,environment := .binding 9 .unit (.binding 8 .unit .empty),code := .unit
  scope := .ticket (ticket graph 0) 0
  literal := .unit (node := graph.nodes[2]'(by decide)) rfl rfl (.binding ValueRel.unit (.binding ValueRel.unit .empty))
  control := rfl
  stack := prepend_resume resumeFrame
    (ValueRel.unit (graph := graph) (owners := [⟨0,0,ticket graph 0⟩]) (heap := [])).closed
    (pushed_mapped .nil) (.ticket (ticket graph 0) 0) }
private noncomputable def s12 := (literal_result resumeOperand).after
private theorem s12_returned : s12.state.control = .returned .unit := by
  have concrete : CoreMachine.next graph s11.state = .stepped {s11.state with
    control := .returned .unit,observations := s11.state.observations ++ [.entered 2]} := rfl
  have same := CoreMachine.Outcome.stepped.inj ((literal_result resumeOperand).core.symm.trans concrete)
  change (literal_result resumeOperand).after.state.control = .returned .unit
  rw [same]

private noncomputable def selected := location s8 captureRequest.index
private noncomputable def savedCapture := selected.before.append (.handler selected.installation selected.header .nil)
private noncomputable def resumeSelected : ResumeInput s12 := {
  handler := 0,owner := 0,occurrence := 0,dynamicTicket := 0,savedOwners := []
  frameOwners := [⟨0,0,ticket graph 0⟩],data := outerData,result := .unit
  captured := [.handlerBoundary 5 (.binding 8 .unit .empty) 0]
  capturedTarget := selected.front.append (.push (.handler selected.data) .nil)
  installation := capturedData.installation,header := capturedData.header,capturedHistory := savedCapture
  outside := selected.outside,tail := selected.tail,outsideHistory := selected.after
  front := [.handlerBoundary 4 (.binding 9 .unit (.binding 8 .unit .empty)) 1]
  frontTarget := .push (.handler frontData) .nil
  frontHistory := .handler frontPast frontPast.header .nil
  pass := .handler frontPast frontPast.header .nil .nil
  physical := rfl,lexical := rfl
  split := .handler frontPast frontPast.header _ _ .here
  plain := resumePlain,binder := ticket graph 0,frame := resumeFrame,context := rfl
  value := .unit,code := .unit,operand := .unit,resolve := rfl
  control := s12_returned,maps := rfl,focus := rfl }
private noncomputable def s13 := (resume_result resumeSelected).after

private noncomputable def spentOutside := GeneralHistory.spent capturedData.installation capturedData.header selected.after
private noncomputable def frontRest := (GeneralHistory.handler frontPast frontPast.header .nil).append spentOutside
private noncomputable def outerRest := (GeneralHistory.nil (graph := graph) (heap := [])).append frontRest
private noncomputable def returnOuter : HandlerReturnInput s13 := {
  owners := [],site := 5,environment := .binding 8 .unit .empty,data := outerData
  installation := selected.installation,header := selected.header
  suffixPhysical := [.handlerBoundary 4 (.binding 9 .unit (.binding 8 .unit .empty)) 1,
    .clauseBoundary 0 0 0 0 none,.cleanupCompletion action.identity .unit]
  suffixTarget := .push (.handler frontData) (.spent 0 .unit .none (.push (.running action .unit start.running.value.closed) .nil))
  suffix := outerRest,value := .unit,code := .unit,scope := .ticket (ticket graph 0) 0,operand := .unit
  control := rfl,empty := ⟨rfl,rfl⟩,physical := rfl,lexical := rfl
  head := .append _ _ _ (.emptyPrefix _ _ (.here .nil)) }
private noncomputable def s14 := (handler_return_result returnOuter).after
private noncomputable def afterFront := (GeneralHistory.nil (graph := graph) (heap := [])).append spentOutside
private noncomputable def returnFront : HandlerReturnInput s14 := {
  owners := [⟨0,0,ticket graph 0⟩],site := 4,environment := .binding 9 .unit (.binding 8 .unit .empty),data := frontData
  installation := frontPast,header := frontPast.header
  suffixPhysical := [.clauseBoundary 0 0 0 0 none,.cleanupCompletion action.identity .unit]
  suffixTarget := .spent 0 .unit .none (.push (.running action .unit start.running.value.closed) .nil)
  suffix := afterFront,value := .unit,code := .unit,scope := .none,operand := .unit
  control := rfl,empty := ⟨rfl,rfl⟩,physical := rfl,lexical := rfl
  head := .emptyPrefix _ _ (.append _ _ _ (.here .nil)) }
private noncomputable def s15 := (handler_return_result returnFront).after
private noncomputable def returnSpent : SpentReturnInput s15 := {
  owners := [],handler := 0,owner := 0,occurrence := 0,dynamicTicket := 0
  captured := [.handlerBoundary 5 (.binding 8 .unit .empty) 0],data := outerData
  installation := capturedData.installation,header := capturedData.header
  suffixPhysical := [.cleanupCompletion action.identity .unit]
  suffixTarget := .push (.running action .unit start.running.value.closed) .nil
  suffix := selected.after,value := .unit,code := .unit,scope := .ticket (ticket graph 0) 0,operand := .unit
  control := rfl,empty := ⟨rfl,rfl⟩,physical := rfl,lexical := rfl
  head := .emptyPrefix _ _ (.here _) }
private noncomputable def s16 := (spent_return_result returnSpent).after

noncomputable def captured_trace : Generated start s9 9 [.ticket 0] [] := by
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

noncomputable def clause_operand_trace : Generated start s12 12 [.ticket 0] [] := by
  have g10 := Generated.next captured_trace (Operation.handler enterFront)
  have g11 := Generated.next g10 (Operation.entry enterResume)
  exact Generated.next g11 (Operation.literal resumeOperand)
noncomputable def resumed_trace : Generated start s13 13 [.ticket 0] [.ticket 0] :=
  Generated.next clause_operand_trace (Operation.resume resumeSelected)
noncomputable def nested_returned : Generated start s16 16 [.ticket 0] [.ticket 0] := by
  have g14 := Generated.next resumed_trace (Operation.handlerReturn returnOuter)
  have g15 := Generated.next g14 (Operation.handlerReturn returnFront)
  exact Generated.next g15 (Operation.spentReturn returnSpent)

private noncomputable def finishNested : FinishInput nested_returned := {
  head := .append _ _ (.running start.running)
  activation := .inactive nested_returned rfl []
  scope := .none,control := rfl,empty := ⟨rfl,rfl⟩ }
noncomputable def nested_completed : Completed start (finish_result finishNested).after 17
    [.ticket 0] [.cleanup action.identity,.ticket 0] :=
  .finish nested_returned finishNested

/-- Full actual current prefix restoration: captured handler, intervening
clause handler, SAME spent marker, and SAME running completion. -/
theorem nested_full_prefix : s13.state.frames =
    [.handlerBoundary 5 (.binding 8 .unit .empty) 0,
     .handlerBoundary 4 (.binding 9 .unit (.binding 8 .unit .empty)) 1,
     .clauseBoundary 0 0 0 0 none,.cleanupCompletion action.identity .unit] := rfl

theorem nested_original_receipt_through_path :
    RunningReceipt graph [] s9.state.heap 8 environment action .unit .unit [] ∧
    RunningReceipt graph [] s12.state.heap 8 environment action .unit .unit [] ∧
    RunningReceipt graph [] s13.state.heap 8 environment action .unit .unit [] ∧
    RunningReceipt graph [] s16.state.heap 8 environment action .unit .unit [] :=
  ⟨captured_trace.retained_running_receipt,clause_operand_trace.retained_running_receipt,
    resumed_trace.retained_running_receipt,nested_returned.retained_running_receipt⟩

theorem nested_through_finish :
    CoreAllocationHistory.Steps graph 18 (start_before start).state (finish_result finishNested).after.state ∧
    CoreUnwindRelation.Trace (start_before start).point.machine (finish_result finishNested).after.point.machine
      [.ticket 0] [.cleanup action.identity,.ticket 0] ∧
    (finish_result finishNested).after.state.control = .returned .unit ∧
    (finish_result finishNested).after.state.frames = [] ∧
    CurrentOwnership graph [] (finish_result finishNested).after.state .none .nil := by
  refine ⟨nested_completed.from_actual_start.1,nested_completed.from_actual_start.2,
    (finish_restores_saved finishNested).1,(finish_restores_saved finishNested).2.2,?_⟩
  apply finish_current_ownership finishNested
  intro ticket
  simp [s16,spent_return_result,returnSpent,selected,location,s8,literal_result,s7,entry_result,enterRequest,
    s6,handler_result,enterOuter,s5,beta_result,apply,s4,literal_result,s3,swap_result,changeArgument,
    s2,literal_result,s1,entry_result,enter,s0,started,start,Stack.erase,ExecFrame.erase,Control.ticketNames]

#print axioms captured_trace
#print axioms clause_operand_trace
#print axioms resumed_trace
#print axioms nested_returned
#print axioms nested_completed
#print axioms nested_full_prefix
#print axioms nested_original_receipt_through_path
#print axioms nested_through_finish
end Ash.OneShot.CoreCallableGeneratedCleanupCompletion.Nested
