import CoreCallableGeneratedCurrentScopeConsumers
import CoreCallableGeneratedTicketBound
import GeneratedNestedHandlerProbes
namespace Ash.OneShot.CoreCallableGeneratedCurrentScopeConsumers.Probes
open CoreCallableGeneratedChronology CoreCallableGeneratedTicketBound
open CoreCallableGeneratedSiteConsumers CoreCallableGeneralCleanupRegistration
open CoreCallableGeneralHistory CoreCallableFrameInstallations
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableCallerBarriers CoreCallableRunningOccurrence CoreCallableReachableResume
open CoreCallableSiteLineage CoreCaptureEntry CoreRequestFrames CoreCallableCleanupOrigins
open CoreCallableCleanupReachableTransport CoreCleanupFrames
namespace Cleanup
private def graph : Graph := ⟨[
  ⟨0,.unit,[],none,.unit⟩,
  ⟨1,.function .unit .unit [],[],none,.function ⟨8,.unit⟩ 0⟩,
  ⟨2,.function .unit .unit [],[],none,.variable 5⟩,
  ⟨3,.unit,[],none,.apply 2 0⟩,
  ⟨4,.unit,[],none,.cleanup ⟨5,.function .unit .unit []⟩ 3 0⟩,
  ⟨5,.unit,[],none,.unit⟩,
  ⟨6,.function .unit .unit [],[],none,.function ⟨9,.unit⟩ 4⟩,
  ⟨7,.function .unit .unit [],[],none,.variable 10⟩,
  ⟨8,.unit,[],none,.apply 7 0⟩,
  ⟨9,.unit,[],none,.cleanup ⟨10,.function .unit .unit []⟩ 8 0⟩,
  ⟨10,.unit,[],none,.bind ⟨10,.function .unit .unit []⟩ 6 9⟩],10⟩
private def innerCallback : Code := .lambda 8 .unit
private def innerClosure : CoreMachine.Value := .closure 8 0 .empty
private def captured : CoreMachine.Environment := .binding 5 innerClosure .empty
private def callback : Code := .lambda 9 (.cleanup innerCallback .unit)
private def closure : CoreMachine.Value := .closure 9 4 captured
private def environment : CoreMachine.Environment := .binding 10 closure captured

private theorem inner_callable : CallableCertificate graph 8 0 .unit := by
  refine ⟨⟨1,⟨8,.unit⟩,_,rfl,rfl,rfl⟩,⟨1,rfl⟩,?_⟩
  intro binder; simp [Code.dependencies,Syntax.without]
private theorem inner_value : ValueRel graph [] [] innerClosure innerCallback := by
  refine .closure (fuel := 1) (bodyCode := .unit) rfl inner_callable .empty ?_
  simp [innerCallback,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Syntax.without]
private theorem callable : CallableCertificate graph 9 4 (.cleanup (.variable 5) .unit) := by
  refine ⟨⟨6,⟨9,.unit⟩,_,rfl,rfl,rfl⟩,⟨6,rfl⟩,?_⟩
  intro binder; simp [Code.dependencies,Syntax.without]
private theorem callback_value : ValueRel graph [] [] closure callback := by
  refine .closure (fuel := 6) (bodyCode := .cleanup (.variable 5) .unit) rfl callable ?_ ?_
  · refine .binding inner_value ?_
    simpa [callback,innerCallback,Code.subst] using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := callback))
  · simp [callback,innerCallback,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Syntax.without]
private def action : ActionData := ⟨0,callback,callback_value.closed,.none,.unit,[]⟩
private theorem ordered : Postorder graph := checkShape_postorder graph (by rfl)
private def original : CoreMachine.State := {control := .evaluate 9 environment}
private theorem original_closing : EnvCloses graph [] [] environment
    (.cleanup (.variable 10) .unit) (.cleanup action.action .unit) := by
  refine .binding callback_value (.binding inner_value ?_)
  simpa [action,callback,innerCallback,Code.subst] using
    (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .cleanup callback .unit))
private theorem registered :
    ∃ past : GeneralRegisteredCleanupPast graph [] original 9 ⟨10,.function .unit .unit []⟩ 8 0 environment action [] .nil .unit .unit,
      past.identity = rfl := by
  obtain ⟨past,_sameHistory,_raw,_owned⟩ := general_register (graph := graph) (owners := []) (base := original) (data := action) (physical := []) (target := .nil) (site := 9) (body := 0) (action := 8) ordered (.inactive (.empty graph))
    (node := graph.nodes[9]'(by decide)) rfl rfl rfl (by rfl) original_closing
    (parameter := 9) (lambdaBody := .cleanup innerCallback .unit) rfl rfl
    ⟨TicketBound.empty _,.inactive (.empty graph)⟩ .nil
  exact ⟨past,Subsingleton.elim _ _⟩
private noncomputable def registration := Classical.choose registered
private def base : CoreMachine.State := {
  registeredState original 9 0 8 environment action [] with control := .returned .unit,observations := (registeredState original 9 0 8 environment action []).observations ++ [.entered 0]}
private theorem body_step : CoreMachine.next graph (registeredState original 9 0 8 environment action []) = .stepped base := rfl
private theorem receipt : SavedCleanupOrigin graph [] [] 8 environment action [] := registration.installed
private theorem saved_callback : EnvCloses graph [] [] environment
    (.app (.variable 10) .unit) (.app callback .unit) := by
  refine .binding callback_value (.binding inner_value ?_)
  simpa [callback,innerCallback,Code.subst] using
    (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .app callback .unit))
private noncomputable def start : RunningStartPast graph [] 8 environment action .unit .unit [] .nil := {
  predecessor := base,callerOwners := [],scope := .none
  installed := receipt,saved := .unit,originalHistory := .nil
  running := ⟨receipt,.unit⟩,sameInstalled := rfl
  actual := CoreGeneralRestoration.normal_start receipt.delayed (ValueRel.unit (owners := [])) (GeneralHistory.nil (graph := graph) (heap := [])).related .none }

private noncomputable def s0 : Endpoint graph := started start

private noncomputable def enter : EntryInput s0 := {
  ordered := ordered,site := 8,environment := environment,node := graph.nodes[8]'(by decide),known := rfl
  nextIndex := 7,frame := .applyFunction 0 environment,kind := .application rfl,environmentSame := rfl
  control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl saved_callback }

private noncomputable def s1 := (entry_result enter).after
private noncomputable def literalFunction : LiteralInput s1 := {
  index := 7,environment := environment,code := callback,scope := .none
  literal := .lexicalVariable (node := graph.nodes[7]'(by decide)) rfl rfl (by
    refine .binding callback_value (.binding inner_value ?_)
    simpa [s1,entry_result,enter,s0,started,start,base,startedState,Code.subst,callback,innerCallback,registeredState,original] using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := callback))) callback_value.closed
  control := rfl
  stack := by
    let plain : PlainData := ⟨.appFunction .unit,.none,.unit,.unit,[],rfl⟩
    have frame : PlainFrameRel graph [] [] (.applyFunction 0 environment) plain := by
      refine .applyFunction (fuel := 1) rfl ?_
      refine .binding callback_value (.binding inner_value ?_)
      simpa [Code.subst,callback,innerCallback] using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .unit))
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
    refine .binding callback_value (.binding inner_value ?_)
    simpa [s3,swap_result,changeArgument,s2,literal_result,s1,entry_result,enter,s0,started,start,base,startedState,Code.subst,callback,innerCallback,registeredState,original]
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
  frameOwners := [],parameter := 9,body := 4,environment := captured,value := .unit
  argument := .unit,bodyCode := .cleanup innerCallback .unit,scope := .none,function := callback_value,operand := .unit
  control := by rw [s4_exact]
  maps := rfl,focus := rfl }

private noncomputable def s5 := (beta_result apply).after


private noncomputable def prefixGenerated : Generated start s5 5 [] [] := by
  have g0 : Generated start s0 0 [] [] := .initial
  have g1 := Generated.next g0 (Operation.entry enter)
  have g2 := Generated.next g1 (Operation.literal literalFunction)
  have g3 := Generated.next g2 (Operation.swap changeArgument)
  have g4 := Generated.next g3 (Operation.literal literalArgument)
  exact Generated.next g4 (Operation.beta apply)

private def nestedAction : ActionData := ⟨1,innerCallback,inner_value.closed,.none,.unit,[]⟩
private noncomputable def nestedCurrent : CleanupReady s5 := {
  site := 4,callback := ⟨5,.function .unit .unit []⟩,action := 3,body := 0
  environment := .binding 9 .unit captured,data := nestedAction,node := graph.nodes[4]'(by decide)
  known := rfl,kind := rfl,shape := rfl
  rawBody := .unit,bodyCode := .unit,translated := rfl
  closing := by
    change EnvCloses graph [] [] (.binding 9 .unit captured) (.cleanup (.variable 5) .unit) (.cleanup innerCallback .unit)
    refine .binding (ValueRel.unit (owners := [])) (.binding inner_value ?_)
    simpa [Code.subst,nestedAction,innerCallback] using
      (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .cleanup innerCallback .unit))
  parameter := 8,lambdaBody := .unit,callable := rfl,identity := rfl
  control := rfl,empty := ⟨rfl,rfl⟩ }

private noncomputable def registerNested := cleanup_from_current_scope ordered prefixGenerated (TicketBound.empty _) nestedCurrent
private noncomputable def nestedEndpoint := (cleanup_result registerNested).after
private noncomputable def nestedGenerated : Generated start nestedEndpoint 6 [.cleanup 1] [] :=
  .next prefixGenerated (.cleanup registerNested)

theorem preceding_origins : EvaluatedScopeOrigins s5 := prefixGenerated.current_evaluating_scope

theorem cleanup_without_current_guards : CoreMachine.next graph s5.state = .stepped nestedEndpoint.state ∧
    Matching graph s5 nestedEndpoint [.cleanup 1] [] := cleanup_actual ordered prefixGenerated (TicketBound.empty _) nestedCurrent

theorem same_input_history : (cleanup_data registerNested).past.history = s5.history :=
  cleanup_history_same ordered prefixGenerated (TicketBound.empty _) nestedCurrent

theorem exact_fresh_key_and_frames : s5.state.nextCleanup = 1 ∧ nestedEndpoint.state.nextCleanup = 2 ∧
    nestedEndpoint.state.frames = [.cleanupBoundary 3 (.binding 9 .unit captured) 1,.cleanupCompletion 0 .unit] :=
  ⟨rfl,rfl,rfl⟩

theorem connected_seven_steps : CoreAllocationHistory.Steps graph 7 (start_before start).state nestedEndpoint.state :=
  nestedGenerated.from_actual_start.1

theorem original_running_retained : RunningReceipt graph [] nestedEndpoint.state.heap 8 environment action .unit .unit [] :=
  nestedGenerated.retained_running_receipt

#print axioms preceding_origins
#print axioms cleanup_without_current_guards
#print axioms same_input_history
#print axioms exact_fresh_key_and_frames
#print axioms connected_seven_steps
#print axioms original_running_retained
end Cleanup
namespace Handler
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


private def frontData : HandlerData := ⟨1,.user 1 [],.nil,.ticket (ticket graph 0) 0,.unit,rfl⟩
private noncomputable def frontCurrent : HandlerReady s9 := {
  site := 4,environment := .binding 9 .unit (.binding 8 .unit .empty),data := frontData
  node := graph.nodes[4]'(by decide),handler := 1,effect := .user 1 [],body := 3,clauses := []
  known := rfl,kind := rfl,code := .resume (ticket graph 0) .unit,raw := .resume (ticket graph 0) .unit
  rawClauses := .nil,fuel := 3,translated := rfl,siteTranslated := rfl
  lexical := .binding ValueRel.unit (.binding ValueRel.unit .empty)
  activation := rfl
  control := s9_control,empty := ⟨rfl,s9_focus⟩ }
private noncomputable def front := handler_from_current_scope ordered captured_trace frontCurrent

theorem active_clause_occurrence : CurrentScopeOrigin graph [⟨0,0,ticket graph 0⟩] (.ticket (ticket graph 0) 0) s9.physical := by
  have site := captured_trace.current_evaluating_scope.at s9_control
  have owners : s9.owners = [⟨0,0,ticket graph 0⟩] := rfl
  simpa only [s9_focus,owners] using site

theorem handler_without_current_guards : CoreMachine.next graph s9.state = .stepped (handler_result front).after.state ∧
    Matching graph s9 (handler_result front).after [] [] := handler_actual ordered captured_trace frontCurrent

theorem actual_original_suffix : front.installation.predecessor = s9.state ∧
    front.installation.originalSuffix = s9.physical ∧ front.installation.body = 3 :=
  by
    refine ⟨front.predecessor,front.suffix,?_⟩
    unfold front handler_from_current_scope handler_from_generated
    exact (handler_data_from_generated ordered captured_trace _).body

private noncomputable def afterHandler : Generated start (handler_result front).after 10 [.ticket 0] [] :=
  .next captured_trace (.handler front)

theorem produced_handler_scope : EvaluatedScopeOrigins (handler_result front).after :=
  afterHandler.current_evaluating_scope

theorem wrong_dynamic_ticket : ¬ CurrentScopeOrigin graph [⟨0,0,ticket graph 0⟩]
    (.ticket (ticket graph 0) 1) s9.physical := by
  intro origin
  cases origin with
  | clause canonical path =>
    have impossible : (1 : Nat) = 0 := OwnerPath.first_pair_ticket path
    exact Nat.noConfusion impossible

#print axioms active_clause_occurrence
#print axioms handler_without_current_guards
#print axioms actual_original_suffix
#print axioms produced_handler_scope
#print axioms wrong_dynamic_ticket
end Handler

private noncomputable def traceEndpoint {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (_run : Generated start current count created discharged) : Endpoint graph := current

private noncomputable def resumedEndpoint :=
  traceEndpoint CoreCallableGeneratedCleanupCompletion.Nested.resumed_trace

theorem exported_resumed_returned : resumedEndpoint.state.control = .returned .unit ∧
    EvaluatingScopeOrigin resumedEndpoint ∧ resumedEndpoint.maps = [] :=
  ⟨rfl,CoreCallableGeneratedCleanupCompletion.Nested.resumed_trace.current_evaluating_scope.evaluating,rfl⟩

theorem exported_resumed_actual_frames : resumedEndpoint.state.frames =
    [.handlerBoundary 5 (.binding 8 .unit .empty) 0,
     .handlerBoundary 4 (.binding 9 .unit (.binding 8 .unit .empty)) 1,
     .clauseBoundary 0 0 0 0 none,.cleanupCompletion 0 .unit] :=
  CoreCallableGeneratedCleanupCompletion.Nested.nested_full_prefix

#print axioms exported_resumed_returned
#print axioms exported_resumed_actual_frames
end Ash.OneShot.CoreCallableGeneratedCurrentScopeConsumers.Probes
