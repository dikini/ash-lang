import GeneratedOutsideActivationConsumers
namespace Ash.OneShot.GeneratedOutsideActivationProbes
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneratedChronology CoreCallableReachableResume
open CoreCallableCleanupOrigins CoreCallableSiteLineage CoreCallableGeneralHistory CoreCallableRunningOccurrence
open CoreGeneralRestoration CoreCallableGeneratedCurrentScopeConsumers CoreCallableInitialChronology
open GeneratedOutsideActivationOrigins GeneratedOutsideActivationConsumers

def graph : Graph := ⟨[
  {originalId:=0,type:=.unit,effects:=[],source:=none,kind:=.unit},
  {originalId:=1,type:=.unit,effects:=[],source:=none,kind:=.resume 1 1 .consumed 0},
  {originalId:=2,type:=.unit,effects:=[.user 1 []],source:=none,kind:=.request (.user 1 []) 0 0},
  {originalId:=3,type:=.function .unit .unit [.user 1 []],effects:=[],source:=none,kind:=.function ⟨8,.unit⟩ 2},
  {originalId:=4,type:=.function .unit .unit [.user 1 []],effects:=[],source:=none,kind:=.variable 5},
  {originalId:=5,type:=.unit,effects:=[.user 1 []],source:=none,kind:=.apply 4 0},
  {originalId:=6,type:=.unit,effects:=[.user 1 []],source:=none,kind:=.cleanup ⟨5,.function .unit .unit [.user 1 []]⟩ 5 0},
  {originalId:=7,type:=.unit,effects:=[.user 1 []],source:=none,kind:=.handler 1 (.user 1 []) 6 [⟨0,.binder ⟨10,.unit⟩,1,1⟩]},
  {originalId:=8,type:=.unit,effects:=[.user 0 []],source:=none,kind:=.request (.user 0 []) 0 0},
  {originalId:=9,type:=.unit,effects:=[.user 1 []],source:=none,kind:=.handler 0 (.user 0 []) 8 [⟨0,.binder ⟨9,.unit⟩,0,7⟩]},
  {originalId:=10,type:=.unit,effects:=[.user 1 []],source:=none,kind:=.bind ⟨5,.function .unit .unit [.user 1 []]⟩ 3 9}
],10⟩
def callback : Code := .lambda 8 (.perform (.user 1 []) 0 .unit)
def innerClauses : Clauses := .cons 0 10 (ticket graph 1) (.resume (ticket graph 1) .unit) .nil
def innerCode : Code := .handle (.user 1 []) (.cleanup (.variable 5) .unit) innerClauses
def outerClauses : Clauses := .cons 0 9 (ticket graph 0) innerCode .nil
def outerCode : Code := .handle (.user 0 []) (.perform (.user 0 []) 0 .unit) outerClauses
def original : Code := .bind 5 callback outerCode
theorem initialInput : InitialInput graph original := ⟨rfl,rfl⟩
private theorem callable : CallableCertificate graph 8 2 (.perform (.user 1 []) 0 .unit) := by
  refine ⟨⟨3,⟨8,.unit⟩,_,rfl,rfl,rfl⟩,⟨3,rfl⟩,?_⟩
  intro ticket; simp [Code.dependencies,effectAtoms,Instantiation.Effect.resources,Syntax.without]
private theorem callback_closed : ClosedValue callback := by
  simp [callback,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Instantiation.Effect.freeNames,effectAtoms,Instantiation.Effect.resources,Syntax.without]
private def plain : PlainData := ⟨.bind 5 outerCode,.none,.unit,.unit,[],rfl⟩
def bootstrap : ReadyBind initialInput := {
  binder := ⟨5,.function .unit .unit [.user 1 []]⟩,parameter := ⟨8,.unit⟩
  initializer := 3,body := 9,fnBody := 2,fuel := 10,fnFuel := 3
  bindNode := graph.nodes[10]'(by decide),functionNode := graph.nodes[3]'(by decide)
  rawInitializer := callback,rawBody := outerCode,rawFunction := .perform (.user 1 []) 0 .unit
  initializerCode := callback,suffix := outerCode
  known := rfl,kind := rfl,fnKnown := rfl,fnKind := rfl,it := rfl,bt := rfl,ft := rfl
  fnRaw := rfl,certificate := callable,codeSame := rfl,rawSame := rfl,bodySame := rfl
  closed := callback_closed,ready := by
    simp [ClosedExcept,outerCode,outerClauses,innerCode,innerClauses,Code.dependencies,Clauses.dependencies,effectAtoms,Instantiation.Effect.resources,Syntax.without]
  plain := plain,scope := rfl,context := rfl }
private def closure : CoreMachine.Value := .closure 8 2 .empty
private def environment : Environment := .binding 5 closure .empty
private theorem callback_value (owners : OwnerMap) : ValueRel graph owners [] closure callback := by
  refine .closure (fuel := 3) (bodyCode := .perform (.user 1 []) 0 .unit) rfl callable .empty callback_closed
noncomputable def s0 := ready_endpoint bootstrap
noncomputable def prefix0 : InitialChronology initialInput s0 3 [] [] := .readyBind bootstrap
private def outerData : HandlerData := ⟨0,.user 0 [],outerClauses.subst 5 callback,.none,.unit,by
  simp [outerClauses,innerCode,innerClauses,callback,Clauses.subst,Code.subst,Clauses.dependencies,Code.dependencies,Syntax.ticketDependencies,Syntax.without,effectAtoms,Instantiation.Effect.resources]⟩
private noncomputable def outerReady : HandlerReady s0 := {
  site := 9,environment := environment,data := outerData,node := graph.nodes[9]'(by decide)
  handler := 0,effect := .user 0 [],body := 8,clauses := [⟨0,.binder ⟨9,.unit⟩,0,7⟩]
  known := rfl,kind := rfl,code := .perform (.user 0 []) 0 .unit
  raw := .perform (.user 0 []) 0 .unit,rawClauses := outerClauses,fuel := 10
  translated := rfl,siteTranslated := rfl
  lexical := by
    change EnvCloses graph [] [] environment outerCode (outerCode.subst 5 callback)
    exact (ready_binding_produced bootstrap).2.1
  activation := rfl,control := rfl,empty := ⟨rfl,rfl⟩ }
noncomputable def outer := handler_from_initial prefix0 outerReady
noncomputable def s1 := (handler_result outer).after
noncomputable def prefix1 := InitialChronology.next prefix0 (Operation.handler outer)
private theorem ordered : Postorder graph := checkShape_postorder graph initialInput.shape
private noncomputable def outerRequest : EntryInput s1 := {
  ordered := ordered,site := 8,environment := environment,node := graph.nodes[8]'(by decide),known := rfl
  nextIndex := 0,frame := .request (.user 0 []) 0 environment,kind := .request rfl
  environmentSame := rfl,control := by
    change (handler_result (handler_from_initial prefix0 outerReady)).after.state.control = .evaluate outerReady.body outerReady.environment
    exact handler_current_control prefix0 outerReady,maps := rfl,stack := rfl
  interpreted := by
    have control : s1.state.control = .evaluate 8 environment := by
      change (handler_result (handler_from_initial prefix0 outerReady)).after.state.control = .evaluate outerReady.body outerReady.environment
      exact handler_current_control prefix0 outerReady
    rw [control]
    change ControlRel graph [] [] (.evaluate 8 environment) (.perform (.user 0 []) 0 .unit)
    exact .evaluate (fuel := 2) rfl (.binding (callback_value []) .empty) }

noncomputable def s2 := (entry_result outerRequest).after
private def requestPlain : PlainData := ⟨.perform (.user 0 []) 0,.none,.unit,.unit,[],rfl⟩
private noncomputable def outerOperand : LiteralInput s2 := {
  index := 0,environment := environment,code := .unit,scope := .none
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (by
    refine .binding (callback_value []) ?_
    exact .empty)
  control := rfl
  stack := by
    have frame : CoreRequestFrames.RequestRel graph [] [] (.request (.user 0 []) 0 environment) requestPlain :=
      .operand (requested := .user 0 []) (.binding (callback_value []) .empty) rfl
    exact prepend_request frame (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed (pushed_mapped .nil) .none }
noncomputable def s3 := (literal_result outerOperand).after
private theorem s3_returned : s3.state.control = .returned .unit := by
  have actual : CoreMachine.next graph s2.state = .stepped {s2.state with
    control := .returned .unit
    observations := s2.state.observations ++ [.entered 0]} := rfl
  exact congrArg CoreMachine.State.control (CoreMachine.Outcome.stepped.inj ((literal_result outerOperand).core.symm.trans actual))
private noncomputable def captureOuter : CaptureInput s3 := {
  index := ⟨0,by decide⟩,requested := .user 0 [],effect := .user 0 [],operation := 0
  selectedClause := ⟨0,.binder ⟨9,.unit⟩,0,7⟩,value := .unit,code := .unit
  environment := environment,plain := requestPlain,context := [],outward := [.user 0 []],result := .unit
  same := rfl,prefixScope := .nil,route := .outside (by simp)
  lookup := rfl,selected := by
    change outer.installation.clauses.find? _ = _
    rw [show outer.installation.clauses = outerReady.clauses from (handler_literal_fields prefix0 outerReady).2.2.2]
    rfl
  operand := .unit,requestCarrier := .binding (callback_value []) .empty,plainContext := rfl
  ready := by
    intro parameter binder body atClause
    cases atClause with
    | hit => simp [ClosedExcept,innerCode,innerClauses,callback,Code.subst,Clauses.subst,Code.dependencies,Clauses.dependencies,effectAtoms,Instantiation.Effect.resources,Syntax.without]
    | pass different rest => exact False.elim (different rfl)
  control := s3_returned,maps := rfl,focus := rfl }
noncomputable def s4 := (capture_result captureOuter).after
noncomputable def prefix4 := InitialChronology.next
  (InitialChronology.next (InitialChronology.next prefix1 (Operation.entry outerRequest)) (Operation.literal outerOperand))
  (Operation.capture captureOuter)
private noncomputable def outerCapture := capture_data captureOuter
private theorem outer_argument : outerCapture.argument.id = 9 := by
  exact congrArg CoreSyntax.Binder.id (CoreSyntax.Pattern.binder.inj outerCapture.pattern).symm
private theorem outer_body : outerCapture.body = innerCode.subst 5 callback := by
  have atClause := outerCapture.clauseAt
  change ClauseAt 0 (outerClauses.subst 5 callback) _ _ _ at atClause
  have only : ∀ parameter binder body, ClauseAt 0 (outerClauses.subst 5 callback) parameter binder body → body = innerCode.subst 5 callback := by
    intro parameter binder body selected
    cases selected with
    | hit => rfl
    | pass different rest => exact False.elim (different rfl)
  exact only _ _ _ atClause
private theorem s4_control : s4.state.control = .evaluate 7 (.binding 9 .unit environment) := by
  change CoreMachine.Control.evaluate 7 (.binding outerCapture.argument.id .unit environment) = _
  rw [outer_argument]
private theorem s4_focus : s4.focus = ⟨innerCode.subst 5 callback,.ticket (ticket graph 0) 0,.nil⟩ := by
  change (⟨outerCapture.body.subst outerCapture.argument.id .unit,.ticket (ticket graph 0) 0,.nil⟩ : Configuration) = _
  rw [outer_body,outer_argument]
  rfl
private def innerData : HandlerData := ⟨1,.user 1 [],innerClauses,.ticket (ticket graph 0) 0,.unit,by
  simp [innerClauses,Clauses.dependencies,Code.dependencies,Syntax.ticketDependencies,Syntax.without]⟩
private def innerEnvironment : Environment := .binding 9 .unit environment
private noncomputable def innerReady : HandlerReady s4 := {
  site := 7,environment := innerEnvironment,data := innerData,node := graph.nodes[7]'(by decide)
  handler := 1,effect := .user 1 [],body := 6,clauses := [⟨0,.binder ⟨10,.unit⟩,1,1⟩]
  known := rfl,kind := rfl,code := .cleanup callback .unit,raw := .cleanup (.variable 5) .unit
  rawClauses := innerClauses,fuel := 7,translated := rfl,siteTranslated := rfl
  lexical := by
    refine .binding (ValueRel.unit (graph := graph) (owners := s4.owners) (heap := [])) ?_
    refine .binding (callback_value s4.owners) ?_
    exact .empty
  activation := rfl,control := s4_control,empty := ⟨rfl,s4_focus⟩ }
noncomputable def inner := handler_from_initial prefix4 innerReady
noncomputable def s5 := (handler_result inner).after
noncomputable def prefix5 := InitialChronology.next prefix4 (Operation.handler inner)
private def action : ActionData := ⟨0,callback,callback_closed,.ticket (ticket graph 0) 0,.unit,[]⟩
private noncomputable def readyCleanup : CleanupReady s5 := {
  site := 6,callback := ⟨5,.function .unit .unit [.user 1 []]⟩,action := 5,body := 0
  environment := innerEnvironment,data := action,node := graph.nodes[6]'(by decide)
  known := rfl,kind := rfl,shape := rfl,rawBody := .unit,bodyCode := .unit,translated := rfl
  closing := by
    refine .binding (ValueRel.unit (graph := graph) (owners := s5.owners) (heap := [])) ?_
    refine .binding (callback_value s5.owners) ?_
    exact .empty
  parameter := 8,lambdaBody := .perform (.user 1 []) 0 .unit,callable := rfl,identity := rfl
  control := by
    change (handler_result (handler_from_initial prefix4 innerReady)).after.state.control = .evaluate innerReady.body innerReady.environment
    exact handler_current_control prefix4 innerReady
  empty := ⟨rfl,rfl⟩ }
noncomputable def acquisition := cleanup_from_initial prefix5 readyCleanup
noncomputable def registered := (cleanup_result acquisition).after
private noncomputable def bodyUnit : LiteralInput registered := {
  index := 0,environment := innerEnvironment,code := .unit,scope := action.scope
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl
    (.binding ValueRel.unit (.binding (callback_value registered.owners) .empty))
  control := rfl
  stack := by
    change OrdinaryWithMaps graph [] [] .unit action.scope .unit action.scope .nil
    exact ⟨[],[],rfl,.nil,PushedWithMaps.nil⟩ }
noncomputable def bodyEnd := (literal_result bodyUnit).after
noncomputable def body_prefix : OperationSegment registered bodyEnd 1 [] [] :=
  .next .initial (Operation.literal bodyUnit)
private theorem body_returned : bodyEnd.state.control = .returned .unit := by
  have concrete : CoreMachine.next graph registered.state = .stepped {registered.state with
    control := .returned .unit
    observations := registered.state.observations ++ [.entered 0]} := rfl
  exact congrArg CoreMachine.State.control (CoreMachine.Outcome.stepped.inj ((literal_result bodyUnit).core.symm.trans concrete))
private theorem body_frames : bodyEnd.state.frames = .cleanupBoundary 5 innerEnvironment 0 :: s5.physical := by
  have concrete : CoreMachine.next graph registered.state = .stepped {registered.state with
    control := .returned .unit
    observations := registered.state.observations ++ [.entered 0]} := rfl
  exact congrArg CoreMachine.State.frames (CoreMachine.Outcome.stepped.inj ((literal_result bodyUnit).core.symm.trans concrete))
private noncomputable def bodyRun := (InitialChronology.next prefix5 (Operation.cleanup acquisition)).extend body_prefix
private theorem bodyBound : TicketBound bodyEnd.state (.push (.armed action) s5.lexical) := by
  change TicketBound bodyEnd.state bodyEnd.lexical
  exact bodyRun.lexical_ticket_bound
private theorem installed : CoreCallableCleanupOrigins.SavedCleanupOrigin graph s5.owners [] 5 innerEnvironment action s5.physical :=
  (cleanup_data acquisition).past.installed
private theorem normalStep : CoreGeneralCaptureResume.GeneralStepWitness graph
    ⟨returnedState bodyEnd.state .unit (.cleanupBoundary 5 innerEnvironment action.identity :: s5.physical),
      .eval ⟨.unit,action.scope,.push (.armed action) s5.lexical⟩,bodyEnd.owners,[]⟩
    ⟨startedState bodyEnd.state 5 innerEnvironment action.identity .unit s5.physical,
      .eval ⟨.app action.action .unit,.none,.push (.running action .unit (ValueRel.unit (graph := graph) (owners := bodyEnd.owners) (heap := [])).closed) s5.lexical⟩,s5.owners,[]⟩ [] [] := (normal_start_history (base := bodyEnd.state) installed
  (ValueRel.unit (graph := graph) (owners := bodyEnd.owners) (heap := [])) s5.history bodyBound action.scope).1
noncomputable def start : RunningStartPast graph s5.owners 5 innerEnvironment action .unit .unit s5.physical s5.lexical := {
  predecessor := bodyEnd.state,callerOwners := bodyEnd.owners,scope := action.scope
  installed := installed,saved := .unit,originalHistory := s5.history
  running := ⟨installed,.unit⟩,sameInstalled := rfl,actual := normalStep }
private theorem start_next : CoreMachine.next graph bodyEnd.state = .stepped (started start).state := by
  have same : returnedState bodyEnd.state .unit (.cleanupBoundary 5 innerEnvironment 0 :: s5.physical) = bodyEnd.state := by
    simp only [returnedState]
    rw [← body_returned,← body_frames]
  have core := normalStep.core
  change CoreMachine.next graph (returnedState bodyEnd.state .unit (.cleanupBoundary 5 innerEnvironment 0 :: s5.physical)) = .stepped (started start).state at core
  rw [same] at core
  exact core
private theorem retained_heap_refl {graph : Graph} {heap : CoreMachine.Heap} {physical : List CoreMachine.Frame} {target : Stack}
    (history : RetainedHistory graph heap physical target) (extension : HeapExtends heap heap) :
    history.heap_weaken extension = history := by
  induction history <;> simp_all [RetainedHistory.heap_weaken]
private theorem history_heap_refl {graph : Graph} {heap : CoreMachine.Heap} {physical : List CoreMachine.Frame} {target : Stack}
    (history : GeneralHistory graph heap physical target) (extension : HeapExtends heap heap) :
    history.heap_weaken extension = history := by
  induction history <;> simp_all [GeneralHistory.heap_weaken,retained_heap_refl]
theorem causal_active_start : CausalStart prefix5 acquisition body_prefix start := by
  have edge : CoreUnwindRelation.Trace bodyEnd.point.machine (started start).point.machine [] [] := by
    change CoreUnwindRelation.Trace (.eval ⟨.unit,action.scope,.push (.armed action) s5.lexical⟩)
      (.eval ⟨.app action.action .unit,.none,.push (.running action .unit start.saved.closed) s5.lexical⟩) [] []
    exact normalStep.target.trace
  refine ⟨⟨body_prefix.actual_steps,body_returned,body_frames,fun _ _ h => h,HEq.rfl,?_⟩,
    start_next,bodyRun.actual_steps.snoc start_next,?_,?_⟩
  · rw [(cleanup_data acquisition).historySame]
    exact heq_of_eq (history_heap_refl s5.history _).symm
  · exact bodyRun.target_trace.append edge
  · intro ticket
    have bounded := bodyRun.lexical_ticket_bound ticket
    have lexical : bodyEnd.lexical = .push (.armed action) s5.lexical := rfl
    rw [lexical] at bounded
    change List.count ticket s5.lexical.erase.ticketNames ≤ List.count ticket (CoreTicketHistory.capturedTickets bodyEnd.state.observations)
    simp only [Stack.erase,ExecFrame.erase,Control.ticketNames,List.count_append] at bounded
    omega

theorem actual_active_registration :
    CoreAllocationHistory.Steps graph 9 (CoreMachine.initial graph) registered.state ∧
    action.scope = .ticket (ticket graph 0) 0 ∧
    s5.physical = .handlerBoundary 7 innerEnvironment 1 :: s4.physical :=
  ⟨(InitialChronology.next prefix5 (Operation.cleanup acquisition)).actual_steps,rfl,rfl⟩

private noncomputable def t0 : Endpoint graph := started start
private theorem saved_callback : EnvCloses graph s5.owners [] innerEnvironment
    (.app (.variable 5) .unit) (.app callback .unit) := by
  refine .binding ValueRel.unit ?_
  refine .binding (callback_value s5.owners) ?_
  exact .empty
private noncomputable def enter : EntryInput t0 := {
  ordered := ordered,site := 5,environment := innerEnvironment,node := graph.nodes[5]'(by decide),known := rfl
  nextIndex := 4,frame := .applyFunction 0 innerEnvironment,kind := .application rfl,environmentSame := rfl
  control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl saved_callback }

private noncomputable def t1 := (entry_result enter).after
private noncomputable def literalFunction : LiteralInput t1 := {
  index := 4,environment := innerEnvironment,code := callback,scope := .none
  literal := .lexicalVariable (node := graph.nodes[4]'(by decide)) rfl rfl (by
    refine .binding ValueRel.unit ?_
    refine .binding (callback_value s5.owners) ?_
    exact .empty) (callback_value s5.owners).closed
  control := rfl
  stack := by
    let plain : PlainData := ⟨.appFunction .unit,.none,.unit,.unit,[],rfl⟩
    have frame : PlainFrameRel graph s5.owners [] (.applyFunction 0 innerEnvironment) plain := by
      refine .applyFunction (fuel := 1) rfl ?_
      refine .binding ValueRel.unit ?_
      refine .binding (callback_value s5.owners) ?_
      simpa [Code.subst] using (EnvCloses.empty (graph := graph) (owners := s5.owners) (heap := []) (code := .unit))
    exact prepend_mapped frame (callback_value s5.owners).closed (pushed_mapped PushedWithMaps.nil) .none }

private noncomputable def t2 := (literal_result literalFunction).after


private theorem t2_exact : t2.state = { t1.state with
    control := .returned closure
    observations := t1.state.observations ++ [.entered 4] } := by
  have concrete : CoreMachine.next graph t1.state = .stepped { t1.state with
      control := .returned closure
      observations := t1.state.observations ++ [.entered 4] } := rfl
  exact CoreMachine.Outcome.stepped.inj ((literal_result literalFunction).core.symm.trans concrete)

private noncomputable def changeArgument : SwapInput t2 := {
  frameOwners := s5.owners,beforeFrame := .applyFunction 0 innerEnvironment,afterFrame := .applyArgument closure
  kind := .application,value := closure,nextIndex := 0,environment := innerEnvironment
  frameBefore := Or.inl rfl,frameAfter := Or.inl rfl,code := callback,related := (callback_value s5.owners)
  interpreted := ⟨rfl,callback,.none,(by
    change ControlRel graph s5.owners [] t2.state.control callback
    rw [t2_exact]
    exact .returned (callback_value s5.owners)),literalFunction.stack⟩
  control := by rw [t2_exact]
  maps := rfl }

private noncomputable def t3 := (swap_result changeArgument).after

private noncomputable def literalArgument : LiteralInput t3 := {
  index := 0,environment := innerEnvironment,code := .unit,scope := .none
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (by
    refine .binding ValueRel.unit ?_
    refine .binding (callback_value s5.owners) ?_
    exact .empty)
  control := rfl
  stack := by
    let plain : PlainData := ⟨.appArgument callback,.none,.unit,.unit,[],rfl⟩
    have frame : PlainFrameRel graph s5.owners [] (.applyArgument closure) plain := .applyArgument (callback_value s5.owners)
    exact prepend_mapped frame (ValueRel.unit (graph := graph) (owners := s5.owners) (heap := [])).closed
      (pushed_mapped PushedWithMaps.nil) .none }

private noncomputable def t4 := (literal_result literalArgument).after

private theorem t4_exact : t4.state = { t3.state with
    control := .returned .unit
    observations := t3.state.observations ++ [.entered 0] } := by
  have concrete : CoreMachine.next graph t3.state = .stepped { t3.state with
      control := .returned .unit
      observations := t3.state.observations ++ [.entered 0] } := rfl
  exact CoreMachine.Outcome.stepped.inj ((literal_result literalArgument).core.symm.trans concrete)

private noncomputable def apply : BetaInput t4 := {
  frameOwners := s5.owners,parameter := 8,body := 2,environment := .empty,value := .unit
  argument := .unit,bodyCode := .perform (.user 1 []) 0 .unit,scope := .none,function := (callback_value s5.owners),operand := .unit
  control := by rw [t4_exact]
  maps := rfl,focus := rfl }

private noncomputable def t5 := (beta_result apply).after


private def calleeEnvironment : Environment := .binding 8 .unit .empty
private noncomputable def innerRequest : EntryInput t5 := {
  ordered := ordered,site := 2,environment := calleeEnvironment,node := graph.nodes[2]'(by decide),known := rfl
  nextIndex := 0,frame := .request (.user 1 []) 0 calleeEnvironment,kind := .request rfl
  environmentSame := rfl,control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl (.binding ValueRel.unit .empty) }
private noncomputable def t6 := (entry_result innerRequest).after
private def innerRequestPlain : PlainData := ⟨.perform (.user 1 []) 0,.none,.unit,.unit,[],rfl⟩
private noncomputable def innerOperand : LiteralInput t6 := {
  index := 0,environment := calleeEnvironment,code := .unit,scope := .none
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (.binding ValueRel.unit .empty)
  control := rfl
  stack := by
    have frame : CoreRequestFrames.RequestRel graph [] [] (.request (.user 1 []) 0 calleeEnvironment) innerRequestPlain :=
      .operand (requested := .user 1 []) (.binding ValueRel.unit .empty) rfl
    exact prepend_request frame (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed (pushed_mapped .nil) .none }
private noncomputable def t7 := (literal_result innerOperand).after
private theorem t7_returned : t7.state.control = .returned .unit := by
  have actual : CoreMachine.next graph t6.state = .stepped {t6.state with
    control := .returned .unit
    observations := t6.state.observations ++ [.entered 0]} := rfl
  exact congrArg CoreMachine.State.control (CoreMachine.Outcome.stepped.inj ((literal_result innerOperand).core.symm.trans actual))
private noncomputable def captureInner : CaptureInput t7 := {
  index := ⟨0,by decide⟩,requested := .user 1 [],effect := .user 1 [],operation := 0
  selectedClause := ⟨0,.binder ⟨10,.unit⟩,1,1⟩,value := .unit,code := .unit
  environment := calleeEnvironment,plain := innerRequestPlain,context := [],outward := [.user 1 []],result := .unit
  same := rfl,prefixScope := .skip (by rfl) .nil,route := .outside (by simp)
  lookup := rfl,selected := by
    change inner.installation.clauses.find? _ = _
    rw [show inner.installation.clauses = innerReady.clauses from (handler_literal_fields prefix4 innerReady).2.2.2]
    rfl
  operand := .unit,requestCarrier := .binding ValueRel.unit .empty,plainContext := rfl
  ready := by
    intro parameter binder body atClause
    change ClauseAt 0 innerClauses parameter binder body at atClause
    cases atClause with
    | hit => simp [ClosedExcept,Code.dependencies]
    | pass different rest => exact False.elim (different rfl)
  control := t7_returned,maps := rfl,focus := rfl }
private noncomputable def t8 := (capture_result captureInner).after
private noncomputable def innerCapture := capture_data captureInner
private theorem inner_argument : innerCapture.argument.id = 10 := by
  exact congrArg CoreSyntax.Binder.id (CoreSyntax.Pattern.binder.inj innerCapture.pattern).symm
private theorem inner_body : innerCapture.body = .resume (ticket graph 1) .unit := by
  have only : ∀ parameter binder body, ClauseAt 0 innerClauses parameter binder body → body = .resume (ticket graph 1) .unit := by
    intro parameter binder body selected
    cases selected with
    | hit => rfl
    | pass different rest => exact False.elim (different rfl)
  exact only _ _ _ innerCapture.clauseAt
private theorem t8_control : t8.state.control = .evaluate 1 (.binding 10 .unit innerEnvironment) := by
  change CoreMachine.Control.evaluate 1 (.binding innerCapture.argument.id .unit innerEnvironment) = _
  rw [inner_argument]
private theorem t8_focus : t8.focus = ⟨.resume (ticket graph 1) .unit,.ticket (ticket graph 1) 1,.nil⟩ := by
  change (⟨innerCapture.body.subst innerCapture.argument.id .unit,.ticket (ticket graph 1) 1,.nil⟩ : Configuration) = _
  rw [inner_body,inner_argument]
  rfl
private noncomputable def enterInnerResume : EntryInput t8 := {
  ordered := ordered,site := 1,environment := .binding 10 .unit innerEnvironment,node := graph.nodes[1]'(by decide),known := rfl
  nextIndex := 0,frame := .resume 1 1,kind := .resume rfl,environmentSame := trivial
  control := t8_control,maps := rfl,stack := rfl
  interpreted := by
    rw [t8_control,t8_focus]
    have handler : inner.installation.handler = 1 := (handler_literal_fields prefix4 innerReady).1
    change ControlRel graph (⟨inner.installation.handler,1,ticket graph 1⟩ :: s5.owners) []
      (.evaluate 1 (.binding 10 .unit innerEnvironment)) (.resume (ticket graph 1) .unit)
    rw [handler]
    exact .evaluate (fuel := 2) rfl (.binding ValueRel.unit (.binding ValueRel.unit (.binding (callback_value _) .empty))) }
private noncomputable def t9 := (entry_result enterInnerResume).after
private def innerResumePlain : PlainData := ⟨.resume (ticket graph 1),.ticket (ticket graph 1) 1,.unit,.unit,[1],rfl⟩
private theorem innerResumeFrame : CoreResumeFrames.ResumeRel graph t8.owners [] (.resume 1 1) innerResumePlain := by
  have handler : inner.installation.handler = 1 := (handler_literal_fields prefix4 innerReady).1
  change CoreResumeFrames.ResumeRel graph (⟨inner.installation.handler,1,ticket graph 1⟩ :: s5.owners) [] (.resume 1 1) innerResumePlain
  rw [handler]
  exact .operand (environment := .binding 10 .unit innerEnvironment) (site := 1) (node := graph.nodes[1]'(by decide)) (fuel := 2)
    rfl rfl rfl rfl (.binding ValueRel.unit (.binding ValueRel.unit (.binding (callback_value _) .empty))) rfl
private noncomputable def innerResumeOperand : LiteralInput t9 := {
  index := 0,environment := .binding 10 .unit innerEnvironment,code := .unit,scope := innerResumePlain.scope
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl
    (.binding ValueRel.unit (.binding ValueRel.unit (.binding (callback_value t8.owners) .empty)))
  control := rfl
  stack := by
    change OrdinaryWithMaps graph [] [(t8.owners,.resume 1 1)] .unit innerResumePlain.scope
      t8.focus.expression t8.focus.scope t8.focus.stack
    rw [t8_focus]
    exact prepend_resume innerResumeFrame (ValueRel.unit (graph := graph) (owners := t8.owners) (heap := [])).closed (pushed_mapped .nil) innerResumePlain.scope }
private noncomputable def t10 := (literal_result innerResumeOperand).after
private theorem t10_returned : t10.state.control = .returned .unit := by
  have actual : CoreMachine.next graph t9.state = .stepped {t9.state with
    control := .returned .unit
    observations := t9.state.observations ++ [.entered 0]} := rfl
  exact congrArg CoreMachine.State.control (CoreMachine.Outcome.stepped.inj ((literal_result innerResumeOperand).core.symm.trans actual))
private noncomputable def selectedInner := location t7 captureInner.index
private noncomputable def savedInner := selectedInner.before.append (.handler selectedInner.installation selectedInner.header .nil)
private noncomputable def resumeInner : ResumeInput t10 := {
  handler := inner.installation.handler,owner := 1,occurrence := 1,dynamicTicket := 1,savedOwners := s5.owners
  frameOwners := t8.owners,data := innerData,result := .unit
  captured := [.cleanupCompletion 0 .unit,.handlerBoundary 7 innerEnvironment 1]
  capturedTarget := selectedInner.front.append (.push (.handler selectedInner.data) .nil)
  installation := innerCapture.installation,header := innerCapture.header,capturedHistory := savedInner
  outside := selectedInner.outside,tail := selectedInner.tail,outsideHistory := selectedInner.after
  front := [],frontTarget := .nil,frontHistory := .nil,pass := .nil
  physical := rfl,lexical := rfl,split := .here
  plain := innerResumePlain,binder := ticket graph 1,frame := by
    rw [show inner.installation.handler = 1 from (handler_literal_fields prefix4 innerReady).1]
    exact innerResumeFrame
  context := rfl,value := .unit,code := .unit,operand := .unit,resolve := rfl
  control := t10_returned,maps := by
    rw [show inner.installation.handler = 1 from (handler_literal_fields prefix4 innerReady).1]
    rfl
  focus := t8_focus }
private noncomputable def t11 := (resume_result resumeInner).after
noncomputable def callback_segment : StableSegment (started start) t7 7 := by
  exact .next (.next (.next (.next (.next (.next (.next .initial (.entry enter)) (.literal literalFunction))
    (.swap changeArgument)) (.literal literalArgument)) (.beta apply)) (.entry innerRequest)) (.literal innerOperand)
noncomputable def captured_trace : Generated start t8 8 [.ticket 1] [] :=
  .next callback_segment.generated (.capture captureInner)
noncomputable def resumed_trace : Generated start t11 11 [.ticket 1] [.ticket 1] :=
  .next (.next (.next captured_trace (.entry enterInnerResume)) (.literal innerResumeOperand)) (.resume resumeInner)
private noncomputable def restoredHead : CoreCallableGeneratedCleanupCompletion.RunningHead start t11.history :=
  .append _ _ (.append _ _ (.append _ _ (.running start.running)))
private theorem restored_tail : restoredHead.tail.physical =
    .handlerBoundary inner.site inner.environment inner.data.activation ::
      .clauseBoundary inner.installation.handler 1 1 1 none :: s4.physical := rfl
private noncomputable def finish : CoreCallableGeneratedCleanupCompletion.FinishInput resumed_trace :=
  finish_without_checked inner readyCleanup resumed_trace (checkHandlerSites_sound (graph := graph) rfl)
    innerCapture.installation innerCapture.header restoredHead restored_tail
    (.ticket (ticket graph 1) 1) rfl ⟨rfl,rfl⟩
noncomputable def completed : CoreCallableGeneratedCleanupCompletion.Completed start
    (CoreCallableGeneratedCleanupCompletion.finish_result finish).after 12 [.ticket 1] [.cleanup 0,.ticket 1] :=
  .finish resumed_trace finish

theorem actual_outside_tail : t11.state.frames =
    [.cleanupCompletion 0 .unit,.handlerBoundary 7 innerEnvironment 1,
      .clauseBoundary inner.installation.handler 1 1 1 none,
      .clauseBoundary outer.installation.handler 0 0 0 (some [.handlerBoundary 9 environment 0])] := rfl

theorem same_original_selected_installation :
    HEq innerCapture.installation.installation inner.installation := innerCapture.sameInstallation

theorem connected_initial_finish :
    CoreAllocationHistory.Steps graph 23 (CoreMachine.initial graph)
      (CoreCallableGeneratedCleanupCompletion.finish_result finish).after.state ∧
    (CoreCallableGeneratedCleanupCompletion.finish_result finish).after.state.control = .returned .unit ∧
    (CoreCallableGeneratedCleanupCompletion.finish_result finish).after.focus.scope = action.scope ∧
    (CoreCallableGeneratedCleanupCompletion.finish_result finish).after.physical = restoredHead.tail.physical := by
  have beforeFinish := causal_active_start.generated_from_initial resumed_trace
  exact ⟨beforeFinish.1.snoc (CoreCallableGeneratedCleanupCompletion.finish_result finish).core,rfl,rfl,rfl⟩

theorem connected_initial_target_trace :
    CoreUnwindRelation.Trace (initial_endpoint initialInput).point.machine
      (CoreCallableGeneratedCleanupCompletion.finish_result finish).after.point.machine
      [.ticket 0,.cleanup 0,.ticket 1] [.cleanup 0,.ticket 1] := by
  have beforeFinish := causal_active_start.generated_from_initial resumed_trace
  exact beforeFinish.2.1.append (CoreCallableGeneratedCleanupCompletion.finish_result finish).matching.target_trace

/-- Conditional physical-barrier counterevidence, reused from the existing
first-pair theorem; it is not another initially admitted program. -/
theorem same_pair_spent_blocks_old_ticket {handler owner oldOccurrence oldTicket newOccurrence newTicket : Nat}
    {oldSaved : Option (List CoreMachine.Frame)} {physical front outside : List CoreMachine.Frame}
    (different : oldTicket ≠ newTicket) :
    ¬ CoreCallableReachableResume.OwnerPath handler owner oldOccurrence oldTicket oldSaved
      (.clauseBoundary handler owner newOccurrence newTicket none :: physical) front outside :=
  CoreCallableCleanupReachableTransport.outside_static_shadow_obstruction different

theorem produced_original_split_and_check :
    s5.physical = [.handlerBoundary 7 innerEnvironment 1] ++ s4.physical ∧
    CoreCallableOutsideOrigin.outsideCheck inner.owners readyCleanup.data.scope
      (GeneralHistory.spent innerCapture.installation innerCapture.header .nil) = true :=
  ⟨rfl,outside_checked_spent inner readyCleanup (checkHandlerSites_sound (graph := graph) rfl)
    innerCapture.installation innerCapture.header⟩

#print axioms completed
#print axioms produced_original_split_and_check
#print axioms same_pair_spent_blocks_old_ticket
#print axioms callback_segment
#print axioms captured_trace
#print axioms resumed_trace
#print axioms actual_outside_tail
#print axioms same_original_selected_installation
#print axioms connected_initial_finish
#print axioms connected_initial_target_trace
#print axioms initialInput
#print axioms prefix4
#print axioms causal_active_start
#print axioms actual_active_registration
end Ash.OneShot.GeneratedOutsideActivationProbes
