import CoreCallableGeneratedTicketBound
namespace Ash.OneShot.CoreCallableGeneralCleanupRegistration.Probes
open CoreCallableGeneratedChronology CoreCallableGeneratedTicketBound
open CoreCallableGeneralCleanupRegistration CoreCallableGeneralHistory CoreCallableFrameInstallations
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableCallerBarriers CoreCallableRunningOccurrence CoreCallableReachableResume
open CoreCallableSiteLineage CoreCaptureEntry CoreRequestFrames CoreCallableCleanupOrigins
open CoreCallableCleanupReachableTransport CoreCleanupFrames

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
private noncomputable def registerNested : CleanupInput s5 := {
  site := 4,callback := ⟨5,.function .unit .unit []⟩,action := 3,body := 0
  environment := .binding 9 .unit captured,data := nestedAction,node := graph.nodes[4]'(by decide)
  known := rfl,kind := rfl,shape := rfl,postorder := ordered,lineage := .inactive (.empty graph)
  rawBody := .unit,bodyCode := .unit,translated := rfl
  closing := by
    change EnvCloses graph [] [] (.binding 9 .unit captured) (.cleanup (.variable 5) .unit) (.cleanup innerCallback .unit)
    refine .binding (ValueRel.unit (owners := [])) (.binding inner_value ?_)
    simpa [Code.subst,nestedAction,innerCallback] using
      (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .cleanup innerCallback .unit))
  parameter := 8,lambdaBody := .unit,callable := rfl,identity := rfl
  ownership := by
    constructor
    · exact Generated.lexical_ticket_bound prefixGenerated (TicketBound.empty _)
    · exact .inactive (.empty graph)
  control := rfl,empty := ⟨rfl,rfl⟩ }
private noncomputable def nestedEndpoint := (cleanup_result registerNested).after

noncomputable def nestedGenerated : Generated start nestedEndpoint 6 [.cleanup 1] [] :=
  .next prefixGenerated (.cleanup registerNested)

theorem actual_original_counter : (started start).state.nextCleanup = 1 ∧ s5.state.nextCleanup = 1 ∧
    nestedEndpoint.state.nextCleanup = 2 := by exact ⟨rfl,rfl,rfl⟩

theorem registration_start_chain : CoreAllocationHistory.Steps graph 3 original (started start).state := by
  have one : CoreAllocationHistory.Steps graph 1 original (registeredState original 9 0 8 environment action []) :=
    .snoc (.refl _) registration.actual
  have two := CoreAllocationHistory.Steps.snoc one body_step
  exact .snoc two start.actual.core

/-- One SAME-start chain reaches actual nested registration above running0. -/
theorem nested_actual_and_matching :
    CoreAllocationHistory.Steps graph 7 (start_before start).state nestedEndpoint.state ∧
    CoreUnwindRelation.Trace (start_before start).point.machine nestedEndpoint.point.machine [.cleanup 1] [] ∧
    nestedEndpoint.state.frames = [.cleanupBoundary 3 (.binding 9 .unit captured) 1,.cleanupCompletion 0 .unit] :=
  ⟨nestedGenerated.from_actual_start.1,nestedGenerated.from_actual_start.2,rfl⟩

theorem nested_positive : CoreUnwindRelation.Positive s5.point.machine nestedEndpoint.point.machine [.cleanup 1] [] := by
  have matching := (cleanup_result registerNested).matching
  cases matching with
  | positive step => exact step

theorem nested_ticket_events : CoreTicketHistory.capturedTickets nestedEndpoint.state.observations =
    CoreTicketHistory.capturedTickets s5.state.observations := by
  simpa [issuedTickets,nestedEndpoint] using Operation.ticket_events (.cleanup registerNested)

theorem nested_ticket_bound : TicketBound nestedEndpoint.state nestedEndpoint.lexical :=
  Generated.lexical_ticket_bound nestedGenerated (TicketBound.empty _)

theorem original_running_retained :
    RunningReceipt graph [] nestedEndpoint.state.heap 8 environment action .unit .unit [] :=
  nestedGenerated.retained_running_receipt

/-- An actual cleanup completion cannot occur in mapped-frame history. -/
theorem mapped_cannot_completion
    (history : MappedHistory graph heap maps target) :
    ∀ owners saved rest, maps ≠ (owners,.cleanupCompletion identity saved) :: rest := by
  induction history with
  | nil => intro _ _ _ impossible; cases impossible
  | @push frameOwners core targetFrame maps target frame ordinary tail ih =>
    intro owners saved rest impossible
    have head := (List.cons.inj impossible).1
    have same : core = .cleanupCompletion identity saved := congrArg Prod.snd head
    cases same
    cases frame <;> rename_i related
    all_goals cases related
  | handler installation header tail ih => intro _ _ _ impossible; cases impossible
  | live installation header captured tail ihSaved ihTail => intro _ _ _ impossible; cases impossible
  | spent installation header tail ih => intro _ _ _ impossible; cases impossible

theorem wrong_registration_node
    (past : GeneralRegisteredCleanupPast graph [] original 8 ⟨10,.function .unit .unit []⟩ 8 0 environment action [] .nil .unit .unit) : False := by
  have actual : graph.node 8 = some (graph.nodes[8]'(by decide)) := rfl
  have same := Option.some.inj (actual.symm.trans past.known)
  have kind := past.kind
  rw [← same] at kind
  cases kind

theorem current_suffix_is_general_only :
    ¬ Nonempty (MappedHistory graph s5.state.heap [([], .cleanupCompletion 0 .unit)] s5.lexical) := by
  rintro ⟨mapped⟩
  exact mapped_cannot_completion mapped [] .unit [] rfl

theorem no_active_registration_lineage : ¬ SiteLineage graph [] (.ticket 17 0) 4 := by
  intro invalid
  cases invalid

#print axioms actual_original_counter
#print axioms registration_start_chain
#print axioms nested_actual_and_matching
#print axioms nested_positive
#print axioms nested_ticket_events
#print axioms nested_ticket_bound
#print axioms original_running_retained
#print axioms mapped_cannot_completion
#print axioms wrong_registration_node
#print axioms current_suffix_is_general_only
#print axioms no_active_registration_lineage
end Ash.OneShot.CoreCallableGeneralCleanupRegistration.Probes
