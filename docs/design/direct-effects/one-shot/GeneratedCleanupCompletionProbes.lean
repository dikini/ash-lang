import CoreCallableGeneratedCleanupCompletion
namespace Ash.OneShot.CoreCallableGeneratedCleanupCompletion.Probes
open CoreCallableGeneratedChronology
open CoreSyntax CoreTranslation CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableGeneralHistory CoreCallableCallerBarriers CoreCallableRunningOccurrence CoreCallableReachableResume
open CoreCallableRunningCapture CoreCallableSiteLineage CoreCaptureEntry CoreRequestFrames CoreCallableCleanupOrigins
open CoreCallableCleanupReachableTransport CoreCleanupFrames

private def graph : Graph := CoreTranslation.Examples.authenticatedCleanup
private def callback : Code := .lambda 8 .unit
private def closure : CoreMachine.Value := .closure 8 0 .empty
private def environment : Environment := .binding 5 closure .empty
private def base : CoreMachine.State := {control := .returned .unit}

private theorem callable : CallableCertificate graph 8 0 .unit := by
  refine ⟨⟨1,⟨8,.unit⟩,_,rfl,rfl,rfl⟩,⟨1,rfl⟩,?_⟩
  intro ticket
  simp [Code.dependencies,Syntax.without]

private theorem callback_value : ValueRel graph [] [] closure callback := by
  refine .closure (fuel := 1) (bodyCode := .unit) rfl callable .empty ?_
  simp [callback,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Syntax.without]

private def action : ActionData := ⟨0,callback,callback_value.closed,.none,.unit,[]⟩

private theorem saved_callback : EnvCloses graph [] [] environment
    (.app (.variable 5) .unit) (.app callback .unit) := by
  refine .binding callback_value ?_
  simpa [Code.subst] using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .app callback .unit))

private theorem receipt : SavedCleanupOrigin graph [] [] 3 environment action [] := by
  refine ⟨?_,.inactive (CanonicalOwnerMap.empty graph)⟩
  exact .armed (site := 4) (node := graph.nodes[4]'(by decide)) rfl rfl rfl rfl saved_callback rfl callback_value

private noncomputable def start : RunningStartPast graph [] 3 environment action .unit .unit [] .nil := {
  predecessor := base,callerOwners := [],scope := .none
  installed := receipt,saved := .unit,originalHistory := .nil
  running := ⟨receipt,.unit⟩,sameInstalled := rfl
  actual := CoreGeneralRestoration.normal_start receipt.delayed (ValueRel.unit (owners := [])) (GeneralHistory.nil (graph := graph) (heap := [])).related .none }

private noncomputable def s0 : Endpoint graph := started start

private theorem ordered : CoreTranslationFuel.Postorder graph :=
  CoreTranslationFuel.checkShape_postorder graph (by rfl)

private noncomputable def enter : EntryInput s0 := {
  ordered := ordered,site := 3,environment := environment,node := graph.nodes[3]'(by decide),known := rfl
  nextIndex := 2,frame := .applyFunction 0 environment,kind := .application rfl,environmentSame := rfl
  control := rfl,maps := rfl,stack := rfl
  interpreted := .evaluate (fuel := 2) rfl saved_callback }

private noncomputable def s1 := (entry_result enter).after
private noncomputable def literalFunction : LiteralInput s1 := {
  index := 2,environment := environment,code := callback,scope := .none
  literal := .lexicalVariable (node := graph.nodes[2]'(by decide)) rfl rfl (by
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
    observations := s1.state.observations ++ [.entered 2] } := by
  have concrete : CoreMachine.next graph s1.state = .stepped { s1.state with
      control := .returned closure
      observations := s1.state.observations ++ [.entered 2] } := rfl
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
  frameOwners := [],parameter := 8,body := 0,environment := .empty,value := .unit
  argument := .unit,bodyCode := .unit,scope := .none,function := callback_value,operand := .unit
  control := by rw [s4_exact]
  maps := rfl,focus := rfl }

private noncomputable def s5 := (beta_result apply).after

private noncomputable def literalBody : LiteralInput s5 := {
  index := 0,environment := .binding 8 .unit .empty,code := .unit,scope := .none
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (by
    exact .binding ValueRel.unit .empty)
  control := rfl
  stack := pushed_mapped PushedWithMaps.nil }

private noncomputable def s6 := (literal_result literalBody).after

/-- A concrete authenticated delayed invocation traverses application/function,
argument/value and beta/body steps without resetting any intermediate state. -/
noncomputable def callback_trace : Generated start s6 6 [] [] := by
  have g0 : Generated start s0 0 [] [] := .initial
  have g1 := Generated.next g0 (Operation.entry enter)
  have g2 := Generated.next g1 (Operation.literal literalFunction)
  have g3 := Generated.next g2 (Operation.swap changeArgument)
  have g4 := Generated.next g3 (Operation.literal literalArgument)
  have g5 := Generated.next g4 (Operation.beta apply)
  exact Generated.next g5 (Operation.literal literalBody)

theorem callback_actual_and_saved_receipt :
    CoreAllocationHistory.Steps graph 7 (start_before start).state s6.state ∧
    CoreUnwindRelation.Trace (start_before start).point.machine s6.point.machine [] [] ∧
    RunningReceipt graph [] s6.state.heap 3 environment action .unit .unit [] :=
  ⟨callback_trace.from_actual_start.1,callback_trace.from_actual_start.2,callback_trace.retained_running_receipt⟩

/-- A generated path rejects attempts to replace a successful edge with a
malformed Core transition, independently of any supplied target relation. -/
theorem rejected_no_operation {graph : Graph} {before after : Endpoint graph}
    (rejected : CoreMachine.next graph before.state = .rejected error) :
    ¬ Nonempty (Operation before after created discharged) := by
  rintro ⟨operation⟩
  exact CoreMachine.rejected_not_step graph before.state error rejected after.state operation.actual.1

/-- A mixed current front is traversable from the actual full history records.
The live and spent pair misses are CURRENT guards, not future scan promises. -/
theorem mixed_front_pass
    (frame : PushCarrier graph frameOwners heap core ordinaryTarget) (ordinary)
    (handlerPast : GeneralHandlerPast graph handlerOwners site handlerEnvironment handlerData)
    (handlerHeader : CoreEffectFrames.BoundaryRel graph handlerOwners heap
      (.handlerBoundary site handlerEnvironment handlerData.activation) (.handler handlerData))
    (livePast : GeneralClausePast graph liveOwners liveHandler liveOwner liveActivation liveTicket liveCaptured liveData)
    (liveHeader : OwnerHeader graph liveOwners heap liveHandler liveOwner liveActivation liveData)
    (saved : GeneralHistory graph heap liveCaptured savedTarget)
    (spentPast : GeneralClausePast graph spentOwners spentHandler spentOwner spentActivation spentTicket spentCaptured spentData)
    (spentHeader : OwnerHeader graph spentOwners heap spentHandler spentOwner spentActivation spentData)
    (liveMiss : handler ≠ liveHandler ∨ owner ≠ liveOwner)
    (spentMiss : handler ≠ spentHandler ∨ owner ≠ spentOwner) :
    PassFront handler owner
      (.push frame ordinary (.handler handlerPast handlerHeader
        (.live (result := result) livePast liveHeader saved
          (.spent spentPast spentHeader .nil)))) :=
  .push frame ordinary _ (.handler handlerPast handlerHeader _
    (.live livePast liveHeader saved _ liveMiss (.spent spentPast spentHeader _ spentMiss .nil)))

/-- The innermost matching spent owner blocks an older live owner even across
unrelated handler metadata. The lookup result is computed, not assumed. -/
theorem matching_spent_before_older_live (handler owner occurrence ticket olderOccurrence olderTicket : Nat)
    (captured : List CoreMachine.Frame) :
    CoreMachine.findOwner handler owner
      [.clauseBoundary handler owner occurrence ticket none,
       .clauseBoundary handler owner olderOccurrence olderTicket (some captured)] =
      .error (.consumedOwner handler owner) := by
  simp [CoreMachine.findOwner]

private theorem s6_exact : s6.state = { s5.state with
    control := .returned .unit
    observations := s5.state.observations ++ [.entered 0]} := by
  have actual : CoreMachine.next graph s5.state = .stepped { s5.state with
    control := .returned .unit
    observations := s5.state.observations ++ [.entered 0]} := rfl
  exact CoreMachine.Outcome.stepped.inj ((literal_result literalBody).core.symm.trans actual)

private noncomputable def finish : FinishInput callback_trace := {
  head := .append _ _ (.running start.running)
  activation := .unchanged
  scope := .none
  control := by rw [s6_exact]
  empty := ⟨rfl,rfl⟩ }

/-- The SAME six-edge callback now executes actual cleanup completion. -/
noncomputable def callback_completed : Completed start (finish_result finish).after 7 [] [.cleanup action.identity] :=
  .finish callback_trace finish

theorem callback_through_finish :
    CoreAllocationHistory.Steps graph 8 (start_before start).state (finish_result finish).after.state ∧
    CoreUnwindRelation.Trace (start_before start).point.machine (finish_result finish).after.point.machine [] [.cleanup action.identity] ∧
    (finish_result finish).after.state.control = .returned .unit ∧
    (finish_result finish).after.focus = ⟨.unit,.none,.nil⟩ ∧
    CurrentOwnership graph [] (finish_result finish).after.state .none .nil := by
  refine ⟨callback_completed.from_actual_start.1,callback_completed.from_actual_start.2,
    (finish_restores_saved finish).1,(finish_restores_saved finish).2.1,?_⟩
  apply finish_current_ownership finish
  intro ticket
  simp [s6,literal_result,s5,beta_result,apply,s4,literal_result,s3,swap_result,changeArgument,
    s2,literal_result,s1,entry_result,enter,s0,started,start,Stack.erase,ExecFrame.erase,Control.ticketNames]


#print axioms callback_completed
#print axioms callback_through_finish
#print axioms callback_trace
#print axioms callback_actual_and_saved_receipt
#print axioms rejected_no_operation
#print axioms mixed_front_pass
#print axioms matching_spent_before_older_live
end Ash.OneShot.CoreCallableGeneratedCleanupCompletion.Probes
