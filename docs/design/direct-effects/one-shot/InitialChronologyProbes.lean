import CoreCallableGeneralStartedFrom
namespace Ash.OneShot.CoreCallableInitialChronology.Probes
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneratedChronology CoreCallableReachableResume
open CoreCallableCleanupOrigins CoreCallableSiteLineage CoreCallableGeneralHistory CoreCallableRunningOccurrence
open CoreGeneralRestoration CoreCallableGeneratedCurrentScopeConsumers

def graph : Graph := CoreTranslation.Examples.authenticatedCleanup
def callback : Code := .lambda 8 .unit
def original : Code := .bind 5 callback (.cleanup (.variable 5) .unit)
theorem initialInput : InitialInput graph original := ⟨rfl,rfl⟩
private theorem callable : CallableCertificate graph 8 0 .unit := by
  refine ⟨⟨1,⟨8,.unit⟩,_,rfl,rfl,rfl⟩,⟨1,rfl⟩,?_⟩
  intro ticket; simp [Code.dependencies,Syntax.without]
private theorem callback_closed : ClosedValue callback := by
  simp [callback,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Syntax.without]
private def plain : PlainData := ⟨.bind 5 (.cleanup (.variable 5) .unit),.none,.unit,.unit,[],rfl⟩
def bootstrap : ReadyBind initialInput := {
  binder := ⟨5,.function .unit .unit []⟩,parameter := ⟨8,.unit⟩
  initializer := 1,body := 4,fnBody := 0,fuel := 2,fnFuel := 1
  bindNode := graph.nodes[5]'(by decide),functionNode := graph.nodes[1]'(by decide)
  rawInitializer := callback,rawBody := .cleanup (.variable 5) .unit,rawFunction := .unit
  initializerCode := callback,suffix := .cleanup (.variable 5) .unit
  known := rfl,kind := rfl,fnKnown := rfl,fnKind := rfl,it := rfl,bt := rfl,ft := rfl
  fnRaw := rfl,certificate := callable,codeSame := rfl,rawSame := rfl,bodySame := rfl
  closed := callback_closed,ready := by simp [ClosedExcept,Code.dependencies]
  plain := plain,scope := rfl,context := rfl }
noncomputable def registrationEndpoint := ready_endpoint bootstrap
noncomputable def initial_prefix : InitialChronology initialInput registrationEndpoint 3 [] [] := .readyBind bootstrap
private def closure : CoreMachine.Value := .closure 8 0 .empty
private theorem callback_value : ValueRel graph [] [] closure callback := by
  refine .closure (fuel := 1) (bodyCode := .unit) rfl callable .empty callback_closed
private def action : ActionData := ⟨0,callback,callback_closed,.none,.unit,[]⟩
private def environment : Environment := .binding 5 closure .empty
private def readyCleanup : CleanupReady registrationEndpoint := {
  site := 4,callback := ⟨5,.function .unit .unit []⟩,action := 3,body := 0
  environment := environment,data := action,node := graph.nodes[4]'(by decide)
  known := rfl,kind := rfl,shape := rfl,rawBody := .unit,bodyCode := .unit,translated := rfl
  closing := by
    refine .binding callback_value ?_
    change EnvCloses graph [] [] .empty ((Code.cleanup (.variable 5) .unit).subst 5 callback) (.cleanup callback .unit)
    simpa [Code.subst,action,callback] using (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .cleanup callback .unit))
  parameter := 8,lambdaBody := .unit,callable := rfl,identity := rfl,control := rfl
  empty := ⟨rfl,by simp [registrationEndpoint,ready_endpoint,bootstrap,callback,Code.subst,action]⟩ }
noncomputable def acquisition := cleanup_from_initial initial_prefix readyCleanup
noncomputable def registered := (cleanup_result acquisition).after
private noncomputable def bodyUnit : LiteralInput registered := {
  index := 0,environment := environment,code := .unit,scope := .none
  literal := .unit (node := graph.nodes[0]'(by decide)) rfl rfl (by
    refine .binding callback_value ?_
    change EnvCloses graph [] [] .empty .unit .unit
    exact .empty)
  control := rfl
  stack := by
    change OrdinaryWithMaps graph [] [] .unit .none .unit .none .nil
    exact ⟨[],[],rfl,.nil,PushedWithMaps.nil⟩ }
noncomputable def bodyEnd := (literal_result bodyUnit).after
noncomputable def body_prefix : OperationSegment registered bodyEnd 1 [] [] :=
  .next .initial (Operation.literal bodyUnit)
private theorem body_exact : bodyEnd.state = {
    control := .returned .unit
    frames := [.cleanupBoundary 3 environment 0]
    observations := [.entered 5,.entered 1,.entered 4,.cleanupArmed 0,.entered 0]
    nextCleanup := 1 } := by
  have concrete : CoreMachine.next graph registered.state = .stepped {
    control := .returned .unit,frames := [.cleanupBoundary 3 environment 0]
    observations := [.entered 5,.entered 1,.entered 4,.cleanupArmed 0,.entered 0],nextCleanup := 1 } := rfl
  exact CoreMachine.Outcome.stepped.inj ((literal_result bodyUnit).core.symm.trans concrete)

theorem actual_initial_literal : (initial_endpoint initialInput).state = CoreMachine.initial graph ∧
    (initial_endpoint initialInput).focus.expression = original := ⟨rfl,rfl⟩
theorem bootstrap_three_ranked_edges :
    CoreInitialPrefix.Chain graph (ready_before_point bootstrap)
      [ready_middle_point bootstrap,ready_value_point bootstrap,ready_after_point bootstrap] (ready_after_point bootstrap) ∧
    CoreAllocationHistory.Steps graph 3 (CoreMachine.initial graph) registrationEndpoint.state :=
  ⟨(ready_binding_produced bootstrap).1,ready_binding_steps bootstrap⟩
theorem original_initial_to_registration :
    CoreAllocationHistory.Steps graph 4 (CoreMachine.initial graph) registered.state ∧
    (cleanup_data acquisition).past.history = registrationEndpoint.history :=
  ⟨(InitialChronology.next initial_prefix (Operation.cleanup acquisition)).actual_steps,(cleanup_data acquisition).historySame⟩
theorem causal_registered_start :
    ∃ start : RunningStartPast graph [] 3 environment action .unit .unit [] .nil,
      CausalStart initial_prefix acquisition body_prefix start ∧
      Nonempty (Generated start (started start) 0 [] []) := by
  apply start_from_registration initial_prefix acquisition body_prefix
  · rw [body_exact]
  · rw [body_exact]; rfl
  · change ValueRel graph [] [] .unit .unit
    exact .unit
  · rfl
  · exact ⟨rfl,rfl⟩

theorem six_edges_from_actual_initial :
    ∃ start : RunningStartPast graph [] 3 environment action .unit .unit [] .nil,
      GeneralStartedFrom (cleanup_data acquisition).past start 1 ∧
      CoreAllocationHistory.Steps graph 6 (CoreMachine.initial graph) (started start).state ∧
      TicketBound (started start).state (started start).point.machine.stack := by
  obtain ⟨start,causal,⟨generated⟩⟩ := causal_registered_start
  have connected := causal.generated_from_initial generated
  exact ⟨start,causal.registration,by simpa using connected.1,connected.2.2⟩

theorem actual_body_endpoint : bodyEnd.state.control = .returned .unit ∧ bodyEnd.state.nextCleanup = 1 := by
  rw [body_exact]; exact ⟨rfl,rfl⟩
theorem no_fictional_initial_unit : ¬ (initial_endpoint initialInput).focus.expression = .unit := by
  change ¬ original = .unit
  intro impossible
  cases impossible

theorem rejects_wrong_initial_metadata : ¬ InitialInput graph .unit := by
  intro wrong
  have actual : translateFuel graph (graph.nodes.length+1) [] graph.root = .ok original := rfl
  have impossible := Except.ok.inj (actual.symm.trans wrong.translated)
  cases impossible

#print axioms actual_initial_literal
#print axioms bootstrap_three_ranked_edges
#print axioms original_initial_to_registration
#print axioms causal_registered_start
#print axioms six_edges_from_actual_initial
#print axioms actual_body_endpoint
#print axioms no_fictional_initial_unit
#print axioms rejects_wrong_initial_metadata
end Ash.OneShot.CoreCallableInitialChronology.Probes
