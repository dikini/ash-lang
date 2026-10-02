import CoreCallableComposedRuntimeCalls
import CoreResumeEntry
namespace Ash.OneShot.CoreCallableComposedRuntimeCompletion
open ScopedExpressions ScopedExecution CoreSyntax CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreCallableGeneratedChronology CoreCallableCallerBarriers CoreCallableGeneralHistory
open CoreCallableComposedRuntimeCalls CoreCallableComposedRuntimeCalls.Original
open CoreResumeFrames ComposedResourceRuntimeOriginProbes
open CoreCallableComposedResourceEntry CoreCallableComposedRuntimeBindings
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Both the saved original and the current front come from the same bind factory. -/
theorem read_bind_lineage : HEq bindInput.past.originalHistory e15.history ∧
    HEq e29.history e16.history := ⟨bindInput.original,HEq.rfl⟩

noncomputable def e30 : Endpoint G where
  state := { e29.state with
    control := .evaluate 17 (.binding 5 (.integer 0) selectedHigher.environment),
    frames := [.resourceBoundary 21 0 0]}
  focus := ⟨branchCode,.none,.nil⟩
  owners := []; maps := []
  physical := e15.physical
  lexical := e15.lexical
  history := e15.history
  frames := rfl

theorem branch_closing : EnvCloses G [] [] (.binding 5 (.integer 0) selectedHigher.environment)
    (.branch (.boolean true) (.variable 7) (.variable 7)) branchCode := by
  have saved := (CoreOrdinaryCompletion.bind_components bindReady.closing).2
  have result := saved.beta_argument (ValueRel.integer (graph := G) (owners := []) (heap := []) (value := 0))
  exact result

/-- Restoring the saved caller uses the exact original body barrier. -/
theorem bind_actual : CoreMachine.next G e29.state = .stepped e30.state ∧
    CoreUnwindRelation.Positive e29.point.machine e30.point.machine [] [] := by
  have saved := (CoreOrdinaryCompletion.bind_components bindReady.closing).2
  have completed := CoreStrictSteps.bind_complete (base := e29.state)
    bindReady.bodyTranslated saved (ValueRel.integer (value := 0)) bindReady.closed
    [.resourceBoundary 21 0 0] Execution.Scope.none e15.lexical
  refine ⟨?_,?_⟩
  · exact completed.1
  · have plug := RawStep.plug bindReady.plain (.integer 0)
      (ValueRel.integer (graph := G) (owners := []) (heap := []) (value := 0)).closed
      Execution.Scope.none e15.lexical
    exact .next (.evaluate plug (by trivial))
      (.one (.evaluate completed.2.1 (by trivial)))

theorem branch_endpoint : e30.state.control = .evaluate 17 (.binding 5 (.integer 0) selectedHigher.environment) ∧
    e30.focus.expression = branchCode ∧ e30.maps = [] ∧
    e30.physical = [.resourceBoundary 21 0 0] := ⟨rfl,rfl,rfl,rfl⟩

/-- A ready Boolean branch uses the existing traversal family and potential. -/
theorem ready_branch_decreases {graph : Graph} {base : CoreMachine.State}
    (ordered : CoreTranslationFuel.Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .matchCases scrutinee (CoreStrictSteps.booleanArms yes no reversed))
    (environment : Environment) (tail : List CoreMachine.Frame) :
    CoreStrictPotential.potential graph
      {base with
        control := .evaluate scrutinee environment
        frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: tail,
        observations := base.observations ++ [.entered site]} <
    CoreStrictPotential.potential graph {base with control := .evaluate site environment,frames := tail} := by
  have cost := CoreStrictPotential.cost_recurrence ordered known
  cases reversed <;>
    simp only [kind,CoreStrictSteps.booleanArms,Bool.false_eq_true,↓reduceIte,
      CoreSyntax.Kind.children,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at cost ⊢ <;>
    simp only [CoreStrictPotential.potential,CoreStrictPotential.frameWeight,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] <;> omega

def callerEnvironment : Environment := .binding 5 (.integer 0) selectedHigher.environment

def branchPlain : PlainData := ⟨.branch (.integer 17) (.integer 17),.none,.boolean,.integer,[],rfl⟩

noncomputable def e31 : Endpoint G where
  state := {e30.state with
    control := .evaluate 14 callerEnvironment
    frames := .matchCases (CoreStrictSteps.booleanArms 15 16 false) callerEnvironment :: e30.state.frames
    observations := e30.state.observations ++ [.entered 17]}
  focus := ⟨branchCode,.none,.nil⟩
  owners := []
  maps := [([], .matchCases (CoreStrictSteps.booleanArms 15 16 false) callerEnvironment)]
  physical := e30.physical
  lexical := e30.lexical
  history := e30.history
  frames := rfl

theorem branch_frame : PlainFrameRel G [] []
    (.matchCases (CoreStrictSteps.booleanArms 15 16 false) callerEnvironment) branchPlain :=
  .booleanMatch (yesFuel := 24) (noFuel := 24) (rawYes := .variable 7) (rawNo := .variable 7) rfl rfl (branch_components branch_closing).2.1
    (branch_components branch_closing).2.2

theorem branch_entry_actual : CoreMachine.next G e30.state = .stepped e31.state ∧
    Matching G e30 e31 [] [] := by
  refine ⟨rfl,.administrative rfl (.inr (by rfl)) ?_⟩
  exact ready_branch_decreases (base := e30.state)
    (CoreTranslationFuel.checkShape_postorder G initialInput.shape)
    (site := 17) (node := CoreTranslation.Examples.node 17
      (.matchCases 14 (CoreStrictSteps.booleanArms 15 16 false)) .integer)
    rfl rfl callerEnvironment [.resourceBoundary 21 0 0]

noncomputable def e32 : Endpoint G := {e31 with
  state := {e31.state with
    control := .returned (.boolean true)
    observations := e31.state.observations ++ [.entered 14]}}

theorem boolean_actual : CoreMachine.next G e31.state = .stepped e32.state ∧
    Matching G e31 e32 [] [] := by
  have witness := (CoreAdministrativeSteps.boolean_evaluate (base := e31.state)
    (graph := G) (owners := []) (index := 14)
    (node := CoreTranslation.Examples.node 14 (.boolean true) .boolean)
    rfl rfl (branch_components branch_closing).1
    e31.state.frames).1
  refine ⟨witness.core,.administrative rfl (.inl witness.permitted) ?_⟩
  exact CoreStrictPotential.administrative_potential witness

noncomputable def e33 : Endpoint G where
  state := {e32.state with control := .evaluate 15 callerEnvironment,frames := e30.state.frames}
  focus := ⟨.integer 17,.none,.nil⟩
  owners := []; maps := []
  physical := e30.physical
  lexical := e30.lexical
  history := e30.history
  frames := rfl

theorem selection_actual : CoreMachine.next G e32.state = .stepped e33.state ∧
    CoreUnwindRelation.Positive e32.point.machine e33.point.machine [] [] := by
  have completed := CoreStrictSteps.branch_complete (base := e32.state)
    (graph := G) (owners := []) (fuel := 24) (yes := 15) (no := 16)
    (rawYes := .variable 7) (rawNo := .variable 7)
    rfl rfl (branch_components branch_closing).2.1 (branch_components branch_closing).2.2
    true false [.resourceBoundary 21 0 0] Execution.Scope.none e30.lexical
  exact ⟨completed.1,.one (.evaluate completed.2.1 (by trivial))⟩

noncomputable def e34 : Endpoint G := {e33 with
  state := {e33.state with
    control := .returned (.integer 17)
    observations := e33.state.observations ++ [.entered 15]}}

theorem outer_lookup : callerEnvironment.lookup 7 = some (.integer 17) := rfl

theorem outer_actual : CoreMachine.next G e33.state = .stepped e34.state ∧
    Matching G e33 e34 [] [] := by
  obtain ⟨value,lookup,witness,translation⟩ := CoreAdministrativeSteps.variable_evaluate
    (base := e33.state) (graph := G) (owners := []) (index := 15)
    (node := CoreTranslation.Examples.node 15 (.variable 7) .integer)
    rfl rfl (branch_components branch_closing).2.1
    (ValueRel.integer (graph := G) (owners := []) (heap := []) (value := 17)).closed
    e33.state.frames
  have same : value = .integer 17 := Option.some.inj (lookup.symm.trans outer_lookup)
  subst value
  exact ⟨witness.core,.administrative rfl (.inl witness.permitted)
    (CoreStrictPotential.administrative_potential witness)⟩

noncomputable def e35 : Endpoint G where
  state := {e34.state with frames := [],observations := e34.state.observations ++ [.released 0]}
  focus := ⟨.integer 17,.none,.nil⟩
  owners := []; maps := []; physical := []; lexical := .nil
  history := .nil
  frames := rfl

theorem release_actual : CoreMachine.next G e34.state = .stepped e35.state ∧
    CoreUnwindRelation.Positive e34.point.machine e35.point.machine [] [.resource 0] := by
  have returned := CoreEffectEntry.cell_leave (base := e34.state) (savedOwners := [])
    (key := 0) (payload := 0) (scope := .none) (answer := .integer)
    (CoreEffectFrames.BoundaryRel.cell selection.resourceKnown selection.resourceKind)
    (ValueRel.integer (graph := G) (owners := []) (heap := []) (value := 17))
    Execution.Scope.none [] Stack.nil
  exact ⟨returned.1,.one (.evaluate returned.2.1 (by trivial))⟩

theorem branch_flattened : OrdinaryWithMaps G [] e31.maps (.boolean true) .none
    branchCode .none .nil := by
  exact ⟨e31.maps,[],rfl,
    .cons branch_frame (ValueRel.boolean (graph := G) (owners := []) (heap := []) (value := true)).closed .nil,
    .nil⟩

/-- The strict branch map and retained cell history are separately derived. -/
theorem completion_histories :
    CoreGeneralStack.GeneralSegment G e30.state.heap e30.physical e30.lexical ∧
    CoreGeneralStack.GeneralSegment G e31.state.heap e31.physical e31.lexical ∧
    CoreGeneralStack.GeneralSegment G e35.state.heap e35.physical e35.lexical :=
  ⟨e30.history.related,e31.history.related,e35.history.related⟩

theorem remaining_steps : CoreAllocationHistory.Steps G 6 e29.state e35.state :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.refl e29.state) bind_actual.1)
    branch_entry_actual.1) boolean_actual.1) selection_actual.1) outer_actual.1) release_actual.1

theorem remaining_target : CoreUnwindRelation.Trace e29.point.machine e35.point.machine [] [.resource 0] :=
  bind_actual.2.trace.append ((branch_entry_actual.2.target_trace).append
    ((boolean_actual.2.target_trace).append (selection_actual.2.trace.append
      ((outer_actual.2.target_trace).append release_actual.2.trace))))

theorem initial_to_done : CoreAllocationHistory.Steps G 35 (CoreMachine.initial G) e35.state :=
  initial_to_read.trans remaining_steps

theorem final_done : CoreMachine.next G e35.state = .done (.integer 17) := rfl

theorem exact_observations : e35.state.observations =
    e29.state.observations ++ [.entered 17,.entered 14,.entered 15,.released 0] := by
  simp only [e35,e34,e33,e32,e31,e30,List.append_assoc,List.cons_append,List.nil_append]

theorem final_ledger : e35.state.nextActivation = 1 ∧
    CoreAllocationHistory.acquiredKeys e35.state.observations = [0] ∧
    CoreAllocationHistory.History e35.state := by
  have history := CoreAllocationHistory.initial_steps_history G initial_to_done
  exact ⟨rfl,history,history⟩

theorem full_observations : e35.state.observations =
    [.entered 22,.entered 0,.entered 21,.entered 3,.entered 1,.entered 2,.acquired 21 0,
     .entered 20,.entered 6,.entered 19,.entered 10,.entered 18,.entered 13,.entered 11,
     .entered 12,.entered 9,.entered 7,.entered 8,.entered 5,.entered 4,.read 0 0,
     .entered 17,.entered 14,.entered 15,.released 0] := by
  have site : bindInput.past.site = 18 := (CoreMachine.Control.evaluate.inj bindInput.control).1.symm
  change _ = _
  rw [exact_observations]
  change (((e15.state.observations ++ [.entered bindInput.past.site]) ++
    [.entered 13,.entered 11,.entered 12,.entered 9,.entered 7,.entered 8,.entered 5,.entered 4,.read 0 0]) ++
    [.entered 17,.entered 14,.entered 15,.released 0]) = _
  rw [site]
  rfl

theorem final_stacks : e35.state.frames = [] ∧ e35.maps = [] ∧
    e35.physical = [] ∧ e35.lexical = .nil := ⟨rfl,rfl,rfl,rfl⟩

theorem saved_caller : e30.state.control = .evaluate 17 callerEnvironment ∧
    e30.state.control ≠ .evaluate 17 readerBodyEnvironment := by
  refine ⟨rfl,?_⟩
  intro impossible
  have same := (CoreMachine.Control.evaluate.inj impossible).2
  have head := CoreMachine.Environment.binding.inj same
  omega

theorem final_not_read_reply : e35.state.control ≠ e29.state.control := by
  change CoreMachine.Control.returned (.integer 17) ≠ .returned (.integer 0)
  intro impossible
  have same := CoreMachine.Value.integer.inj (CoreMachine.Control.returned.inj impossible)
  omega

theorem initial_target_done : ∃ created discharged,
    CoreUnwindRelation.Trace (.eval selection.p0.target) e35.point.machine created
      (.resource 0 :: discharged) := by
  obtain ⟨created,discharged,prior⟩ := initial_target_trace
  exact ⟨created,discharged,by simpa using prior.append remaining_target⟩

open CoreCallableComposedResourceOrigins CoreCallableComposedResourceOrigins.Probes
open CoreCallableComposedCapturedHandle

/-- A completed output retains the SAME checked private constructor families.
It adds no admission or future environment premise. -/
structure Completed {resource : Opened} {staticReader : ReaderPath resource}
    {readerReceipt : Current staticReader.path selection.s8.nextActivation (by simp)}
    {handleReceipt : CapturedHandle staticReader.path selection.s8.nextActivation (by simp)}
    {staticHigher : HigherPath resource}
    {higherReceipt : Current staticHigher.path selection.s8.nextActivation (by simp)}
    (checked : CheckedCall staticReader readerReceipt handleReceipt staticHigher higherReceipt) where
  retained : CheckedCall staticReader readerReceipt handleReceipt staticHigher higherReceipt
  same : retained = checked
  calls : CoreMachine.next G e20.state = .stepped e21.state ∧
    CoreMachine.next G e25.state = .stepped e26.state
  steps : CoreAllocationHistory.Steps G 35 (CoreMachine.initial G) e35.state
  finish : CoreMachine.next G e35.state = .done (.integer 17)
  observations : e35.state.observations =
    e29.state.observations ++ [.entered 17,.entered 14,.entered 15,.released 0]

noncomputable def complete {resource : Opened} {staticReader : ReaderPath resource}
    {readerReceipt : Current staticReader.path selection.s8.nextActivation (by simp)}
    {handleReceipt : CapturedHandle staticReader.path selection.s8.nextActivation (by simp)}
    {staticHigher : HigherPath resource}
    {higherReceipt : Current staticHigher.path selection.s8.nextActivation (by simp)}
    (checked : CheckedCall staticReader readerReceipt handleReceipt staticHigher higherReceipt) : Completed checked :=
  ⟨checked,rfl,checked_call_actual checked,initial_to_done,final_done,exact_observations⟩

/-- The existing executable join runs here; successful outputs are not metadata seeds. -/
noncomputable def finish_checked {resource : Opened} (staticReader : ReaderPath resource)
    (readerReceipt : Current staticReader.path selection.s8.nextActivation (by simp))
    (handleReceipt : CapturedHandle staticReader.path selection.s8.nextActivation (by simp))
    (staticHigher : HigherPath resource)
    (higherReceipt : Current staticHigher.path selection.s8.nextActivation (by simp)) :
    Except CoreCallableComposedRuntimeBindings.Error
      (Σ checked : CheckedCall staticReader readerReceipt handleReceipt staticHigher higherReceipt,Completed checked) := do
  let checked ← check_call staticReader readerReceipt handleReceipt staticHigher higherReceipt
  .ok ⟨checked,complete checked⟩

theorem finish_checked_executed {resource : Opened} (staticReader : ReaderPath resource)
    (readerReceipt : Current staticReader.path selection.s8.nextActivation (by simp))
    (handleReceipt : CapturedHandle staticReader.path selection.s8.nextActivation (by simp))
    (staticHigher : HigherPath resource)
    (higherReceipt : Current staticHigher.path selection.s8.nextActivation (by simp)) :
    ∃ output, finish_checked staticReader readerReceipt handleReceipt staticHigher higherReceipt = .ok output := by
  obtain ⟨checked,accepted⟩ := check_call_executed staticReader readerReceipt handleReceipt staticHigher higherReceipt
  unfold finish_checked
  rw [accepted]
  exact ⟨_,rfl⟩

#print axioms branch_flattened
#print axioms completion_histories
#print axioms remaining_steps
#print axioms remaining_target
#print axioms initial_to_done
#print axioms final_done
#print axioms exact_observations
#print axioms final_ledger
#print axioms full_observations
#print axioms final_stacks
#print axioms saved_caller
#print axioms final_not_read_reply
#print axioms initial_target_done
#print axioms finish_checked_executed
#print axioms ready_branch_decreases
#print axioms branch_frame
#print axioms branch_entry_actual
#print axioms boolean_actual
#print axioms selection_actual
#print axioms outer_lookup
#print axioms outer_actual
#print axioms release_actual
#print axioms read_bind_lineage
#print axioms bind_actual
#print axioms branch_closing
#print axioms branch_endpoint
end Ash.OneShot.CoreCallableComposedRuntimeCompletion
