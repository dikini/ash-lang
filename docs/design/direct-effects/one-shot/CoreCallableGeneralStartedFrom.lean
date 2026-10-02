import CoreCallableInitialChronology
import CoreCallableGeneratedCleanupRegistration
namespace Ash.OneShot.CoreCallableInitialChronology
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation
open ScopedExpressions ScopedExecution CoreCallableGeneratedChronology CoreCallableRunningOccurrence
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableSiteLineage CoreStrictStack
open CoreCallableGeneralHistory CoreCallableGeneralCleanupRegistration CoreCallableGeneratedTicketBound
open CoreGeneralRestoration

/-- Body continuation accepts only SAME endpoint-threaded named operations. -/
inductive OperationSegment (first : Endpoint graph) : Endpoint graph → Nat → List Owner → List Owner → Type where
  | initial : OperationSegment first first 0 [] []
  | next (earlier : OperationSegment first before count created discharged)
      (operation : Operation before after added removed) :
      OperationSegment first after (count+1) (created++added) (removed++discharged)

theorem OperationSegment.actual_steps {graph : Graph} {first current : Endpoint graph}
    (run : OperationSegment first current count created discharged) :
    CoreAllocationHistory.Steps graph count first.state current.state := by
  induction run with
  | initial => exact .refl _
  | next earlier operation ih => exact .snoc ih operation.actual.1

noncomputable def InitialChronology.extend {graph : Graph} {code : Code} {input : InitialInput graph code}
    {first current : Endpoint graph} (run : InitialChronology input first count created discharged)
    (later : OperationSegment first current laterCount added removed) :
    InitialChronology input current (count+laterCount) (created++added) (removed++discharged) := by
  induction later with
  | initial => simpa using run
  | next earlier operation ih =>
    simpa [Nat.add_assoc,List.append_assoc] using InitialChronology.next ih operation

theorem InitialChronology.lexical_ticket_bound {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current : Endpoint graph} (run : InitialChronology input current count created discharged) :
    TicketBound current.state current.lexical := by
  intro ticket
  have full := run.ticket_bound ticket
  simp only [Endpoint.point,CoreCleanupRunFrames.attach,LexicalUnwind.Machine.stack,
    erase_append,ticketNames_append,List.count_append] at full
  omega

/-- The SAME preceding initial chronology produces both site and ownership at
actual cleanup entry. Literal/closure/current shape guards remain current data. -/
noncomputable def cleanup_from_initial {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current : Endpoint graph} (run : InitialChronology input current count created discharged)
    (ready : CoreCallableGeneratedCurrentScopeConsumers.CleanupReady current) : CleanupInput current := {
  site := ready.site,callback := ready.callback,action := ready.action,body := ready.body
  environment := ready.environment,data := ready.data,node := ready.node,known := ready.known
  kind := ready.kind,shape := ready.shape,postorder := checkShape_postorder graph input.shape
  lineage := by simpa only [ready.empty.focus] using run.site_origins.at ready.control
  rawBody := ready.rawBody,bodyCode := ready.bodyCode,translated := ready.translated,closing := ready.closing
  parameter := ready.parameter,lambdaBody := ready.lambdaBody,callable := ready.callable,identity := ready.identity
  ownership := by
    refine ⟨?_,?_⟩
    · simpa only [TicketBound] using run.lexical_ticket_bound
    · simpa only [ready.empty.focus] using run.scope_origins.at ready.control
  control := ready.control,empty := ready.empty }

structure GeneralStartedFrom
    (registration : GeneralRegisteredCleanupPast graph owners base site callback action body environment data physical target rawBody bodyCode)
    (start : RunningStartPast graph owners action environment data savedValue savedCode physical target)
    (bodyCount : Nat) : Prop where
  bodySteps : CoreAllocationHistory.Steps graph bodyCount
    (registeredState base site body action environment data physical) start.predecessor
  returned : start.predecessor.control = .returned savedValue
  physicalSame : start.predecessor.frames = .cleanupBoundary action environment data.identity :: physical
  extension : HeapExtends base.heap start.predecessor.heap
  installedSame : HEq start.installed (registration.installed.heap_weaken extension)
  historySame : HEq start.originalHistory (registration.history.heap_weaken extension)

/-- Indices retain the SAME original initial prefix, acquisition and named
body prefix at the produced start. No unrelated initial history is attachable. -/
structure CausalStart {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current bodyEnd : Endpoint graph}
    (run : InitialChronology input current count created discharged)
    (cleanup : CleanupInput current)
    (body : OperationSegment (cleanup_result cleanup).after bodyEnd bodyCount bodyCreated bodyDischarged)
    (start : RunningStartPast graph current.owners cleanup.action cleanup.environment cleanup.data savedValue savedCode current.physical current.lexical) : Prop where
  registration : GeneralStartedFrom (cleanup_data cleanup).past start bodyCount
  actual : CoreMachine.next graph bodyEnd.state = .stepped (started start).state
  core : CoreAllocationHistory.Steps graph (count+bodyCount+2) (CoreMachine.initial graph) (started start).state
  target : CoreUnwindRelation.Trace (initial_endpoint input).point.machine (started start).point.machine
    (created ++ [.cleanup cleanup.data.identity] ++ bodyCreated) (bodyDischarged ++ discharged)
  originalBound : TicketBound (start_before start).state current.lexical

/-- This operation-built body prefix begins at actual cleanup_result, never an
independently supplied CoreSteps chain or running start. -/
theorem start_from_registration {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current bodyEnd : Endpoint graph} (run : InitialChronology input current count created discharged)
    (cleanup : CleanupInput current)
    (body : OperationSegment (cleanup_result cleanup).after bodyEnd bodyCount bodyCreated bodyDischarged)
    (returned : bodyEnd.state.control = .returned savedValue)
    (physicalSame : bodyEnd.state.frames = .cleanupBoundary cleanup.action cleanup.environment cleanup.data.identity :: current.physical)
    (saved : ValueRel graph bodyEnd.owners bodyEnd.state.heap savedValue savedCode)
    (lexicalSame : bodyEnd.lexical = .push (.armed cleanup.data) current.lexical)
    (empty : EmptyFocus bodyEnd savedCode bodyScope) :
    ∃ start : RunningStartPast graph current.owners cleanup.action cleanup.environment cleanup.data savedValue savedCode current.physical current.lexical,
      CausalStart run cleanup body start ∧
      Nonempty (Generated start (started start) 0 [] []) := by
  let registration := (cleanup_data cleanup).past
  have registrationStep := (cleanup_result cleanup).core
  have bodySteps : CoreAllocationHistory.Steps graph bodyCount
      (registeredState current.state cleanup.site cleanup.body cleanup.action cleanup.environment cleanup.data current.physical) bodyEnd.state := by
    exact body.actual_steps
  have extension : HeapExtends current.state.heap bodyEnd.state.heap := by
    have first := CoreSuffixSplice.next_heap_extends registrationStep
    have later := CoreCallableGeneratedCleanupRegistration.steps_heap_extends bodySteps
    exact fun i v h => later i v (first i v h)
  let installed := registration.installed.heap_weaken extension
  let history := registration.history.heap_weaken extension
  have fullRun := (InitialChronology.next run (Operation.cleanup cleanup)).extend body
  have bounded : TicketBound bodyEnd.state (.push (.armed cleanup.data) current.lexical) := by
    rw [← lexicalSame]; exact fullRun.lexical_ticket_bound
  obtain ⟨actual,_owned,running,sameInstalled,_history⟩ :=
    normal_start_history installed saved history bounded bodyScope
  let start : RunningStartPast graph current.owners cleanup.action cleanup.environment cleanup.data savedValue savedCode current.physical current.lexical :=
    ⟨bodyEnd.state,bodyEnd.owners,bodyScope,installed,saved,history,running,sameInstalled,actual⟩
  have stateSame : returnedState bodyEnd.state savedValue
      (.cleanupBoundary cleanup.action cleanup.environment cleanup.data.identity :: current.physical) = bodyEnd.state := by
    simp only [returnedState]; rw [← returned,← physicalSame]
  have next := actual.core
  rw [stateSame] at next
  have initialSteps := fullRun.actual_steps
  have steps : CoreAllocationHistory.Steps graph (count+bodyCount+2) (CoreMachine.initial graph) (started start).state := by
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,start,started] using initialSteps.snoc next
  have target : CoreUnwindRelation.Trace (initial_endpoint input).point.machine (started start).point.machine
      (created ++ [.cleanup cleanup.data.identity] ++ bodyCreated) (bodyDischarged ++ discharged) := by
    have trace := fullRun.target_trace
    have edge : CoreUnwindRelation.Trace bodyEnd.point.machine (started start).point.machine [] [] := by
      simpa only [Endpoint.point,CoreCleanupRunFrames.attach,empty.focus,lexicalSame,Stack.append,start,started] using actual.target.trace
    have composed := trace.append edge
    simpa only [Endpoint.point,CoreCleanupRunFrames.attach,empty.focus,lexicalSame,Stack.append,start,started,
      List.append_nil,List.nil_append] using composed
  have originalBound : TicketBound (start_before start).state current.lexical := by
    intro ticket
    have boundedTail := fullRun.lexical_ticket_bound ticket
    simp only [start_before,start,returnedState,lexicalSame,Stack.erase,ExecFrame.erase,Control.ticketNames,List.count_append] at boundedTail ⊢
    omega
  exact ⟨start,⟨⟨bodySteps,returned,physicalSame,extension,HEq.rfl,HEq.rfl⟩,next,steps,target,originalBound⟩,⟨.initial⟩⟩

theorem CausalStart.generated_from_initial {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current bodyEnd after : Endpoint graph}
    {run : InitialChronology input current count created discharged} {cleanup : CleanupInput current}
    {body : OperationSegment (cleanup_result cleanup).after bodyEnd bodyCount bodyCreated bodyDischarged}
    {start : RunningStartPast graph current.owners cleanup.action cleanup.environment cleanup.data savedValue savedCode current.physical current.lexical}
    (causal : CausalStart run cleanup body start)
    (generated : Generated start after laterCount laterCreated laterDischarged) :
    CoreAllocationHistory.Steps graph (count+bodyCount+2+laterCount) (CoreMachine.initial graph) after.state ∧
    CoreUnwindRelation.Trace (initial_endpoint input).point.machine after.point.machine
      ((created ++ [.cleanup cleanup.data.identity] ++ bodyCreated) ++ laterCreated)
      (laterDischarged ++ (bodyDischarged ++ discharged)) ∧
    TicketBound after.state after.point.machine.stack :=
  ⟨causal.core.trans generated.core_steps,causal.target.append generated.target_trace,
    CoreCallableGeneratedTicketBound.Generated.ticket_bound generated causal.originalBound⟩

#print axioms OperationSegment.actual_steps
#print axioms InitialChronology.extend
#print axioms InitialChronology.lexical_ticket_bound
#print axioms cleanup_from_initial
#print axioms start_from_registration
#print axioms CausalStart.generated_from_initial
end Ash.OneShot.CoreCallableInitialChronology
