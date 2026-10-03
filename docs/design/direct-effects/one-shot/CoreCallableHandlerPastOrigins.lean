import CoreHandlerHistory
import CoreCallableGeneralStartedFrom

namespace Ash.OneShot.CoreCallableHandlerPastOrigins
set_option linter.unusedSimpArgs false
open CoreSyntax CoreMachine CoreValueRelation CoreStrictStack ScopedExpressions ScopedExecution
open CoreCallableGeneralHistory CoreCallableRunningOccurrence CoreCallableGeneratedChronology
open CoreCallableInitialChronology CoreCallableGeneralCleanupRegistration CoreGeneralCaptureResume

/-- The SAME recorded actual entry, not a source annotation, fixes activation. -/
theorem GeneralHandlerPast.activation_at_counter
    (past : GeneralHandlerPast graph owners site environment data) :
    data.activation = past.predecessor.nextHandler := by
  have actual := past.actual
  simp only [CoreMachine.next,past.known,past.kind] at actual
  have frames := congrArg (fun state : CoreMachine.State => state.frames)
    (Outcome.stepped.inj actual)
  have head := (List.cons.inj frames).1
  exact (CoreMachine.Frame.handlerBoundary.inj head).2.2.symm

/-- Every named operation uses its computed actual edge. This includes all
thirteen constructors and assumes no future success or installation receipt. -/
theorem Operation.handler_delta
    (operation : Operation (graph := graph) before after created discharged) :
    CoreHandlerHistory.HandlerDelta before.state after.state :=
  CoreHandlerHistory.next_delta graph _ _ operation.actual.1

/-- The only named entry contributing a handler activation is handler. -/
def Operation.added_handlers
    (operation : Operation (graph := graph) before after created discharged) : List Nat :=
  match operation with
  | .handler _ => [before.state.nextHandler]
  | _ => []

/-- Exact projection for all thirteen existing named transition families. -/
theorem Operation.handler_projection
    (operation : Operation (graph := graph) before after created discharged) :
    after.state.nextHandler = before.state.nextHandler + (Operation.added_handlers operation).length ∧
    CoreHandlerHistory.enteredHandlers after.state.observations =
      CoreHandlerHistory.enteredHandlers before.state.observations ++ (Operation.added_handlers operation) := by
  cases operation <;>
    simp [Operation.added_handlers,cleanup_result,registeredState,bind_result,beta_result,
      bind_return_result,handler_result,handler_return_result,literal_result,entry_result,
      swap_result,tuple_result,capture_result,captureAfter,resume_result,CoreGeneralCaptureResume.resumeAfter,
      spent_return_result,CoreGeneralRestoration.observedState,CoreHandlerHistory.enteredHandlers]
  rename_i input
  simpa only [input.predecessor] using GeneralHandlerPast.activation_at_counter input.installation

/-- Actual initial chronology supplies original-root counter history. -/
theorem InitialChronology.handler_history
    (run : InitialChronology input current count created discharged) :
    CoreHandlerHistory.History current.state :=
  CoreHandlerHistory.initial_steps_history _ run.actual_steps

/-- Arbitrary running starts do not imply initial history. The EXISTING causal
start links the SAME initial/body/start, then the SAME Generated continuation. -/
theorem CausalStart.handler_history
    {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current bodyEnd after : Endpoint graph}
    {run : InitialChronology input current count created discharged} {cleanup : CleanupInput current}
    {body : OperationSegment (cleanup_result cleanup).after bodyEnd bodyCount bodyCreated bodyDischarged}
    {start : RunningStartPast graph current.owners cleanup.action cleanup.environment cleanup.data
      savedValue savedCode current.physical current.lexical}
    (causal : CausalStart run cleanup body start)
    (generated : Generated start after laterCount laterCreated laterDischarged) :
    CoreHandlerHistory.History after.state :=
  CoreHandlerHistory.initial_steps_history graph (causal.generated_from_initial generated).1

/-- These negatives reject exact receipt attachment mismatch, never arbitrary
inequality between two earlier states that may join the same actual past. -/
theorem HandlerInput.predecessor_mismatch (input : HandlerInput endpoint)
    (different : input.installation.predecessor ≠ endpoint.state) : False :=
  different input.predecessor

theorem HandlerInput.suffix_mismatch (input : HandlerInput endpoint)
    (different : input.installation.originalSuffix ≠ endpoint.physical) : False :=
  different input.suffix

#print axioms GeneralHandlerPast.activation_at_counter
#print axioms Operation.handler_delta
#print axioms Operation.handler_projection
#print axioms InitialChronology.handler_history
#print axioms CausalStart.handler_history
#print axioms HandlerInput.predecessor_mismatch
#print axioms HandlerInput.suffix_mismatch
end Ash.OneShot.CoreCallableHandlerPastOrigins
