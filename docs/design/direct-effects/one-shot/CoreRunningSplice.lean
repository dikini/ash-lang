import CoreSuffixSplice
import CoreResourceUnwind

/-! Successful isolated components extend above the same authenticated running
cleanup tail. Both full Related endpoints are derived here. The beta connection
constructs isolated components from current lexical/value evidence; no future
callback success or selection into the appended tail is assumed. -/
namespace Ash.OneShot.CoreRunningSplice
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack
  CoreCleanupRunFrames CoreUnwindRelation CoreSuffixSplice

set_option linter.unusedSimpArgs false

def appendMachine (machine : LexicalUnwind.Machine) (suffix : Stack) : LexicalUnwind.Machine :=
  match machine with
  | .eval configuration => .eval (appendStack configuration suffix)
  | .unwind scope stack => .unwind scope (stack.append suffix)

/-- Ordinary guards are retained, including exclusion of legacy raw discard. -/
theorem transition_append (step : LexicalUnwind.Transition before after created discharged) (suffix : Stack) :
    LexicalUnwind.Transition (appendMachine before suffix) (appendMachine after suffix) created discharged := by
  cases step with
  | evaluate step allowed => exact .evaluate (raw_step_append step suffix) (ordinary_append allowed suffix)
  | advance step => exact .advance (LexicalUnwind.append step suffix)
  | startCleanup => exact .startCleanup
  | finishCleanup => exact .finishCleanup
  | discard binder ticket identity scope caller input answer front captured tail resolve unprotected =>
    simpa [appendMachine,appendStack,Stack.append,stack_append_assoc] using
      LexicalUnwind.Transition.discard binder ticket identity scope caller input answer front captured (tail.append suffix) resolve unprotected
  | finishClose => exact .finishClose
  | retireValue closed => exact .retireValue closed
  | closeValue closed => exact .closeValue closed

theorem positive_append (positive : Positive before after created discharged) (suffix : Stack) :
    Positive (appendMachine before suffix) (appendMachine after suffix) created discharged := by
  induction positive with
  | one step => exact .one (transition_append step suffix)
  | next step rest ih => exact .next (transition_append step suffix) ih

theorem trace_append_suffix (trace : Trace before after created discharged) (suffix : Stack) :
    Trace (appendMachine before suffix) (appendMachine after suffix) created discharged := by
  induction trace with
  | refl => exact .refl _
  | next step rest ih => exact .next (transition_append step suffix) ih

private theorem isolated_append (component : ComponentMapped graph owners maps state target) (suffix : List CoreMachine.Frame) :
    isolate (appendFrames state suffix) maps = state := by
  simp only [isolate,appendFrames]
  rw [←component.1]

/-- Isolated endpoint proofs are reused outputs of redex correspondence lemmas.
Neither full running Related endpoint nor a successful callback is an input.
Heap extension comes from the actual isolated evaluator step. -/
theorem running_positive
    (carrier : RunningTail graph before.heap physical lexical)
    (current : ComponentMapped graph beforeOwners beforeMaps before beforeTarget)
    (core : CoreMachine.next graph before = .stepped after)
    (target : Positive (.eval beforeTarget) (.eval afterTarget) created discharged)
    (successor : ComponentMapped graph afterOwners afterMaps after afterTarget) :
    CoreResourceUnwind.StepWitness graph
      ⟨appendFrames before physical,.eval (attach beforeTarget lexical),beforeOwners,beforeMaps⟩
      ⟨appendFrames after physical,.eval (attach afterTarget lexical),afterOwners,afterMaps⟩ created discharged := by
  have beforeComponent : ComponentMapped graph beforeOwners beforeMaps (isolate (appendFrames before physical) beforeMaps) beforeTarget := by
    rw [isolated_append current physical]
    exact current
  have afterComponent : ComponentMapped graph afterOwners afterMaps (isolate (appendFrames after physical) afterMaps) afterTarget := by
    rw [isolated_append successor physical]
    exact successor
  have extended := carrier.heap_weaken (next_heap_extends core)
  refine ⟨.runningCleanup carrier beforeComponent ?_,next_append core physical,?_,.runningCleanup extended afterComponent ?_⟩
  · change before.frames ++ physical = framesOf beforeMaps ++ physical
    rw [current.1]
  · exact positive_append target lexical
  · change after.frames ++ physical = framesOf afterMaps ++ physical
    rw [successor.1]

/-- One ordinary target step is the same exact event witness after extension. -/
theorem running_raw
    (carrier : RunningTail graph before.heap physical lexical)
    (current : ComponentMapped graph beforeOwners beforeMaps before beforeTarget)
    (core : CoreMachine.next graph before = .stepped after)
    (target : RawStep beforeTarget afterTarget created discharged)
    (allowed : LexicalUnwind.ordinary beforeTarget.expression)
    (successor : ComponentMapped graph afterOwners afterMaps after afterTarget) :
    CoreResourceUnwind.StepWitness graph
      ⟨appendFrames before physical,.eval (attach beforeTarget lexical),beforeOwners,beforeMaps⟩
      ⟨appendFrames after physical,.eval (attach afterTarget lexical),afterOwners,afterMaps⟩ created discharged :=
  running_positive carrier current core (ordinary_step target allowed) successor

/-- General beta above any authenticated normal or projected running tail.
All isolated interpretations are derived from current closure, argument and
saved ordinary-frame evidence using beta_complete_mapped. -/
theorem beta_running {base : CoreMachine.State}
    (function : ValueRel graph codeOwners base.heap (.closure parameter body saved) (.lambda parameter result))
    (argument : ValueRel graph codeOwners base.heap value argumentCode)
    (plain : PlainData) (context : plain.context = .appArgument (.lambda parameter result))
    (older : PushedWithMaps graph base.heap annotations target)
    (carrier : RunningTail graph base.heap physical lexical)
    (runtimeScope : Scope) (frameOwners : CoreTranslation.OwnerMap) :
    CoreResourceUnwind.StepWitness graph
      ⟨appendFrames {base with control := .returned value,frames := .applyArgument (.closure parameter body saved) :: framesOf annotations} physical,
        .eval (attach ⟨.app (.lambda parameter result) argumentCode,plain.scope,target⟩ lexical),
        codeOwners,(frameOwners,.applyArgument (.closure parameter body saved))::annotations⟩
      ⟨appendFrames {base with control := .evaluate body (.binding parameter value saved),frames := framesOf annotations} physical,
        .eval (attach ⟨result.subst parameter argumentCode,.none,target⟩ lexical),[],annotations⟩ [] [] := by
  obtain ⟨current,next,step,successor⟩ := beta_complete_mapped function argument plain context older runtimeScope frameOwners
  exact running_raw carrier current next step (by trivial) successor

/-- This accounting refers to the same exposed target steps, not a separately
chosen execution between the two configurations. It does not assert freshness. -/
theorem running_accounting
    (witness : CoreResourceUnwind.StepWitness graph before after created discharged) :
    (before.machine.stack.erase.owners ++ created).Perm (after.machine.stack.erase.owners ++ discharged) :=
  (CoreResourceUnwind.AccountedChain.last witness).accounting

#print axioms transition_append
#print axioms positive_append
#print axioms trace_append_suffix
#print axioms running_positive
#print axioms running_raw
#print axioms beta_running
#print axioms running_accounting
end Ash.OneShot.CoreRunningSplice
