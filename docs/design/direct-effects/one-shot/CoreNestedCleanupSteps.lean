import CoreNormalCleanupSteps
import CoreRunningSplice

/-! Normal cleanup inside a running callback preserves both authenticated tails.
Start saves the actual current value; Unit completion restores it and the saved
scope. These are current redex correspondences, not callback termination, user
handler capture, or projected-left completion into unwind. -/
namespace Ash.OneShot.CoreNestedCleanupSteps
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreCleanupFrames
  CoreCleanupRunFrames CoreNormalCleanupSteps CoreUnwindRelation CoreSuffixSplice CoreRunningSplice

/-- Actual start under the same enclosing carrier. The new running tail is the
structural composition of the existing normal carrier and that enclosing tail. -/
theorem nested_start {base : CoreMachine.State}
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (pending : PushedWithMaps graph base.heap pendingMaps pendingTarget)
    (enclosing : RunningTail graph base.heap physical lexical)
    (scope : Scope) :
    CoreResourceUnwind.StepWitness graph
      ⟨appendFrames (startBefore base action environment data.identity savedValue pendingMaps) physical,
        .eval (attach ⟨savedCode,scope,.push (.armed data) pendingTarget⟩ lexical),
        callerOwners,(cleanupOwners,.cleanupBoundary action environment data.identity)::pendingMaps⟩
      ⟨appendFrames (startAfter base action environment data.identity savedValue pendingMaps) physical,
        .eval (attach ⟨.app data.action .unit,.none,.push (.running data savedCode saved.closed) pendingTarget⟩ lexical),
        cleanupOwners,[]⟩ [] [] := by
  obtain ⟨current,actual,target,_normalSuccessor⟩ := normal_start delayed saved pending scope
  obtain ⟨callback,translated,closed⟩ := delayed_action delayed
  have beforeComponent : ComponentMapped graph callerOwners
      ((cleanupOwners,.cleanupBoundary action environment data.identity)::pendingMaps)
      (isolate (appendFrames (startBefore base action environment data.identity savedValue pendingMaps) physical)
        ((cleanupOwners,.cleanupBoundary action environment data.identity)::pendingMaps))
      ⟨savedCode,scope,.push (.armed data) pendingTarget⟩ := by
    simpa [isolate,appendFrames,startBefore,framesOf_cons] using current
  have afterComponent : ComponentMapped graph cleanupOwners []
      (isolate (appendFrames (startAfter base action environment data.identity savedValue pendingMaps) physical) [])
      ⟨.app data.action .unit,.none,.nil⟩ :=
    ⟨rfl,_,.none,.evaluate translated closed,pushed_mapped .nil⟩
  refine ⟨.runningCleanup enclosing beforeComponent ?_,next_append actual physical,
    .one (transition_append target lexical),?_⟩
  · simp [appendFrames,startBefore,framesOf_cons]
  · have combined : RunningTail graph base.heap
        ((.cleanupCompletion data.identity savedValue::framesOf pendingMaps)++physical)
        ((Stack.push (.running data savedCode saved.closed) pendingTarget).append lexical) :=
      .append (.normal delayed saved pending) enclosing
    simpa [attach,Stack.append] using
      Related.runningCleanup
        (state := appendFrames (startAfter base action environment data.identity savedValue pendingMaps) physical)
        combined afterComponent (by rfl)

/-- Actual Unit finish uses the same delayed/saved/pending/enclosing witnesses.
The enclosing callback remains running; no future result is supplied. -/
theorem nested_finish {base : CoreMachine.State}
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (pending : PushedWithMaps graph base.heap pendingMaps pendingTarget)
    (enclosing : RunningTail graph base.heap physical lexical)
    (activeOwners : CoreTranslation.OwnerMap) (scope : Scope) :
    CoreResourceUnwind.StepWitness graph
      ⟨appendFrames (finishBefore base data.identity savedValue pendingMaps) physical,
        .eval (attach ⟨.unit,scope,.push (.running data savedCode saved.closed) pendingTarget⟩ lexical),activeOwners,[]⟩
      ⟨appendFrames (finishAfter base data.identity savedValue pendingMaps) physical,
        .eval (attach ⟨savedCode,data.scope,pendingTarget⟩ lexical),callerOwners,pendingMaps⟩
      [] [.cleanup data.identity] := by
  obtain ⟨_normalCurrent,actual,target,successor⟩ := normal_finish delayed saved pending activeOwners scope
  have beforeComponent : ComponentMapped graph activeOwners []
      (isolate (appendFrames (finishBefore base data.identity savedValue pendingMaps) physical) [])
      ⟨.unit,scope,.nil⟩ :=
    ⟨rfl,.unit,scope,.returned .unit,pushed_mapped .nil⟩
  have afterComponent : ComponentMapped graph callerOwners pendingMaps
      (isolate (appendFrames (finishAfter base data.identity savedValue pendingMaps) physical) pendingMaps)
      ⟨savedCode,data.scope,pendingTarget⟩ := by
    simpa [isolate,appendFrames,finishAfter] using successor
  have combined : RunningTail graph base.heap
      ((.cleanupCompletion data.identity savedValue::framesOf pendingMaps)++physical)
      ((Stack.push (.running data savedCode saved.closed) pendingTarget).append lexical) :=
    .append (.normal delayed saved pending) enclosing
  refine ⟨?_,next_append actual physical,.one (transition_append target lexical),
    .runningCleanup enclosing afterComponent ?_⟩
  · simpa [attach,Stack.append] using
      Related.runningCleanup
        (state := appendFrames (finishBefore base data.identity savedValue pendingMaps) physical)
        combined beforeComponent (by rfl)
  · rfl

/-- Start records precisely one new callback-start observation. -/
theorem start_observations (base : CoreMachine.State) :
    (appendFrames (startAfter base action environment identity savedValue pendingMaps) physical).observations =
      base.observations ++ [.cleanupStarted identity] := rfl

/-- Completion records its boundary while retaining the exact saved value. -/
theorem finish_observations (base : CoreMachine.State) :
    (appendFrames (finishAfter base identity savedValue pendingMaps) physical).observations =
      base.observations ++ [.cleanupFinished identity] ∧
    (appendFrames (finishAfter base identity savedValue pendingMaps) physical).control = .returned savedValue :=
  ⟨rfl,rfl⟩

/-- Accounting refers to the same positive segment used by the Core link. -/
theorem completion_accounting
    (witness : CoreResourceUnwind.StepWitness graph before after [] [.cleanup identity]) :
    before.machine.stack.erase.owners.Perm (after.machine.stack.erase.owners ++ [.cleanup identity]) := by
  simpa using running_accounting witness

/-- Existing beta correspondence applies under the composed carrier without
any new callback evaluator or a future related endpoint. -/
theorem beta_nested {base : CoreMachine.State}
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (pending : PushedWithMaps graph base.heap pendingMaps pendingTarget)
    (enclosing : RunningTail graph base.heap physical lexical)
    (function : ValueRel graph codeOwners base.heap (.closure parameter body captured) (.lambda parameter result))
    (argument : ValueRel graph codeOwners base.heap value argumentCode)
    (plain : PlainData) (context : plain.context = .appArgument (.lambda parameter result))
    (older : PushedWithMaps graph base.heap annotations target)
    (runtimeScope : Scope) (frameOwners : CoreTranslation.OwnerMap) :
    CoreResourceUnwind.StepWitness graph
      ⟨appendFrames {base with control := .returned value,frames := .applyArgument (.closure parameter body captured)::framesOf annotations}
          ((.cleanupCompletion data.identity savedValue::framesOf pendingMaps)++physical),
        .eval (attach ⟨.app (.lambda parameter result) argumentCode,plain.scope,target⟩
          ((Stack.push (.running data savedCode saved.closed) pendingTarget).append lexical)),
        codeOwners,(frameOwners,.applyArgument (.closure parameter body captured))::annotations⟩
      ⟨appendFrames {base with control := .evaluate body (.binding parameter value captured),frames := framesOf annotations}
          ((.cleanupCompletion data.identity savedValue::framesOf pendingMaps)++physical),
        .eval (attach ⟨result.subst parameter argumentCode,.none,target⟩
          ((Stack.push (.running data savedCode saved.closed) pendingTarget).append lexical)),[],annotations⟩ [] [] :=
  beta_running function argument plain context older (.append (.normal delayed saved pending) enclosing) runtimeScope frameOwners

#print axioms nested_start
#print axioms nested_finish
#print axioms start_observations
#print axioms finish_observations
#print axioms completion_accounting
#print axioms beta_nested
end Ash.OneShot.CoreNestedCleanupSteps
