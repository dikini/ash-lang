import CoreGeneralCaptureResume
import CoreNormalCleanupSteps

/-! Completion redexes preserve the same arbitrary restored segment. Saved
values retain ValueRel, and physical/lexical close labels remain a local pair.
No callback result, future relation, admission or freshness is assumed. -/
namespace Ash.OneShot.CoreGeneralRestoration
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreEffectFrames
  CoreCleanupFrames CoreCleanupRunFrames CoreUnwindRelation CoreGeneralStack CoreGeneralCaptureResume
set_option linter.unusedSimpArgs false

/-- Construct evaluation correspondence from a current returned value. -/
theorem returned_related
    (segment : GeneralSegment graph state.heap physical lexical)
    (value : ValueRel graph owners state.heap returned code)
    (control : state.control = .returned returned) (frames : state.frames = physical) (scope : Scope) :
    GeneralRelated graph ⟨state,.eval ⟨code,scope,lexical⟩,owners,[]⟩ := by
  have component : ComponentMapped graph owners [] (isolate state []) ⟨code,scope,.nil⟩ := by
    refine ⟨rfl,code,scope,?_,pushed_mapped .nil⟩
    simp only [isolate,control]
    exact .returned value
  simpa [attach,Stack.append] using GeneralRelated.evalSegment segment component (by simpa [framesOf] using frames)

def returnedState (base : CoreMachine.State) (value : CoreMachine.Value) (physical : List CoreMachine.Frame) : CoreMachine.State :=
  {base with control := .returned value,frames := physical}

def observedState (base : CoreMachine.State) (value : CoreMachine.Value) (physical : List CoreMachine.Frame)
    (observation : CoreMachine.Observation) : CoreMachine.State :=
  {base with control := .returned value,frames := physical,observations := base.observations ++ [observation]}

def startedState (base : CoreMachine.State) (action : Nat) (environment : CoreMachine.Environment)
    (identity : Nat) (saved : CoreMachine.Value) (physical : List CoreMachine.Frame) : CoreMachine.State :=
  {base with control := .evaluate action environment,frames := .cleanupCompletion identity saved :: physical, observations := base.observations ++ [.cleanupStarted identity]}

/-- Normal cleanup begins with any authenticated saved value and leaves every
outside obligation in place. -/
theorem normal_start {base : CoreMachine.State}
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (outside : GeneralSegment graph base.heap physical lexical) (scope : Scope) :
    GeneralStepWitness graph
      ⟨returnedState base savedValue (.cleanupBoundary action environment data.identity :: physical),
        .eval ⟨savedCode,scope,.push (.armed data) lexical⟩,callerOwners,[]⟩
      ⟨startedState base action environment data.identity savedValue physical,
        .eval ⟨.app data.action .unit,.none,.push (.running data savedCode saved.closed) lexical⟩,cleanupOwners,[]⟩ [] [] := by
  obtain ⟨callback,translated,closed⟩ := CoreNormalCleanupSteps.delayed_action delayed
  have component : ComponentMapped graph cleanupOwners []
      (isolate (startedState base action environment data.identity savedValue physical) []) ⟨.app data.action .unit,.none,.nil⟩ :=
    ⟨rfl,_,.none,.evaluate translated closed,pushed_mapped .nil⟩
  have ordinary : LexicalUnwind.ordinary savedCode := by
    cases savedCode <;> simp [LexicalUnwind.ordinary]
    simpa [Code.IsValue] using saved.closed.1
  refine ⟨returned_related (state := returnedState base savedValue (.cleanupBoundary action environment data.identity :: physical)) (.push (.cleanup delayed) outside) saved rfl rfl scope,rfl,
    .one (.evaluate (.startCleanup data savedCode saved.closed scope lexical) ordinary),?_⟩
  simpa [attach,Stack.append] using GeneralRelated.evalSegment (state := startedState base action environment data.identity savedValue physical)
    (GeneralSegment.append (.completion (.normal delayed saved)) outside) component (by simp [startedState,framesOf])

/-- Actual Unit completion restores the same saved value and scope ahead of
an arbitrary outside segment, including protected running or closing frames. -/
theorem normal_finish {base : CoreMachine.State}
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (outside : GeneralSegment graph base.heap physical lexical)
    (activeOwners : CoreTranslation.OwnerMap) (scope : Scope) :
    GeneralStepWitness graph
      ⟨returnedState base .unit (.cleanupCompletion data.identity savedValue :: physical),
        .eval ⟨.unit,scope,.push (.running data savedCode saved.closed) lexical⟩,activeOwners,[]⟩
      ⟨observedState base savedValue physical (.cleanupFinished data.identity),
        .eval ⟨savedCode,data.scope,lexical⟩,callerOwners,[]⟩ [] [.cleanup data.identity] := by
  refine ⟨?_,rfl,.one (.evaluate (.finishCleanup data savedCode saved.closed scope lexical) (by trivial)),?_⟩
  · exact returned_related (state := returnedState base .unit (.cleanupCompletion data.identity savedValue :: physical)) (by simpa [Stack.append,returnedState] using GeneralSegment.append (.completion (.normal delayed saved)) outside)
      (.unit (owners := activeOwners)) rfl rfl scope
  · exact returned_related (state := observedState base savedValue physical (.cleanupFinished data.identity)) outside saved rfl rfl data.scope

/-- Returning through a spent actual owner restores its authenticated handler
scope and preserves every outside carrier. -/
theorem leave_clause {base : CoreMachine.State}
    (header : CoreRequestFrames.OwnerHeader graph savedOwners base.heap handler owner occurrence data)
    (value : ValueRel graph currentOwners base.heap returned code)
    (outside : GeneralSegment graph base.heap physical lexical) (ticket : Nat) (scope : Scope) :
    GeneralStepWitness graph
      ⟨returnedState base returned (.clauseBoundary handler owner occurrence ticket none :: physical),
        .eval ⟨code,scope,.spent ticket data.answer data.scope lexical⟩,currentOwners,[]⟩
      ⟨observedState base returned physical (.clauseReturned ticket),.eval ⟨code,data.scope,lexical⟩,savedOwners,[]⟩ [] [] := by
  refine ⟨returned_related (state := returnedState base returned (.clauseBoundary handler owner occurrence ticket none :: physical)) (.spent header outside) value rfl rfl scope,rfl,?_,
    returned_related (state := observedState base returned physical (.clauseReturned ticket)) outside (value.owner_transport savedOwners) rfl rfl data.scope⟩
  exact ordinary_step (.leaveClause ticket data.answer code value.closed scope data.scope lexical)
    (by cases code <;> simp [LexicalUnwind.ordinary]; simpa [Code.IsValue] using value.closed.1)

/-- A resumed CLOSE obligation can finish in evaluation mode. Target and Core
close names remain distinct; the Core observation uses its physical label. -/
theorem close_value {base : CoreMachine.State}
    (outside : GeneralSegment graph base.heap physical lexical)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    GeneralStepWitness graph
      ⟨returnedState base .unit (.closeCompletion coreClose :: physical),
        .eval ⟨.unit,scope,.push (.closing targetClose callerScope) lexical⟩,owners,[]⟩
      ⟨observedState base .unit physical (.closeFinished coreClose),.eval ⟨.unit,callerScope,lexical⟩,owners,[]⟩ [] [.close targetClose] := by
  refine ⟨?_,rfl,.one (.closeValue (ValueRel.closed (.unit (graph := graph) (owners := owners) (heap := base.heap)))),?_⟩
  · exact returned_related (state := returnedState base .unit (.closeCompletion coreClose :: physical)) (by simpa [Stack.append,returnedState] using GeneralSegment.append (.completion (.closing coreClose targetClose callerScope)) outside)
      .unit rfl rfl scope
  · exact returned_related (state := observedState base .unit physical (.closeFinished coreClose)) outside .unit rfl rfl callerScope

/-- Resume and then finish the normal cleanup captured at the saved segment's
head. The very same arbitrary captured tail, caller and outside are used by
both redexes; no intermediate relation is supplied. -/
theorem resume_then_normal_finish {base : CoreMachine.State}
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (cut : GeneralOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data result
      (.cleanupCompletion actionData.identity savedValue :: capturedPhysical)
      (.push (.running actionData savedCode saved.closed) capturedTarget) outside outsideTarget)
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment actionData.identity) actionData)
    (capturedTail : GeneralSegment graph base.heap capturedPhysical capturedTarget)
    (frame : CoreResumeFrames.ResumeRel graph frameOwners base.heap (.resume handler owner) plain)
    (context : plain.context = .resume binder) (resolve : plain.scope.resolve binder = some ticket)
    (activeOwners : CoreTranslation.OwnerMap) (runtimeScope : Scope) :
    let resumed := resumeAfter base handler owner occurrence ticket .unit
      (.cleanupCompletion actionData.identity savedValue :: capturedPhysical) front outside
    let restPhysical := capturedPhysical ++ front ++ .clauseBoundary handler owner occurrence ticket none :: outside
    let restTarget := capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))
    GeneralChain graph
      ⟨resumeBefore base handler owner .unit whole,.eval ⟨.resume binder .unit,plain.scope,target⟩,activeOwners,[(frameOwners,.resume handler owner)]⟩
      [⟨resumed,.eval ⟨.unit,plain.scope,.push (.running actionData savedCode saved.closed) restTarget⟩,activeOwners,[]⟩,
       ⟨observedState resumed savedValue restPhysical (.cleanupFinished actionData.identity),.eval ⟨savedCode,actionData.scope,restTarget⟩,callerOwners,[]⟩]
      ⟨observedState resumed savedValue restPhysical (.cleanupFinished actionData.identity),.eval ⟨savedCode,actionData.scope,restTarget⟩,callerOwners,[]⟩
      [] [.cleanup actionData.identity,.ticket ticket] := by
  have resumedStep := resume_general cut frame context (.unit (owners := activeOwners)) resolve runtimeScope
  obtain ⟨found,shape,header,current,frontSegment,capturedSegment,outsideSegment⟩ := cut.realizes
  let resumed := resumeAfter base handler owner occurrence ticket .unit
    (.cleanupCompletion actionData.identity savedValue :: capturedPhysical) front outside
  have remaining := capturedTail.append (frontSegment.append (.spent (ticket := ticket) header outsideSegment))
  have finished := normal_finish (base := resumed) delayed saved remaining activeOwners plain.scope
  have finishedExact : GeneralStepWitness graph
      ⟨resumed,.eval ⟨.unit,plain.scope,.push (.running actionData savedCode saved.closed)
        (capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))⟩,activeOwners,[]⟩
      ⟨observedState resumed savedValue (capturedPhysical ++ front ++ .clauseBoundary handler owner occurrence ticket none :: outside)
        (.cleanupFinished actionData.identity),.eval ⟨savedCode,actionData.scope,
          capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩,callerOwners,[]⟩
      [] [.cleanup actionData.identity] := by
    simpa [resumed,resumeAfter,returnedState,observedState,List.append_assoc] using finished
  have chained := GeneralChain.next (GeneralLink.positive resumedStep) (GeneralChain.last (GeneralLink.positive finishedExact))
  simpa [resumed,resumeAfter,returnedState,observedState,Stack.append,List.append_assoc,stack_append_assoc] using chained

theorem observation_exact (base : CoreMachine.State) (value : CoreMachine.Value) (physical : List CoreMachine.Frame)
    (observation : CoreMachine.Observation) :
    (observedState base value physical observation).observations = base.observations ++ [observation] ∧
    (observedState base value physical observation).frames = physical ∧
    (observedState base value physical observation).heap = base.heap ∧
    (observedState base value physical observation).nextOwner = base.nextOwner ∧
    (observedState base value physical observation).nextClose = base.nextClose := ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms returned_related
#print axioms normal_start
#print axioms normal_finish
#print axioms leave_clause
#print axioms close_value
#print axioms resume_then_normal_finish
#print axioms observation_exact
end Ash.OneShot.CoreGeneralRestoration
