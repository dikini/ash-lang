import CoreGeneralRestoration
import CoreProjectedCleanupSteps

/-! Residual closing work preserves an arbitrary outside GeneralSegment.
Finite lexical advances are the existing normalization of the same consumed
cursor; actual Core release/start/completion steps determine observations.
Physical and target close labels remain separate local witnesses. -/
namespace Ash.OneShot.CoreGeneralUnwind
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreEffectFrames
  CoreCleanupFrames CoreCleanupRunFrames CoreCleanupProjection CoreUnwindRelation
  CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
set_option linter.unusedSimpArgs false

/-- The exact same positive segment supplies transition and accounting. -/
theorem prepend_positive (trace : Trace before middle created discharged)
    (last : Positive middle after laterCreated laterDischarged) :
    Positive before after (created ++ laterCreated) (laterDischarged ++ discharged) := by
  induction trace with
  | refl => simpa using last
  | next step rest ih => simpa [List.append_assoc] using Positive.next step (ih last)

def closingState (base : CoreMachine.State) (physical outside : List CoreMachine.Frame) (coreClose : Nat) : CoreMachine.State :=
  {base with control := .returned .unit,frames := physical ++ .closeCompletion coreClose :: outside}

def closingPoint (base : CoreMachine.State) (physical outside : List CoreMachine.Frame) (lexical tail : Stack)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) : Point :=
  ⟨closingState base physical outside coreClose,.unwind scope (lexical.append (.push (.closing targetClose callerScope) tail)),owners,[]⟩

/-- The current physical resource determines its release, preceded only by the
existing finite lexical cursor normalization. -/
theorem resource_pop {base : CoreMachine.State}
    (cursor : RetainedCursor graph base.heap (.resourceBoundary site key payload :: physical) lexical)
    (outside : GeneralSegment graph base.heap outsidePhysical outsideTarget)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    ∃ remaining discharged, RetainedCursor graph base.heap physical remaining ∧
      GeneralStepWitness graph
        (closingPoint base (.resourceBoundary site key payload :: physical) outsidePhysical lexical outsideTarget coreClose targetClose scope callerScope owners)
        (closingPoint (CoreResourceUnwind.releasedBase base key) physical outsidePhysical remaining outsideTarget coreClose targetClose scope callerScope owners)
        [] discharged := by
  obtain ⟨normalized,prior,current,head,trace⟩ :=
    CoreProjectedCleanupSteps.normalize cursor scope (.push (.closing targetClose callerScope) outsideTarget)
  cases head with
  | cell frame next =>
      rename_i savedOwners savedScope answer remaining
      have positive : Positive
          (.unwind scope (lexical.append (.push (.closing targetClose callerScope) outsideTarget)))
          (.unwind scope (remaining.append (.push (.closing targetClose callerScope) outsideTarget))) [] ([.resource key] ++ prior) := by
        simpa [Stack.append] using prepend_positive trace (.one (.advance .cell))
      refine ⟨remaining,[Owner.resource key] ++ prior,next,?_,rfl,by simpa [closingPoint] using positive,?_⟩
      · exact .unwindSegment (state := closingState base (.resourceBoundary site key payload :: physical) outsidePhysical coreClose) cursor outside rfl rfl
      · exact .unwindSegment (state := closingState (CoreResourceUnwind.releasedBase base key) physical outsidePhysical coreClose) next outside rfl rfl

/-- Cleanup selection and callback interpretation are derived from this same
retained cursor. Outside protected completions are preserved intact. -/
theorem cleanup_start {base : CoreMachine.State}
    (cursor : RetainedCursor graph base.heap (.cleanupBoundary action environment identity :: physical) lexical)
    (outside : GeneralSegment graph base.heap outsidePhysical outsideTarget)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    ∃ cleanupOwners data remaining discharged,
      data.identity = identity ∧ CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data ∧
      RetainedCursor graph base.heap physical remaining ∧
      GeneralStepWitness graph
        (closingPoint base (.cleanupBoundary action environment identity :: physical) outsidePhysical lexical outsideTarget coreClose targetClose scope callerScope owners)
        ⟨startedState base action environment data.identity .unit (physical ++ .closeCompletion coreClose :: outsidePhysical),
          .eval ⟨.app data.action .unit,.none,.push (.unwinding data) (remaining.append (.push (.closing targetClose callerScope) outsideTarget))⟩,cleanupOwners,[]⟩
        [] discharged := by
  obtain ⟨cleanupOwners,data,remaining,discharged,identityEq,delayed,residual,selection⟩ :=
    CoreProjectedCleanupSteps.select_cleanup cursor scope (.push (.closing targetClose callerScope) outsideTarget)
  obtain ⟨callback,translated,closed⟩ := CoreNormalCleanupSteps.delayed_action delayed
  let after := startedState base action environment data.identity .unit (physical ++ .closeCompletion coreClose :: outsidePhysical)
  have component : ComponentMapped graph cleanupOwners [] (isolate after []) ⟨.app data.action .unit,.none,.nil⟩ :=
    ⟨rfl,_,.none,.evaluate translated closed,pushed_mapped .nil⟩
  refine ⟨cleanupOwners,data,remaining,discharged,identityEq,delayed,residual,?_,?_,?_,?_⟩
  · exact .unwindSegment (state := closingState base (.cleanupBoundary action environment identity :: physical) outsidePhysical coreClose) cursor outside rfl rfl
  · simp [closingPoint,closingState,startedState,CoreMachine.next,identityEq]
  · simpa [closingPoint] using prepend_positive selection (.one LexicalUnwind.Transition.startCleanup)
  · have segment : GeneralSegment graph base.heap after.frames
        (.push (.unwinding data) (remaining.append (.push (.closing targetClose callerScope) outsideTarget))) := by
      simpa [after,startedState,Stack.append,List.append_assoc] using
        GeneralSegment.append (.completion (.unwinding delayed))
          (.append (.retained residual) (.append (.completion (.closing coreClose targetClose callerScope)) outside))
    simpa [after,attach,Stack.append] using GeneralRelated.evalSegment (state := after) segment component (by simp [framesOf])

/-- Actual Unit completion returns to unwinding the same residual and outside.
This is a current redex, not a callback termination premise. -/
theorem cleanup_finish {base : CoreMachine.State}
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data)
    (cursor : RetainedCursor graph base.heap physical lexical)
    (outside : GeneralSegment graph base.heap outsidePhysical outsideTarget)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    GeneralStepWitness graph
      ⟨returnedState base .unit (.cleanupCompletion data.identity .unit :: physical ++ .closeCompletion coreClose :: outsidePhysical),
        .eval ⟨.unit,scope,.push (.unwinding data) (lexical.append (.push (.closing targetClose callerScope) outsideTarget))⟩,owners,[]⟩
      (closingPoint (observedState base .unit [] (.cleanupFinished data.identity)) physical outsidePhysical lexical outsideTarget coreClose targetClose data.scope callerScope owners)
      [] [.cleanup data.identity] := by
  refine ⟨?_,rfl,.one LexicalUnwind.Transition.finishCleanup,?_⟩
  · exact returned_related (state := returnedState base .unit (.cleanupCompletion data.identity .unit :: physical ++ .closeCompletion coreClose :: outsidePhysical))
      (by simpa [returnedState,Stack.append,List.append_assoc] using (GeneralSegment.append (.completion (.unwinding delayed))
        (.append (.retained cursor) (.append (.completion (.closing coreClose targetClose callerScope)) outside)))) .unit rfl rfl scope
  · exact .unwindSegment (state := closingState (observedState base .unit [] (.cleanupFinished data.identity)) physical outsidePhysical coreClose) cursor outside rfl rfl

/-- The same empty physical cursor derives every remaining ghost advance and
retirement before actual CLOSE completion. -/
theorem finish_close {base : CoreMachine.State}
    (cursor : RetainedCursor graph base.heap [] lexical)
    (outside : GeneralSegment graph base.heap outsidePhysical outsideTarget)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    ∃ prior, GeneralStepWitness graph
      (closingPoint base [] outsidePhysical lexical outsideTarget coreClose targetClose scope callerScope owners)
      ⟨observedState base .unit outsidePhysical (.closeFinished coreClose),.eval ⟨.unit,callerScope,outsideTarget⟩,owners,[]⟩
      [] ([.close targetClose] ++ prior) := by
  obtain ⟨normalized,prior,current,head,trace⟩ :=
    CoreProjectedCleanupSteps.normalize cursor scope (.push (.closing targetClose callerScope) outsideTarget)
  cases head with
  | nil =>
      refine ⟨prior,?_,rfl,?_,returned_related (state := observedState base .unit outsidePhysical (.closeFinished coreClose)) outside .unit rfl rfl callerScope⟩
      · exact .unwindSegment (state := closingState base [] outsidePhysical coreClose) cursor outside rfl rfl
      · simpa [closingPoint,Stack.append] using prepend_positive trace (.one LexicalUnwind.Transition.finishClose)

/-- Current unwinding cleanup completion connects to CLOSE completion through
this same empty physical cursor, including all retained ghost retirement. -/
theorem cleanup_finish_then_close {base : CoreMachine.State}
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data)
    (cursor : RetainedCursor graph base.heap [] lexical)
    (outside : GeneralSegment graph base.heap outsidePhysical outsideTarget)
    (coreClose targetClose : Nat) (scope callerScope : Scope) (owners : CoreTranslation.OwnerMap) :
    ∃ prior,
      let completed := observedState base .unit [] (.cleanupFinished data.identity)
      let after := observedState completed .unit outsidePhysical (.closeFinished coreClose)
      GeneralChain graph
        ⟨returnedState base .unit (.cleanupCompletion data.identity .unit :: .closeCompletion coreClose :: outsidePhysical),
          .eval ⟨.unit,scope,.push (.unwinding data) (lexical.append (.push (.closing targetClose callerScope) outsideTarget))⟩,owners,[]⟩
        [closingPoint completed [] outsidePhysical lexical outsideTarget coreClose targetClose data.scope callerScope owners,
         ⟨after,.eval ⟨.unit,callerScope,outsideTarget⟩,owners,[]⟩]
        ⟨after,.eval ⟨.unit,callerScope,outsideTarget⟩,owners,[]⟩ [] ([.close targetClose] ++ prior ++ [.cleanup data.identity]) := by
  have first := cleanup_finish delayed cursor outside coreClose targetClose scope callerScope owners
  let completed := observedState base .unit [] (.cleanupFinished data.identity)
  obtain ⟨prior,last⟩ := finish_close (base := completed) cursor outside coreClose targetClose data.scope callerScope owners
  exact ⟨prior,GeneralChain.next (GeneralLink.positive first) (GeneralChain.last (GeneralLink.positive last))⟩

theorem cleanup_close_observations (base : CoreMachine.State) (identity coreClose : Nat) (outside : List CoreMachine.Frame) :
    (observedState (observedState base .unit [] (.cleanupFinished identity)) .unit outside (.closeFinished coreClose)).observations =
      base.observations ++ [.cleanupFinished identity,.closeFinished coreClose] := by simp [observedState,List.append_assoc]

theorem closing_frames_exact (base : CoreMachine.State) (physical outside : List CoreMachine.Frame) (coreClose : Nat) :
    (closingState base physical outside coreClose).frames = physical ++ .closeCompletion coreClose :: outside ∧
    (closingState base physical outside coreClose).observations = base.observations ∧
    (closingState base physical outside coreClose).heap = base.heap := ⟨rfl,rfl,rfl⟩

#print axioms prepend_positive
#print axioms resource_pop
#print axioms cleanup_start
#print axioms cleanup_finish
#print axioms finish_close
#print axioms cleanup_finish_then_close
#print axioms cleanup_close_observations
#print axioms closing_frames_exact
end Ash.OneShot.CoreGeneralUnwind
