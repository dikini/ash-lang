import CoreCallableRestoredTupleHeads
namespace Ash.OneShot.CoreCallableRestoredTupleDischarge
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers
open CoreCallableStrictCaptureOrigins CoreCallableStrictCallerHeadCompatibility
open CoreCallableRestoredTupleHeads
section Discharge
variable {graph : Graph} {original firstCaptured firstCurrent : Endpoint graph}
variable {pastRun : Prefix graph original} {ready : EntryReady .pair original}
variable {firstBefore : BeforeCapture pastRun ready firstCaptured firstBeforeCount}
variable {firstInput : CaptureInput firstCaptured} {firstAfter : AfterCapture firstInput firstCurrent firstAfterCount}
variable {firstResume : ResumeReady firstInput firstCurrent}
variable (installed : CoreCallableStrictCallerHeadConsumers.ReturnedReady firstBefore firstInput firstAfter firstResume)
variable {capturedFrom current : Endpoint graph}
variable (before : RightBefore installed capturedFrom count) (input : CaptureInput capturedFrom)
variable (after : AfterCapture input current afterCount) (resume : ResumeReady input current)

noncomputable def tuple_after : Endpoint graph := {
  state := {(resume_result (resume_input after resume)).after.state with
    control := .returned (.location current.state.heap.length)
    frames := historyPhysical (CoreCallableRestoredTupleHeads.restored_tail installed before input after)
    heap := current.state.heap ++ [.pair firstResume.value resume.value]}
  focus := ⟨.pair firstResume.code resume.code,installed.afterPlain.scope,.nil⟩
  owners := original.owners,maps := []
  physical := historyPhysical (CoreCallableRestoredTupleHeads.restored_tail installed before input after)
  lexical := historyTarget (CoreCallableRestoredTupleHeads.restored_tail installed before input after)
  history := (CoreCallableRestoredTupleHeads.restored_tail installed before input after).heap_weaken
    (CoreValueRelation.heap_append current.state.heap [.pair firstResume.value resume.value])
  frames := rfl }

theorem tuple_actual : CoreMachine.next graph (resume_result (resume_input after resume)).after.state =
    .stepped (tuple_after installed before input after resume).state := by
  have head := (CoreCallableRestoredTupleHeads.restored_member installed before input after resume).physical
  have frames : (resume_result (resume_input after resume)).after.state.frames =
      .tupleRight firstResume.value :: historyPhysical (CoreCallableRestoredTupleHeads.restored_tail installed before input after) := by
    simpa only [resume_result,CoreGeneralCaptureResume.resumeAfter,historyPhysical,List.append_assoc] using head
  have same : {(resume_result (resume_input after resume)).after.state with
      control := .returned resume.value
      frames := .tupleRight firstResume.value :: historyPhysical (CoreCallableRestoredTupleHeads.restored_tail installed before input after)} =
      (resume_result (resume_input after resume)).after.state := by
    have control : (resume_result (resume_input after resume)).after.state.control = .returned resume.value := rfl
    rw [← control,← frames]
  have left : ValueRel graph original.owners current.state.heap firstResume.value firstResume.code := by
    rw [(AfterCapture.carrier after).heapSame.trans (RightBefore.heap installed before)]
    exact firstResume.operand.owner_transport original.owners
  have produced := (CoreAdministrativeSteps.tuple_allocate (base := (resume_result (resume_input after resume)).after.state)
    left (resume.operand.owner_transport original.owners)
    (historyPhysical (CoreCallableRestoredTupleHeads.restored_tail installed before input after))).1
  rw [same] at produced
  exact produced.core

private theorem before_point : (resume_result (resume_input after resume)).after.point.machine =
    .eval ⟨resume.code,resume.plain.scope,.push (.plain installed.afterPlain)
      (historyTarget (CoreCallableRestoredTupleHeads.restored_tail installed before input after))⟩ := by
  have head := (CoreCallableRestoredTupleHeads.restored_member installed before input after resume).lexical
  simpa only [Endpoint.point,resume_result,resume_input,CoreCleanupRunFrames.attach,Stack.append,historyTarget] using
    congrArg (fun xs => LexicalUnwind.Machine.eval ⟨resume.code,resume.plain.scope,xs⟩) head

theorem tuple_raw : RawStep
    ⟨resume.code,resume.plain.scope,.push (.plain installed.afterPlain)
      (historyTarget (CoreCallableRestoredTupleHeads.restored_tail installed before input after))⟩
    ⟨.pair firstResume.code resume.code,installed.afterPlain.scope,
      (historyTarget (CoreCallableRestoredTupleHeads.restored_tail installed before input after))⟩ [] [] := by
  simpa only [installed.context,PairApplication.rightContext,Context.plug] using
    RawStep.plug installed.afterPlain resume.code resume.operand.closed resume.plain.scope
      (historyTarget (CoreCallableRestoredTupleHeads.restored_tail installed before input after))

theorem tuple_positive : CoreUnwindRelation.Positive (resume_result (resume_input after resume)).after.point.machine
    (tuple_after installed before input after resume).point.machine [] [] := by
  rw [before_point installed before input after resume]
  exact .one (.evaluate (tuple_raw installed before input after resume)
    (CoreUnwindRelation.raw_without_close_ordinary (tuple_raw installed before input after resume) (by simp)))

theorem tuple_value : ValueRel graph original.owners (tuple_after installed before input after resume).state.heap
    (.location current.state.heap.length) (.pair firstResume.code resume.code) := by
  have atNew : (current.state.heap ++ [.pair firstResume.value resume.value])[current.state.heap.length]? =
      some (.pair firstResume.value resume.value) := by simp
  have left : ValueRel graph original.owners current.state.heap firstResume.value firstResume.code := by
    rw [(AfterCapture.carrier after).heapSame.trans (RightBefore.heap installed before)]
    exact firstResume.operand.owner_transport original.owners
  exact .location atNew (left.heap_weaken (CoreValueRelation.heap_append _ _))
    ((resume.operand.owner_transport original.owners).heap_weaken (CoreValueRelation.heap_append _ _))

theorem tuple_heap_extension : HeapExtends current.state.heap (tuple_after installed before input after resume).state.heap :=
  CoreValueRelation.heap_append _ _

theorem tuple_scope (scopeReady : ScopeReady installed before input) :
    CurrentScopeOrigin graph (tuple_after installed before input after resume).owners
      (tuple_after installed before input after resume).focus.scope (tuple_after installed before input after resume).physical :=
  CoreCallableRestoredTupleHeads.restored_scope installed before input after scopeReady

theorem tuple_exact_tail : (tuple_after installed before input after resume).physical =
    (dormant installed before input).kept ++ (after.carrier.front ++
      .clauseBoundary (location capturedFrom input.index).installation.handler input.selectedClause.owner
        (location capturedFrom input.index).data.activation capturedFrom.state.nextOwner none ::
        (location capturedFrom input.index).outside) := rfl

theorem tuple_accounting : ((resume_result (resume_input after resume)).after.point.machine.stack.erase.owners ++ []).Perm
    ((tuple_after installed before input after resume).point.machine.stack.erase.owners ++ []) :=
  CoreGeneralCaptureResume.positive_accounting (tuple_positive installed before input after resume)

end Discharge
#print axioms tuple_actual
#print axioms tuple_raw
#print axioms tuple_positive
#print axioms tuple_value
#print axioms tuple_heap_extension
#print axioms tuple_scope
#print axioms tuple_exact_tail
#print axioms tuple_accounting
end Ash.OneShot.CoreCallableRestoredTupleDischarge
