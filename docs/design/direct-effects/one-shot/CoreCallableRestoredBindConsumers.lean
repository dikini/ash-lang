import CoreCallableRestoredBindOrigins
namespace Ash.OneShot.CoreCallableRestoredBindConsumers
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableCallerBarriers
open CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers CoreCallableStrictCaptureOrigins
open CoreCallableStrictCallerHeadCompatibility CoreCallableStrictOutsideHeadOrigins CoreCallableCleanupReachableTransport

open CoreCallableRestoredBindOrigins CoreCallableRestoredTupleDischarge
section Return
variable {graph : Graph} {bindBefore : Endpoint graph} (binding : BindInput bindBefore)
variable (ready : EntryReady .pair (bind_result binding).after)
variable (pastRun : Prefix graph (bind_result binding).after)
variable {captured : Endpoint graph}
variable (before : BeforeCapture pastRun ready captured count) (input : CaptureInput captured)

variable {current : Endpoint graph} (after : AfterCapture input current afterCount)
variable (resume : ResumeReady input current)
variable (installed : CoreCallableStrictCallerHeadConsumers.ReturnedReady before input after resume)
variable {secondCaptured secondCurrent : Endpoint graph}
variable (secondBefore : CoreCallableRestoredTupleHeads.RightBefore installed secondCaptured secondCount)
variable (secondInput : CaptureInput secondCaptured)
variable (secondAfter : AfterCapture secondInput secondCurrent secondAfterCount)
variable (secondResume : ResumeReady secondInput secondCurrent)

include ready pastRun before after resume installed secondBefore secondAfter in
theorem bind_heap_extension : HeapExtends binding.past.predecessor.heap (tuple_after installed secondBefore secondInput secondAfter secondResume).state.heap := by
  have same : secondCurrent.state.heap = binding.past.predecessor.heap := by
    exact secondAfter.carrier.heapSame.trans ((CoreCallableRestoredTupleHeads.RightBefore.heap installed secondBefore).trans
      (after.carrier.heapSame.trans ((BeforeCapture.heap before).trans (by simpa only [bind_result] using congrArg CoreMachine.State.heap binding.predecessor.symm))))
  have extension := tuple_heap_extension installed secondBefore secondInput secondAfter secondResume
  rw [same] at extension
  exact extension

noncomputable def bind_after : Endpoint graph := {
  state := {(tuple_after installed secondBefore secondInput secondAfter secondResume).state with control := .evaluate binding.body (.binding binding.binder.id (CoreMachine.Value.location secondCurrent.state.heap.length) binding.environment),frames := (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).physical}
  focus := ⟨binding.past.suffixCode.subst binding.binder.id (Code.pair resume.code secondResume.code),binding.plain.scope,.nil⟩
  owners := binding.owners,maps := [],physical := (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).physical,lexical := (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).target
  history := (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).history,frames := rfl }

include ready pastRun before after resume installed secondBefore secondAfter in
theorem bind_actual : CoreMachine.next graph (tuple_after installed secondBefore secondInput secondAfter secondResume).state =
    .stepped (bind_after binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).state := by
  obtain ⟨fuel,rawBody,translated,closing,closed⟩ := binding.past.saved.saved.bind_static binding.past.context
  have produced := (CoreStrictSteps.bind_complete (base := (tuple_after installed secondBefore secondInput secondAfter secondResume).state) translated
    (closing.heap_weaken (bind_heap_extension binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume))
    (tuple_value installed secondBefore secondInput secondAfter secondResume) closed (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).physical binding.plain.scope (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).target).1
  have physical := (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).member.physical
  have frames : (tuple_after installed secondBefore secondInput secondAfter secondResume).state.frames = .bind binding.binder.id binding.body binding.environment :: (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).physical := physical
  have same : {(tuple_after installed secondBefore secondInput secondAfter secondResume).state with
      control := .returned (CoreMachine.Value.location secondCurrent.state.heap.length)
      frames := .bind binding.binder.id binding.body binding.environment :: (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).physical} = (tuple_after installed secondBefore secondInput secondAfter secondResume).state := by
    rw [← frames]
    rfl
  rw [same] at produced
  exact produced

include ready pastRun before after resume installed secondBefore secondAfter in
theorem bind_raw :
    RawStep ⟨(Code.pair resume.code secondResume.code),installed.afterPlain.scope,.push (.plain binding.plain) (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).target⟩
      ⟨.bind binding.binder.id (Code.pair resume.code secondResume.code) binding.past.suffixCode,binding.plain.scope,(discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).target⟩ [] [] ∧
    RawStep ⟨.bind binding.binder.id (Code.pair resume.code secondResume.code) binding.past.suffixCode,binding.plain.scope,(discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).target⟩
      ⟨binding.past.suffixCode.subst binding.binder.id (Code.pair resume.code secondResume.code),binding.plain.scope,(discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).target⟩ [] [] := by
  obtain ⟨fuel,rawBody,translated,closing,closed⟩ := binding.past.saved.saved.bind_static binding.past.context
  refine ⟨?_,RawStep.bind _ _ _ _ _ (tuple_value installed secondBefore secondInput secondAfter secondResume).closed closed⟩
  simpa only [binding.past.context,Context.plug] using RawStep.plug binding.plain (Code.pair resume.code secondResume.code)
    (tuple_value installed secondBefore secondInput secondAfter secondResume).closed installed.afterPlain.scope (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).target

include ready pastRun before after resume installed secondBefore secondAfter in
theorem bind_positive : CoreUnwindRelation.Positive (tuple_after installed secondBefore secondInput secondAfter secondResume).point.machine
    (bind_after binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).point.machine [] [] := by
  have head := (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).member.lexical
  have point : (tuple_after installed secondBefore secondInput secondAfter secondResume).point.machine =
      .eval ⟨(Code.pair resume.code secondResume.code),installed.afterPlain.scope,.push (.plain binding.plain) (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).target⟩ := by
    simp only [tuple_after,Endpoint.point,CoreCleanupRunFrames.attach,Stack.append]
    exact congrArg (fun xs => LexicalUnwind.Machine.eval ⟨(Code.pair resume.code secondResume.code),installed.afterPlain.scope,xs⟩) head
  rw [point]
  exact .next (.evaluate (bind_raw binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).1
    (CoreUnwindRelation.raw_without_close_ordinary (bind_raw binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).1 (by simp)))
    (.one (.evaluate (bind_raw binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).2 (by trivial)))

include ready pastRun before after resume installed secondBefore secondAfter in
theorem bind_closing : ∃ fuel rawBody,
    CoreTranslation.translateFuel graph fuel binding.owners binding.body = .ok rawBody ∧
    EnvCloses graph binding.owners (bind_after binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).state.heap
      (.binding binding.binder.id (.location secondCurrent.state.heap.length) binding.environment)
      rawBody (binding.past.suffixCode.subst binding.binder.id (.pair resume.code secondResume.code)) := by
  obtain ⟨fuel,rawBody,translated,closing,closed⟩ := binding.past.saved.saved.bind_static binding.past.context
  exact ⟨fuel,rawBody,translated,
    (closing.heap_weaken (bind_heap_extension binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume)).beta_argument
      (tuple_value installed secondBefore secondInput secondAfter secondResume)⟩

include ready pastRun before after resume installed secondBefore secondAfter in
theorem bind_site : SiteLineage graph (bind_after binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).owners (bind_after binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).focus.scope binding.body := binding.past.saved.site

include ready pastRun before after resume installed secondBefore secondAfter in
theorem bind_scope
    (firstChecked : BindScopeReady graph binding.owners binding.plain.scope
      (first_kept_bind binding ready pastRun before input).physical
      (location captured input.index).owners (location captured input.index).data.scope)
    (secondChecked : BindScopeReady graph binding.owners binding.plain.scope
      (second_kept_bind binding ready pastRun before input after resume installed secondBefore secondInput).physical
      (location secondCaptured secondInput.index).owners (location secondCaptured secondInput.index).data.scope) :
    CurrentScopeOrigin graph (bind_after binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).owners (bind_after binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).focus.scope (bind_after binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).physical :=
  discharged_bind_scope binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume firstChecked secondChecked

noncomputable def bind_result : Result (tuple_after installed secondBefore secondInput secondAfter secondResume) [] [] :=
  ⟨bind_after binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume,bind_actual binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume,.positive (bind_positive binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume)⟩


end Return
#print axioms bind_heap_extension
#print axioms bind_after
#print axioms bind_actual
#print axioms bind_raw
#print axioms bind_positive
#print axioms bind_closing
#print axioms bind_site
#print axioms bind_scope
#print axioms bind_result
end Ash.OneShot.CoreCallableRestoredBindConsumers
