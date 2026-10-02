import CoreCallableStrictOutsideHeadOrigins
namespace Ash.OneShot.CoreCallableStrictOutsideHeadConsumers
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers
open CoreCallableStrictCaptureOrigins CoreCallableStrictOutsideHeadOrigins

/-- Full current return metadata remains explicit. Head/control/value/maps and
EmptyFocus are derived from the SAME actual resume output, not seeded anew. -/
structure ReturnedReady {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (before : BeforeCapture pastRun ready capturedFrom beforeCount) (input : CaptureInput capturedFrom)
    (afterCapture : AfterCapture input current afterCount) (resume : ResumeReady input current) where
  afterPlain : PlainData
  context : afterPlain.context = kind.rightContext resume.code
  sameScope : afterPlain.scope = ready.plain.scope
  notValue : ¬ ready.rightCode.IsValue
  unique : UniqueHandlerSites graph
  metadata : selectedCallerCheck original.owners ready.plain.scope
    (location capturedFrom input.index).owners (location capturedFrom input.index).data.scope = true
  position : callerOutsideCheck original.owners ready.plain.scope (dormant before input).kept = true

private theorem right_frame {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    {before : BeforeCapture pastRun ready capturedFrom beforeCount} {input : CaptureInput capturedFrom}
    {afterCapture : AfterCapture input current afterCount} {resume : ResumeReady input current}
    (returned : ReturnedReady before input afterCapture resume) :
    PlainFrameRel graph original.owners current.state.heap (kind.rightFrame resume.value) returned.afterPlain := by
  change FrameRel graph original.owners current.state.heap _ returned.afterPlain.context
  rw [returned.context]
  cases kind with
  | pair => exact .tupleRight (resume.operand.owner_transport original.owners)
  | application => exact .applyArgument (resume.operand.owner_transport original.owners)

noncomputable def right_after {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    {before : BeforeCapture pastRun ready capturedFrom beforeCount} {input : CaptureInput capturedFrom}
    {afterCapture : AfterCapture input current afterCount} {resume : ResumeReady input current}
    (returned : ReturnedReady before input afterCapture resume) : Endpoint graph := {
  state := {(resume_result (resume_input afterCapture resume)).after.state with
    control := .evaluate ready.right ready.environment
    frames := kind.rightFrame resume.value :: (historyPhysical (restored_tail before input afterCapture))}
  focus := ⟨ready.rightCode,returned.afterPlain.scope,.nil⟩
  owners := original.owners,maps := []
  physical := kind.rightFrame resume.value :: (historyPhysical (restored_tail before input afterCapture))
  lexical := .push (.plain returned.afterPlain) (historyTarget (restored_tail before input afterCapture))
  history := .push (.ordinary (right_frame returned)) (by cases kind <;> trivial) (restored_tail before input afterCapture)
  frames := rfl }

theorem right_actual {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    {before : BeforeCapture pastRun ready capturedFrom beforeCount} {input : CaptureInput capturedFrom}
    {afterCapture : AfterCapture input current afterCount} {resume : ResumeReady input current}
    (returned : ReturnedReady before input afterCapture resume) :
    CoreMachine.next graph (resume_result (resume_input afterCapture resume)).after.state = .stepped (right_after returned).state := by
  have head := (restored_member before input afterCapture resume).physical
  have frames : (resume_result (resume_input afterCapture resume)).after.state.frames =
      kind.leftFrame ready.right ready.environment :: (historyPhysical (restored_tail before input afterCapture)) := by
    simpa [resume_result,CoreGeneralCaptureResume.resumeAfter,historyPhysical] using head
  have control : (resume_result (resume_input afterCapture resume)).after.state.control = .returned resume.value := rfl
  have same : {(resume_result (resume_input afterCapture resume)).after.state with
      control := .returned resume.value
      frames := kind.leftFrame ready.right ready.environment :: historyPhysical (restored_tail before input afterCapture)} =
      (resume_result (resume_input afterCapture resume)).after.state := by rw [← control,← frames]
  have actual : CoreMachine.next graph {(resume_result (resume_input afterCapture resume)).after.state with
      control := .returned resume.value
      frames := kind.leftFrame ready.right ready.environment :: historyPhysical (restored_tail before input afterCapture)} =
      .stepped {(resume_result (resume_input afterCapture resume)).after.state with
        control := .evaluate ready.right ready.environment
        frames := kind.rightFrame resume.value :: historyPhysical (restored_tail before input afterCapture)} := by
    cases kind <;> rfl
  simpa only [same,right_after] using actual

theorem right_raw {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    {before : BeforeCapture pastRun ready capturedFrom beforeCount} {input : CaptureInput capturedFrom}
    {afterCapture : AfterCapture input current afterCount} {resume : ResumeReady input current}
    (returned : ReturnedReady before input afterCapture resume) :
    RawStep ⟨resume.code,resume.plain.scope,.push (.plain ready.plain) (historyTarget (restored_tail before input afterCapture))⟩
      ⟨kind.code resume.code ready.rightCode,ready.plain.scope,(historyTarget (restored_tail before input afterCapture))⟩ [] [] ∧
    RawStep ⟨kind.code resume.code ready.rightCode,ready.plain.scope,(historyTarget (restored_tail before input afterCapture))⟩
      ⟨ready.rightCode,returned.afterPlain.scope,.push (.plain returned.afterPlain) (historyTarget (restored_tail before input afterCapture))⟩ [] [] := by
  have plug := RawStep.plug ready.plain resume.code resume.operand.closed resume.plain.scope (historyTarget (restored_tail before input afterCapture))
  cases kind with
  | pair =>
    refine ⟨by simpa only [ready.context,PairApplication.leftContext,PairApplication.code,Context.plug] using plug,?_⟩
    rw [← returned.sameScope]
    exact .focus returned.afterPlain (by rw [returned.context]; exact .pairRight resume.operand.closed.1 returned.notValue) _
  | application =>
    have extension : HeapExtends original.state.heap current.state.heap := by
      rw [afterCapture.carrier.heapSame,before.heap]; exact fun _ _ h => h
    have actual := application_return_function ready.rightTranslated
      ((pastRun.receipt ready).rightClosing.heap_weaken extension)
      (resume.operand.owner_transport original.owners) returned.notValue ready.plain returned.afterPlain
      ready.context returned.context returned.sameScope resume.plain.scope
      (historyPhysical (restored_tail before input afterCapture)) (historyTarget (restored_tail before input afterCapture))
    exact ⟨actual.2.1,actual.2.2.1⟩

theorem right_positive {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    {before : BeforeCapture pastRun ready capturedFrom beforeCount} {input : CaptureInput capturedFrom}
    {afterCapture : AfterCapture input current afterCount} {resume : ResumeReady input current}
    (returned : ReturnedReady before input afterCapture resume) :
    CoreUnwindRelation.Positive (resume_result (resume_input afterCapture resume)).after.point.machine (right_after returned).point.machine [] [] := by
  have head := (restored_member before input afterCapture resume).lexical
  have beforePoint : (resume_result (resume_input afterCapture resume)).after.point.machine =
      .eval ⟨resume.code,resume.plain.scope,.push (.plain ready.plain) (historyTarget (restored_tail before input afterCapture))⟩ := by
    simpa only [Endpoint.point,resume_result,resume_input,CoreCleanupRunFrames.attach,Stack.append,historyTarget] using
      congrArg (fun xs => LexicalUnwind.Machine.eval ⟨resume.code,resume.plain.scope,xs⟩) head
  rw [beforePoint]
  change CoreUnwindRelation.Positive _ (.eval ⟨ready.rightCode,returned.afterPlain.scope,.push (.plain returned.afterPlain) (historyTarget (restored_tail before input afterCapture))⟩) [] []
  have allowed : LexicalUnwind.ordinary resume.code := CoreUnwindRelation.raw_without_close_ordinary (right_raw returned).1 (by simp)
  exact .next (.evaluate (right_raw returned).1 allowed) (.one (.evaluate (right_raw returned).2 (by cases kind <;> trivial)))

theorem right_sites {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    {before : BeforeCapture pastRun ready capturedFrom beforeCount} {input : CaptureInput capturedFrom}
    {afterCapture : AfterCapture input current afterCount} {resume : ResumeReady input current}
    (returned : ReturnedReady before input afterCapture resume) : SiteOrigins (right_after returned) := by
  refine ⟨CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical (pastRun.receipt ready).saved.origin,?_,?_,?_⟩
  · simp [MapsCanonical,right_after]
  · simpa only [EvaluatingSite,right_after,returned.sameScope] using (pastRun.receipt ready).rightSite
  · simp [SavedRightSites,right_after]

theorem right_scopes {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    {before : BeforeCapture pastRun ready capturedFrom beforeCount} {input : CaptureInput capturedFrom}
    {afterCapture : AfterCapture input current afterCount} {resume : ResumeReady input current}
    (returned : ReturnedReady before input afterCapture resume) : EvaluatedScopeOrigins (right_after returned) := by
  refine ⟨?_,?_⟩
  · have saved := (outside_restored_scope before input afterCapture returned.unique returned.metadata returned.position).prepend_plain (right_frame returned)
    simpa only [EvaluatingScopeOrigin,right_after,returned.sameScope,historyPhysical] using saved
  · simp [SavedMapScopeOrigins,right_after]

theorem complete_episode {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    {before : BeforeCapture pastRun ready capturedFrom beforeCount} {input : CaptureInput capturedFrom}
    {afterCapture : AfterCapture input current afterCount} {resume : ResumeReady input current}
    (returned : ReturnedReady before input afterCapture resume) :
    CoreAllocationHistory.Steps graph (beforeCount+afterCount+2) original.state (right_after returned).state ∧
    CoreUnwindRelation.Trace original.point.machine (right_after returned).point.machine
      [.ticket capturedFrom.state.nextOwner] [.ticket capturedFrom.state.nextOwner] := by
  have captured := afterCapture.middle before.middle
  have resumed := Middle.covered captured (Operation.resume (resume_input afterCapture resume))
  refine ⟨by simpa [Nat.add_assoc] using CoreAllocationHistory.Steps.snoc resumed.core (right_actual returned),?_⟩
  simpa [resume_input,resume_location] using resumed.trace.append (right_positive returned).trace

private theorem steps_append {before middle after : CoreMachine.State}
    (first : CoreAllocationHistory.Steps graph left before middle)
    (second : CoreAllocationHistory.Steps graph right middle after) :
    CoreAllocationHistory.Steps graph (left+right) before after := by
  induction second with
  | refl => simpa using first
  | snoc earlier step ih => simpa [Nat.add_assoc] using CoreAllocationHistory.Steps.snoc (ih first) step

theorem complete_original_prefix {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    {before : BeforeCapture pastRun ready capturedFrom beforeCount} {input : CaptureInput capturedFrom}
    {afterCapture : AfterCapture input current afterCount} {resume : ResumeReady input current}
    (returned : ReturnedReady before input afterCapture resume) :
    CoreAllocationHistory.Steps graph (pastRun.info.1+(beforeCount+afterCount+2)) pastRun.base.state (right_after returned).state ∧
    CoreUnwindRelation.Trace pastRun.base.point.machine (right_after returned).point.machine
      (pastRun.info.2.1++[.ticket capturedFrom.state.nextOwner]) ([.ticket capturedFrom.state.nextOwner]++pastRun.info.2.2) :=
  ⟨steps_append pastRun.core (complete_episode returned).1,pastRun.trace.append (complete_episode returned).2⟩

#print axioms right_actual
#print axioms right_raw
#print axioms right_positive
#print axioms right_sites
#print axioms right_scopes
#print axioms complete_episode
#print axioms complete_original_prefix
end Ash.OneShot.CoreCallableStrictOutsideHeadConsumers
