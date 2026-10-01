import CoreGeneralCaptureResume

/-! Handler definitions inspected during ordinary resume come from the same
related saved segment. This discharges a structural preparation obligation of
the experimental Core model. Allocator, storage, work and disposal success, and
the general Rust-to-model bridge, remain separate obligations. -/
namespace Ash.OneShot.CoreResumeReadiness
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames
  CoreStrictStack CoreEffectFrames CoreRequestFrames CoreResumeFrames
  CoreCleanupFrames CoreCaptureEntry CoreCleanupProjection CoreCleanupRunFrames
  CoreGeneralStack CoreGeneralCaptureResume

def HandlerReady (graph : CoreSyntax.Graph) : CoreMachine.Frame → Prop
  | .handlerBoundary site _ _ =>
      ∃ node handler effect body clauses,
        graph.node site = some node ∧ node.kind = .handler handler effect body clauses
  | _ => True

def HandlersReady (graph : CoreSyntax.Graph) (frames : List CoreMachine.Frame) : Prop :=
  ∀ frame ∈ frames, HandlerReady graph frame

theorem PushCarrier.handler_ready (frame : PushCarrier graph owners heap core target) :
    HandlerReady graph core := by
  cases frame with
  | ordinary frame =>
      rename_i plain
      change FrameRel graph owners heap core plain.context at frame
      generalize contextEq : plain.context = annotated at frame
      cases frame <;> trivial
  | initializer frame => cases frame; trivial
  | request frame => cases frame; trivial
  | resume frame => cases frame; trivial
  | cleanup frame => cases frame; trivial
  | boundary frame =>
      cases frame with
      | handler known kind translated header => exact ⟨_, _, _, _, _, known, kind⟩
      | cell known kind => trivial

theorem HandlersReady.append (first : HandlersReady graph before) (second : HandlersReady graph after) :
    HandlersReady graph (before ++ after) := by
  intro frame member
  rcases List.mem_append.mp member with member | member
  · exact first frame member
  · exact second frame member

theorem PushedWithMaps.handlers_ready (stack : PushedWithMaps graph heap maps target) :
    HandlersReady graph (framesOf maps) := by
  induction stack with
  | nil => intro frame member; cases member
  | cons frame tail ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · exact PushCarrier.handler_ready (.ordinary frame)
      · exact ih candidate member
  | initializer frame tail ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · exact PushCarrier.handler_ready (.initializer frame)
      · exact ih candidate member
  | request frame tail ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · exact PushCarrier.handler_ready (.request frame)
      · exact ih candidate member
  | resume frame tail ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · exact PushCarrier.handler_ready (.resume frame)
      · exact ih candidate member
  | cleanup frame tail ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · exact PushCarrier.handler_ready (.cleanup frame)
      · exact ih candidate member
  | boundary frame tail ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · exact PushCarrier.handler_ready (.boundary frame)
      · exact ih candidate member
  | live header saved outside ihSaved ihOutside =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact ihOutside candidate member
  | spent header outside ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact ih candidate member

theorem RetainedCursor.handlers_ready (cursor : RetainedCursor graph heap physical lexical) :
    HandlersReady graph physical := by
  induction cursor with
  | nil => intro frame member; cases member
  | plain frame next ih | handler frame next ih | spent header next ih | retiring header next ih => exact ih
  | cell frame next ih | armed frame next ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact ih candidate member
  | live header saved outside ihSaved ihOutside => exact ihSaved.append ihOutside

theorem GeneralSegment.handlers_ready (segment : GeneralSegment graph heap physical lexical) :
    HandlersReady graph physical := by
  induction segment with
  | ordinary stack => exact PushedWithMaps.handlers_ready stack
  | retained cursor => exact RetainedCursor.handlers_ready cursor
  | push frame tail ih =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · exact PushCarrier.handler_ready frame
      · exact ih candidate member
  | completion atom =>
      cases atom <;> intro candidate member <;> simp only [List.mem_singleton] at member <;> subst candidate <;> trivial
  | live header saved outside ihSaved ihOutside | spent header outside ihOutside =>
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact ihOutside candidate member
  | append first second ihFirst ihSecond => exact ihFirst.append ihSecond

/-- Actual owner lookup determines the saved segment whose handler definitions
ordinary resume inspects. The current source relation supplies their readiness;
no independently chosen ready saved segment or future configuration is used. -/
theorem resume_ready_from_lookup {base : CoreMachine.State}
    (segment : GeneralSegment graph base.heap whole target)
    (found : CoreMachine.findOwner handler owner whole = .ok ⟨front,handler,owner,occurrence,ticket,captured,outside⟩)
    (frame : ResumeRel graph frameOwners base.heap (.resume handler owner) plain)
    (context : plain.context = .resume binder)
    (value : ValueRel graph owners base.heap coreValue code)
    (resolve : plain.scope.resolve binder = some ticket) (runtimeScope : Scope) :
    HandlersReady graph captured ∧
    ∃ frontTarget savedOwners data result capturedTarget outsideTarget,
      GeneralOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget ∧
      GeneralStepWitness graph
        ⟨resumeBefore base handler owner coreValue whole,.eval ⟨.resume binder code,plain.scope,target⟩,
          owners,[(frameOwners,.resume handler owner)]⟩
        ⟨resumeAfter base handler owner occurrence ticket coreValue captured front outside,
          .eval ⟨code,plain.scope,capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩,
          owners,[]⟩ [] [.ticket ticket] := by
  obtain ⟨frontTarget,savedOwners,data,result,capturedTarget,outsideTarget,cut,step⟩ :=
    resume_from_lookup segment found frame context value resolve runtimeScope
  have saved := cut.realizes.2.2.2.2.2.1
  exact ⟨GeneralSegment.handlers_ready saved, frontTarget, savedOwners, data, result, capturedTarget, outsideTarget, cut, step⟩

#print axioms PushCarrier.handler_ready
#print axioms HandlersReady.append
#print axioms PushedWithMaps.handlers_ready
#print axioms RetainedCursor.handlers_ready
#print axioms GeneralSegment.handlers_ready
#print axioms resume_ready_from_lookup
end Ash.OneShot.CoreResumeReadiness
