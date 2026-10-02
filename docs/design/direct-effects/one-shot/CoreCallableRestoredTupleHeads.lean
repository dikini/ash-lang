import CoreCallableStrictCallerHeadConsumers
namespace Ash.OneShot.CoreCallableRestoredTupleHeads
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers
open CoreCallableStrictCaptureOrigins CoreCallableStrictOutsideHeadOrigins CoreCallableStrictCallerHeadCompatibility
open CoreCallableCleanupReachableTransport

private theorem pushed_location {graph : Graph} {heap : CoreMachine.Heap}
    (related : PlainFrameRel graph owners heap frame plain) (ordinary)
    (tail : GeneralHistory graph heap physical target)
    (index : Fin (handler_locations (.push (.ordinary related) ordinary tail)).length) :
    ∃ lower ∈ handler_locations tail,
      (handler_locations (.push (.ordinary related) ordinary tail))[index] =
        lower.prepend (.push (.ordinary related) ordinary .nil) := by
  have member := List.getElem_mem index.isLt
  simp only [handler_locations] at member
  obtain ⟨lower,present,same⟩ := List.mem_map.mp member
  exact ⟨lower,present,same.symm⟩

private theorem head_cut_produced {graph : Graph} {heap : CoreMachine.Heap}
    (related : PlainFrameRel graph owners heap frame plain) (ordinary)
    (tail : GeneralHistory graph heap physical target)
    (index : Fin (handler_locations (.push (.ordinary related) ordinary tail)).length) :
    Nonempty (HeadCut owners frame plain (.push (.ordinary related) ordinary tail) index) := by
  obtain ⟨lower,_,same⟩ := pushed_location related ordinary tail index
  refine ⟨⟨lower.inside ++ [.handlerBoundary lower.site lower.environment lower.data.activation],
    lower.front.append (.push (.handler lower.data) .nil),
    (GeneralHistory.nil.append lower.before).append (.handler lower.installation lower.header .nil),related,?_,?_,?_⟩⟩
  · rw [same]
    exact .append _ _ _ (.append _ _ _ (.here related ordinary .nil))
  · rw [same]
    simpa [HandlerLocation.prepend,List.append_assoc] using congrArg (fun xs => frame :: xs) lower.physicalSame
  · rw [same]
    simpa [HandlerLocation.prepend,stack_append_assoc,Stack.append] using
      congrArg (fun xs => Stack.push (.plain plain) xs) lower.targetSame

private theorem head_cut_from_history {graph : Graph} {heap originalHeap : CoreMachine.Heap}
    {owners : OwnerMap} {frame : CoreMachine.Frame} {plain : PlainData}
    {physical originalPhysical : List CoreMachine.Frame} {target originalTarget : Stack}
    (related : PlainFrameRel graph owners originalHeap frame plain) (ordinary)
    (tail : GeneralHistory graph originalHeap originalPhysical originalTarget)
    (history : GeneralHistory graph heap physical target)
    (heapSame : heap = originalHeap)
    (physicalSame : physical = frame :: originalPhysical)
    (targetSame : target = .push (.plain plain) originalTarget)
    (same : HEq history (GeneralHistory.push (.ordinary related) ordinary tail))
    (index : Fin (handler_locations history).length) : Nonempty (HeadCut owners frame plain history index) := by
  cases heapSame
  cases physicalSame
  cases targetSame
  have sameEq := eq_of_heq same
  cases sameEq
  exact head_cut_produced related ordinary tail index

private noncomputable def heap_transport {graph : Graph} {oldHeap nextHeap : CoreMachine.Heap}
    (history : GeneralHistory graph oldHeap physical target) (same : nextHeap = oldHeap) :
    GeneralHistory graph nextHeap physical target := by cases same; exact history

private noncomputable def member_transport {graph : Graph} {oldHeap nextHeap : CoreMachine.Heap}
    {oldHistory : GeneralHistory graph oldHeap physical target}
    {belowHistory : GeneralHistory graph oldHeap below lexical}
    (member : HeadMember owners frame plain oldHistory belowHistory)
    (nextHistory : GeneralHistory graph nextHeap physical target)
    (heapSame : nextHeap = oldHeap) (historySame : HEq nextHistory oldHistory) :
    HeadMember owners frame plain nextHistory (heap_transport belowHistory heapSame) := by
  cases heapSame
  have same := eq_of_heq historySame
  cases same
  exact member

/-- A finite inventory record retains the full original installation, rather
than identifying a handler by its physical site alone. Current before/after
histories remain attached to the actual HandlerLocation. -/
structure HandlerMark (graph : Graph) (heap : CoreMachine.Heap) where
  owners : OwnerMap
  site : Nat
  environment : Environment
  data : HandlerData
  installation : GeneralHandlerPast graph owners site environment data
  inside : List CoreMachine.Frame
  front : Stack
  outside : List CoreMachine.Frame
  tail : Stack

def handlerMark (candidate : HandlerLocation graph heap physical target) : HandlerMark graph heap :=
  ⟨candidate.owners,candidate.site,candidate.environment,candidate.data,candidate.installation,candidate.inside,candidate.front,candidate.outside,candidate.tail⟩

theorem HandlerMark.same_installation (left right : HandlerMark graph heap) (same : left = right) :
    HEq left.installation right.installation := by cases same; rfl

def HandlerMark.head (mark : HandlerMark graph heap) (frame : CoreMachine.Frame) (plain : PlainData) : HandlerMark graph heap :=
  {mark with inside := frame::mark.inside,front := .push (.plain plain) mark.front}

def HandlerMark.suffix (mark : HandlerMark graph heap) (physical : List CoreMachine.Frame) (target : Stack) : HandlerMark graph heap :=
  {mark with outside := mark.outside++physical,tail := mark.tail.append target}

def HandlerMark.leading (mark : HandlerMark graph heap) (physical : List CoreMachine.Frame) (target : Stack) : HandlerMark graph heap :=
  {mark with inside := physical++mark.inside,front := target.append mark.front}

private theorem marks_append (first : GeneralHistory graph heap firstPhysical firstTarget)
    (last : GeneralHistory graph heap lastPhysical lastTarget) :
    (handler_locations (first.append last)).map handlerMark =
      ((handler_locations first).map handlerMark).map (fun mark => mark.suffix lastPhysical lastTarget) ++
      ((handler_locations last).map handlerMark).map (fun mark => mark.leading firstPhysical firstTarget) := by
  simp only [handler_locations,List.map_append,List.map_map,Function.comp_def]
  rfl

def HandlerMark.unhead (mark : HandlerMark graph heap) : HandlerMark graph heap :=
  {mark with inside := mark.inside.tail,front := match mark.front with | .push _ tail => tail | other => other}

theorem HandlerMark.unhead_head (mark : HandlerMark graph heap) (frame : CoreMachine.Frame) (plain : PlainData) :
    (mark.head frame plain).unhead = mark := rfl

/-- Removing an actual ordinary head preserves the full handler installation
inventory and its structural inside/outside positions. -/
theorem HeadMember.handler_marks {graph : Graph} {heap : CoreMachine.Heap}
    {physical below : List CoreMachine.Frame} {target lexical : Stack}
    {history : GeneralHistory graph heap physical target} {belowHistory : GeneralHistory graph heap below lexical}
    (member : HeadMember owners frame plain history belowHistory) :
    (handler_locations history).map handlerMark =
      ((handler_locations belowHistory).map handlerMark).map (fun mark => mark.head frame plain) := by
  induction member with
  | here related ordinary tail =>
    simp only [handler_locations,List.map_map,HandlerLocation.prepend,Stack.append]
    rfl
  | @append firstPhysical firstTarget lastPhysical lastTarget belowPhysical belowTarget first last below member ih =>
    have physical := member.physical
    have lexical := member.lexical
    rw [marks_append,marks_append,ih]
    simp only [List.map_append,List.map_map,Function.comp_def,physical,lexical,
      HandlerMark.suffix,HandlerMark.head,HandlerMark.leading,List.cons_append,Stack.append]

theorem HeadMember.below_handler_marks {graph : Graph} {heap : CoreMachine.Heap}
    {physical below : List CoreMachine.Frame} {target lexical : Stack}
    {history : GeneralHistory graph heap physical target} {belowHistory : GeneralHistory graph heap below lexical}
    (member : HeadMember owners frame plain history belowHistory) :
    (handler_locations belowHistory).map handlerMark =
      ((handler_locations history).map handlerMark).map HandlerMark.unhead := by
  rw [HeadMember.handler_marks member,List.map_map]
  simp only [Function.comp_def,HandlerMark.unhead_head]
  exact (List.map_id _).symm


section Installation
variable {graph : Graph} {original firstCaptured firstCurrent : Endpoint graph}
variable {pastRun : Prefix graph original} {ready : EntryReady .pair original}
variable {firstBefore : BeforeCapture pastRun ready firstCaptured firstBeforeCount}
variable {firstInput : CaptureInput firstCaptured} {firstAfter : AfterCapture firstInput firstCurrent firstAfterCount}
variable {firstResume : ResumeReady firstInput firstCurrent}
variable (installed : CoreCallableStrictCallerHeadConsumers.ReturnedReady firstBefore firstInput firstAfter firstResume)

/-- The tuple-right frame is constructed by the SAME first right transition. -/
theorem installed_related : PlainFrameRel graph original.owners firstCurrent.state.heap
    (.tupleRight firstResume.value) installed.afterPlain := by
  change FrameRel graph original.owners firstCurrent.state.heap _ installed.afterPlain.context
  rw [installed.context]
  exact .tupleRight (firstResume.operand.owner_transport original.owners)

theorem installed_origin : CurrentScopeOrigin graph original.owners installed.afterPlain.scope
    (historyPhysical (CoreCallableStrictCaptureOrigins.restored_tail firstBefore firstInput firstAfter)) := by
  rw [installed.sameScope]
  exact CoreCallableStrictCallerHeadCompatibility.outside_restored_scope firstBefore firstInput firstAfter
    installed.unique installed.metadata installed.position

/-- Finite named outputs retain THIS computed right installation. -/
inductive RightBefore : Endpoint graph → Nat → Type where
  | installed : RightBefore (CoreCallableStrictCallerHeadConsumers.right_after installed) 0
  | stable (earlier : RightBefore before count)
      (step : GeneratedOutsideActivationOrigins.StableOperation before after) : RightBefore after (count+1)

theorem RightBefore.heap (run : RightBefore installed current count) : current.state.heap = firstCurrent.state.heap := by
  induction run with
  | installed => rfl
  | stable earlier step ih => exact step.same_heap.trans ih

theorem RightBefore.physical (run : RightBefore installed current count) :
    current.physical = .tupleRight firstResume.value ::
      historyPhysical (CoreCallableStrictCaptureOrigins.restored_tail firstBefore firstInput firstAfter) := by
  induction run with
  | installed => rfl
  | stable earlier step ih => cases step <;> exact ih

theorem RightBefore.lexical (run : RightBefore installed current count) :
    current.lexical = .push (.plain installed.afterPlain)
      (historyTarget (CoreCallableStrictCaptureOrigins.restored_tail firstBefore firstInput firstAfter)) := by
  induction run with
  | installed => rfl
  | stable earlier step ih => cases step <;> exact ih

theorem RightBefore.history (run : RightBefore installed current count) :
    HEq current.history (CoreCallableStrictCallerHeadConsumers.right_after installed).history := by
  induction run with
  | installed => rfl
  | stable earlier step ih => exact step.same_history.trans ih

theorem RightBefore.core (run : RightBefore installed current count) :
    CoreAllocationHistory.Steps graph count (CoreCallableStrictCallerHeadConsumers.right_after installed).state current.state := by
  induction run with
  | installed => exact .refl _
  | stable earlier step ih => exact .snoc ih step.operation.actual.1

theorem RightBefore.trace (run : RightBefore installed current count) :
    CoreUnwindRelation.Trace (CoreCallableStrictCallerHeadConsumers.right_after installed).point.machine current.point.machine [] [] := by
  induction run with
  | installed => exact .refl _
  | stable earlier step ih => simpa using ih.append step.operation.actual.2.target_trace

/-- Full selected captured prefix and original physical outside are retained. -/
noncomputable def dormant (run : RightBefore installed current count) (input : CaptureInput current) :
    HeadCut original.owners (.tupleRight firstResume.value) installed.afterPlain current.history input.index :=
  Classical.choice (head_cut_from_history (installed_related installed) (by trivial)
    (CoreCallableStrictCaptureOrigins.restored_tail firstBefore firstInput firstAfter) current.history
    run.heap run.physical run.lexical run.history input.index)

theorem dormant_original_tail (run : RightBefore installed current count) (input : CaptureInput current) :
    historyPhysical (CoreCallableStrictCaptureOrigins.restored_tail firstBefore firstInput firstAfter) =
      (dormant installed run input).kept ++ (location current input.index).outside :=
  (List.cons.inj (run.physical.symm.trans (dormant installed run input).physical)).2

noncomputable def restored_tail (before : RightBefore installed capturedFrom count) (input : CaptureInput capturedFrom)
    (after : AfterCapture input current afterCount) :
    GeneralHistory graph current.state.heap
      ((dormant installed before input).kept ++ (after.carrier.front ++
        .clauseBoundary (location capturedFrom input.index).installation.handler input.selectedClause.owner
          (location capturedFrom input.index).data.activation capturedFrom.state.nextOwner none ::
          (location capturedFrom input.index).outside))
      ((dormant installed before input).keptTarget.append (after.carrier.frontTarget.append
        (.spent capturedFrom.state.nextOwner (location capturedFrom input.index).data.answer
          (location capturedFrom input.index).data.scope (location capturedFrom input.index).tail))) :=
  (heap_transport (dormant installed before input).keptHistory after.carrier.heapSame).append
    (after.carrier.frontHistory.append (.spent (capture_data input).installation after.carrier.header after.carrier.outsideHistory))

noncomputable def restored_member (before : RightBefore installed capturedFrom count) (input : CaptureInput capturedFrom)
    (after : AfterCapture input current afterCount) (resume : ResumeReady input current) :
    HeadMember original.owners (.tupleRight firstResume.value) installed.afterPlain
      (resume_result (resume_input after resume)).after.history (restored_tail installed before input after) := by
  have saved := member_transport (dormant installed before input).captured after.carrier.savedHistory
    after.carrier.heapSame after.carrier.savedSame
  exact .append _ _ _ saved

/-- Only original cut classification and selected saved-head metadata are checked. -/
inductive ScopeReady (before : RightBefore installed capturedFrom count) (input : CaptureInput capturedFrom) : Type where
  | inside (checked : insideCheck original.owners installed.afterPlain.scope (dormant installed before input).kept = true)
  | outside (unique : UniqueHandlerSites graph)
      (metadata : savedCallerHeadCheck original.owners installed.afterPlain.scope
        (location capturedFrom input.index).owners (location capturedFrom input.index).data.scope = true)
      (position : callerOutsideCheck original.owners installed.afterPlain.scope (dormant installed before input).kept = true)

theorem restored_scope (before : RightBefore installed capturedFrom count) (input : CaptureInput capturedFrom)
    (after : AfterCapture input current afterCount) (scopeReady : ScopeReady installed before input) :
    CurrentScopeOrigin graph original.owners installed.afterPlain.scope
      (historyPhysical (restored_tail installed before input after)) := by
  cases scopeReady with
  | inside checked =>
    exact CoreCallableCleanupReachableTransport.CurrentScopeOrigin.restore_inside (installed_origin installed)
      (dormant_original_tail installed before input)
      (scope_inside_computed (installed_origin installed) (dormant_original_tail installed before input) checked) _
  | outside unique metadata position =>
      simpa only [List.append_assoc,List.singleton_append,historyPhysical] using
        original_scope_restored (installed_origin installed) (dormant_original_tail installed before input)
          position (capture_data input).installation unique metadata (AfterCapture.caller_front_pass after _ _)

end Installation
#print axioms HeadMember.handler_marks
#print axioms HeadMember.below_handler_marks
#print axioms installed_related
#print axioms installed_origin
#print axioms RightBefore.heap
#print axioms RightBefore.physical
#print axioms RightBefore.history
#print axioms RightBefore.core
#print axioms RightBefore.trace
#print axioms dormant
#print axioms dormant_original_tail
#print axioms restored_member
#print axioms restored_scope
end Ash.OneShot.CoreCallableRestoredTupleHeads
