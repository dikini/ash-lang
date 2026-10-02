import CoreCallableStrictFocusConsumers
import GeneratedOutsideActivationOrigins
import CoreCallableOutsideOrigin
namespace Ash.OneShot.CoreCallableStrictCaptureOrigins
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableInitialChronology CoreCallableGeneralStrictFocus
open CoreCallableStrictFocusConsumers CoreCallableCleanupReachableTransport

/-- Structural membership retains each installation's original frame and metadata. -/
inductive OrdinaryMember (owners : OwnerMap) (frame : CoreMachine.Frame) (plain : PlainData) :
    {physical : List CoreMachine.Frame} → {target : Stack} → GeneralHistory graph heap physical target → Type where
  | here (related : PlainFrameRel graph owners heap frame plain) (ordinary)
      (tail : GeneralHistory graph heap below lexical) :
      OrdinaryMember owners frame plain (.push (.ordinary related) ordinary tail)
  | push (carrier : CoreCaptureEntry.PushCarrier graph otherOwners heap core targetFrame) (ordinary)
      (tail : GeneralHistory graph heap physical target) (member : OrdinaryMember owners frame plain tail) :
      OrdinaryMember owners frame plain (.push carrier ordinary tail)
  | handler (installation : GeneralHandlerPast graph otherOwners site environment data)
      (header : CoreEffectFrames.BoundaryRel graph otherOwners heap (.handlerBoundary site environment data.activation) (.handler data))
      (tail : GeneralHistory graph heap physical target) (member : OrdinaryMember owners frame plain tail) :
      OrdinaryMember owners frame plain (.handler installation header tail)
  | left (first : GeneralHistory graph heap firstPhysical firstTarget)
      (last : GeneralHistory graph heap lastPhysical lastTarget) (member : OrdinaryMember owners frame plain first) :
      OrdinaryMember owners frame plain (first.append last)
  | right (first : GeneralHistory graph heap firstPhysical firstTarget)
      (last : GeneralHistory graph heap lastPhysical lastTarget) (member : OrdinaryMember owners frame plain last) :
      OrdinaryMember owners frame plain (first.append last)

/-- The head is produced by actual entry. Only named history-preserving outputs
occur before capture; the original saved map/scope is never replaced. -/
inductive BeforeCapture (pastRun : Prefix graph original) (ready : EntryReady kind original) :
    Endpoint graph → Nat → Type where
  | entered : BeforeCapture pastRun ready (entry_after ready (pastRun.receipt ready)) 1
  | stable (earlier : BeforeCapture pastRun ready before count)
      (step : GeneratedOutsideActivationOrigins.StableOperation before after) :
      BeforeCapture pastRun ready after (count+1)

theorem BeforeCapture.heap {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : BeforeCapture pastRun ready current count) : current.state.heap = original.state.heap := by
  induction run with
  | entered => rfl
  | stable earlier step ih => exact step.same_heap.trans ih

theorem BeforeCapture.physical {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : BeforeCapture pastRun ready current count) :
    current.physical = kind.leftFrame ready.right ready.environment :: original.physical := by
  induction run with
  | entered => rfl
  | stable earlier step ih => cases step <;> exact ih

theorem BeforeCapture.lexical {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : BeforeCapture pastRun ready current count) : current.lexical = .push (.plain ready.plain) original.lexical := by
  induction run with
  | entered => rfl
  | stable earlier step ih => cases step <;> exact ih

theorem BeforeCapture.history {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : BeforeCapture pastRun ready current count) :
    HEq current.history (entry_after ready (pastRun.receipt ready)).history := by
  induction run with
  | entered => rfl
  | stable earlier step ih => exact step.same_history.trans ih

noncomputable def BeforeCapture.middle {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : BeforeCapture pastRun ready current count) : Middle pastRun ready current count [] [] := by
  induction run with
  | entered => exact .entered
  | stable earlier step ih => simpa using Middle.covered ih step.operation

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

/-- An actual head can be exposed through original append nodes without
asserting false equality between append and push history constructors. -/
inductive HeadMember (owners : OwnerMap) (frame : CoreMachine.Frame) (plain : PlainData) :
    {physical : List CoreMachine.Frame} → {target : Stack} → GeneralHistory graph heap physical target →
    {below : List CoreMachine.Frame} → {lexical : Stack} → GeneralHistory graph heap below lexical → Type where
  | here (related : PlainFrameRel graph owners heap frame plain) (ordinary)
      (tail : GeneralHistory graph heap below lexical) :
      HeadMember owners frame plain (.push (.ordinary related) ordinary tail) tail
  | append (first : GeneralHistory graph heap firstPhysical firstTarget)
      (last : GeneralHistory graph heap lastPhysical lastTarget)
      (below : GeneralHistory graph heap belowPhysical belowTarget)
      (member : HeadMember owners frame plain first below) :
      HeadMember owners frame plain (first.append last) (below.append last)

/-- Computed head membership in the actual selected captured segment. -/
structure HeadCut {graph : Graph} {heap : CoreMachine.Heap} (owners : OwnerMap)
    (frame : CoreMachine.Frame) (plain : PlainData)
    {physical : List CoreMachine.Frame} {target : Stack}
    (history : GeneralHistory graph heap physical target)
    (index : Fin (handler_locations history).length) where
  kept : List CoreMachine.Frame
  keptTarget : Stack
  keptHistory : GeneralHistory graph heap kept keptTarget
  related : PlainFrameRel graph owners heap frame plain
  captured : HeadMember owners frame plain
    (((handler_locations history)[index]).before.append
      (.handler ((handler_locations history)[index]).installation ((handler_locations history)[index]).header .nil))
    keptHistory
  physical : physical = frame :: (kept ++ ((handler_locations history)[index]).outside)
  lexical : target = .push (.plain plain) (keptTarget.append ((handler_locations history)[index]).tail)

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

noncomputable def dormant {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : BeforeCapture pastRun ready current count) (input : CaptureInput current) :
    HeadCut original.owners (kind.leftFrame ready.right ready.environment) ready.plain current.history input.index :=
  Classical.choice (head_cut_from_history (pastRun.receipt ready).saved.related
    (by cases kind <;> trivial) original.history current.history run.heap run.physical run.lexical run.history input.index)

theorem dormant_original_tail {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : BeforeCapture pastRun ready current count) (input : CaptureInput current) :
    original.physical = (dormant run input).kept ++ (location current input.index).outside := by
  have same := (dormant run input).physical
  exact (List.cons.inj (run.physical.symm.trans same)).2

noncomputable def HeadMember.membership {graph : Graph} {heap : CoreMachine.Heap}
    {physical below : List CoreMachine.Frame} {target lexical : Stack}
    {history : GeneralHistory graph heap physical target} {belowHistory : GeneralHistory graph heap below lexical}
    (member : HeadMember owners frame plain history belowHistory) : OrdinaryMember owners frame plain history := by
  induction member with
  | here related ordinary tail => exact .here related ordinary tail
  | append first last below member ih => exact .left first last ih

theorem HeadMember.physical {graph : Graph} {heap : CoreMachine.Heap}
    {physical below : List CoreMachine.Frame} {target lexical : Stack}
    {history : GeneralHistory graph heap physical target} {belowHistory : GeneralHistory graph heap below lexical}
    (member : HeadMember owners frame plain history belowHistory) :
    physical = frame :: below := by
  induction member with
  | here => rfl
  | append first last below member ih => rw [ih]; rfl

theorem HeadMember.lexical {graph : Graph} {heap : CoreMachine.Heap}
    {physical below : List CoreMachine.Frame} {target lexical : Stack}
    {history : GeneralHistory graph heap physical target} {belowHistory : GeneralHistory graph heap below lexical}
    (member : HeadMember owners frame plain history belowHistory) :
    target = .push (.plain plain) lexical := by
  induction member with
  | here => rfl
  | append first last below member ih => rw [ih]; rfl

/-- The same actual capture produces the live base; stable named operations
and actual handler installations construct its current ResumeSplit. -/
inductive AfterCapture {graph : Graph} {capturedFrom : Endpoint graph} (input : CaptureInput capturedFrom) : Endpoint graph → Nat → Type where
  | captured : AfterCapture input (capture_result input).after 1
  | stable (earlier : AfterCapture input before count)
      (step : GeneratedOutsideActivationOrigins.StableOperation before after) : AfterCapture input after (count+1)
  | handler (earlier : AfterCapture input before count) (installed : HandlerInput before) :
      AfterCapture input (handler_result installed).after (count+1)

noncomputable def AfterCapture.middle {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original} {input : CaptureInput capturedFrom}
    (run : AfterCapture input current count)
    (earlier : Middle pastRun ready capturedFrom earlierCount created discharged) :
    Middle pastRun ready current (earlierCount+count) (created++[.ticket capturedFrom.state.nextOwner]) discharged := by
  induction run with
  | captured => simpa using Middle.covered earlier (Operation.capture input)
  | stable previous step ih => simpa [Nat.add_assoc] using Middle.covered ih step.operation
  | handler previous installed ih => simpa [Nat.add_assoc] using Middle.covered ih (Operation.handler installed)

structure LiveCarrier {capturedFrom : Endpoint graph} (input : CaptureInput capturedFrom) (current : Endpoint graph) where
  front : List CoreMachine.Frame
  frontTarget : Stack
  frontHistory : GeneralHistory graph current.state.heap front frontTarget
  header : CoreRequestFrames.OwnerHeader graph (location capturedFrom input.index).owners current.state.heap
    (location capturedFrom input.index).installation.handler input.selectedClause.owner
    (location capturedFrom input.index).data.activation (location capturedFrom input.index).data
  savedHistory : GeneralHistory graph current.state.heap
    ((location capturedFrom input.index).inside ++ [.handlerBoundary (location capturedFrom input.index).site
      (location capturedFrom input.index).environment (location capturedFrom input.index).data.activation])
    ((location capturedFrom input.index).front.append (.push (.handler (location capturedFrom input.index).data) .nil))
  outsideHistory : GeneralHistory graph current.state.heap (location capturedFrom input.index).outside (location capturedFrom input.index).tail
  savedSame : HEq savedHistory ((location capturedFrom input.index).before.append
    (.handler (location capturedFrom input.index).installation (location capturedFrom input.index).header .nil))
  outsideSame : HEq outsideHistory (location capturedFrom input.index).after
  heapSame : current.state.heap = capturedFrom.state.heap
  pass : PassFront (location capturedFrom input.index).installation.handler input.selectedClause.owner frontHistory
  physical : current.physical = front ++ .clauseBoundary (location capturedFrom input.index).installation.handler
    input.selectedClause.owner (location capturedFrom input.index).data.activation capturedFrom.state.nextOwner
    (some ((location capturedFrom input.index).inside ++ [.handlerBoundary (location capturedFrom input.index).site
      (location capturedFrom input.index).environment (location capturedFrom input.index).data.activation])) ::
      (location capturedFrom input.index).outside
  lexical : current.lexical = frontTarget.append (.live capturedFrom.state.nextOwner input.result
    (location capturedFrom input.index).data.answer
    ((location capturedFrom input.index).front.append (.push (.handler (location capturedFrom input.index).data) .nil))
    (location capturedFrom input.index).data.scope (location capturedFrom input.index).tail)
  split : ResumeSplit (capture_data input).installation header savedHistory outsideHistory input.result current.history frontHistory

noncomputable def AfterCapture.carrier {capturedFrom current : Endpoint graph} {input : CaptureInput capturedFrom}
    (run : AfterCapture input current count) : LiveCarrier input current := by
  induction run with
  | captured => exact {
      front := [],frontTarget := .nil,frontHistory := .nil,header := (capture_data input).header
      savedHistory := (location capturedFrom input.index).before.append
        (.handler (location capturedFrom input.index).installation (location capturedFrom input.index).header .nil)
      outsideHistory := (location capturedFrom input.index).after,savedSame := HEq.rfl,outsideSame := HEq.rfl
      heapSame := rfl,pass := .nil,physical := rfl,lexical := rfl,split := .here }
  | stable earlier step ih =>
    cases step <;> exact {
      front := ih.front,frontTarget := ih.frontTarget,frontHistory := ih.frontHistory
      header := ih.header,savedHistory := ih.savedHistory,outsideHistory := ih.outsideHistory
      savedSame := ih.savedSame,outsideSame := ih.outsideSame,heapSame := ih.heapSame
      pass := ih.pass,physical := ih.physical,lexical := ih.lexical,split := ih.split }
  | @handler before count earlier installed ih =>
    let extension : HeapExtends installed.installation.predecessor.heap before.state.heap := by
      rw [installed.predecessor]; exact fun _ _ h => h
    let header := installed.installation.header.heap_weaken extension
    exact {
      front := .handlerBoundary installed.site installed.environment installed.data.activation :: ih.front
      frontTarget := .push (.handler installed.data) ih.frontTarget
      frontHistory := .handler installed.installation header ih.frontHistory
      header := ih.header,savedHistory := ih.savedHistory,outsideHistory := ih.outsideHistory
      savedSame := ih.savedSame,outsideSame := ih.outsideSame,heapSame := ih.heapSame
      pass := .handler installed.installation header ih.frontHistory ih.pass
      physical := congrArg (fun xs => CoreMachine.Frame.handlerBoundary installed.site installed.environment installed.data.activation :: xs) ih.physical
      lexical := congrArg (fun xs => Stack.push (.handler installed.data) xs) ih.lexical
      split := .handler installed.installation header _ _ ih.split }

/-- Current literal resume guards; selected metadata/cut/suffix/history are
constructed by AfterCapture.carrier rather than supplied independently. -/
structure ResumeReady {capturedFrom : Endpoint graph} (input : CaptureInput capturedFrom) (current : Endpoint graph) where
  frameOwners : OwnerMap
  plain : PlainData
  binder : Nat
  frame : CoreResumeFrames.ResumeRel graph frameOwners current.state.heap
    (.resume (location capturedFrom input.index).installation.handler input.selectedClause.owner) plain
  context : plain.context = .resume binder
  value : CoreMachine.Value
  code : Code
  operand : ValueRel graph current.owners current.state.heap value code
  resolve : plain.scope.resolve binder = some capturedFrom.state.nextOwner
  control : current.state.control = .returned value
  maps : current.maps = [(frameOwners,.resume (location capturedFrom input.index).installation.handler input.selectedClause.owner)]
  focus : current.focus = ⟨.resume binder code,plain.scope,.nil⟩

noncomputable def resume_input {capturedFrom current : Endpoint graph} {input : CaptureInput capturedFrom}
    (run : AfterCapture input current count) (ready : ResumeReady input current) : ResumeInput current := {
  handler := (location capturedFrom input.index).installation.handler,owner := input.selectedClause.owner
  occurrence := (location capturedFrom input.index).data.activation,dynamicTicket := capturedFrom.state.nextOwner
  savedOwners := (location capturedFrom input.index).owners,frameOwners := ready.frameOwners
  data := (location capturedFrom input.index).data,result := input.result
  captured := (location capturedFrom input.index).inside ++ [.handlerBoundary (location capturedFrom input.index).site
    (location capturedFrom input.index).environment (location capturedFrom input.index).data.activation]
  capturedTarget := (location capturedFrom input.index).front.append (.push (.handler (location capturedFrom input.index).data) .nil)
  installation := (capture_data input).installation,header := run.carrier.header,capturedHistory := run.carrier.savedHistory
  outside := (location capturedFrom input.index).outside,tail := (location capturedFrom input.index).tail
  outsideHistory := run.carrier.outsideHistory,front := run.carrier.front,frontTarget := run.carrier.frontTarget
  frontHistory := run.carrier.frontHistory,pass := run.carrier.pass,physical := run.carrier.physical
  lexical := run.carrier.lexical,split := run.carrier.split
  plain := ready.plain,binder := ready.binder,frame := ready.frame,context := ready.context
  value := ready.value,code := ready.code,operand := ready.operand,resolve := ready.resolve
  control := ready.control,maps := ready.maps,focus := ready.focus }

def historyPhysical {graph : Graph} {heap : CoreMachine.Heap} {physical : List CoreMachine.Frame} {target : Stack}
    (_history : GeneralHistory graph heap physical target) : List CoreMachine.Frame := physical

def historyTarget {graph : Graph} {heap : CoreMachine.Heap} {physical : List CoreMachine.Frame} {target : Stack}
    (_history : GeneralHistory graph heap physical target) : Stack := target

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

noncomputable def restored_tail {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (before : BeforeCapture pastRun ready capturedFrom beforeCount) (input : CaptureInput capturedFrom)
    (afterCapture : AfterCapture input current afterCount) :
    GeneralHistory graph current.state.heap
      ((dormant before input).kept ++ (afterCapture.carrier.front ++
        .clauseBoundary (location capturedFrom input.index).installation.handler input.selectedClause.owner
          (location capturedFrom input.index).data.activation capturedFrom.state.nextOwner none ::
          (location capturedFrom input.index).outside))
      ((dormant before input).keptTarget.append (afterCapture.carrier.frontTarget.append
        (.spent capturedFrom.state.nextOwner (location capturedFrom input.index).data.answer
          (location capturedFrom input.index).data.scope (location capturedFrom input.index).tail))) :=
  (heap_transport (dormant before input).keptHistory afterCapture.carrier.heapSame).append
    (afterCapture.carrier.frontHistory.append (.spent (capture_data input).installation
      afterCapture.carrier.header afterCapture.carrier.outsideHistory))

noncomputable def restored_member {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (before : BeforeCapture pastRun ready capturedFrom beforeCount) (input : CaptureInput capturedFrom)
    (afterCapture : AfterCapture input current afterCount) (resume : ResumeReady input current) :
    HeadMember original.owners (kind.leftFrame ready.right ready.environment) ready.plain
      (resume_result (resume_input afterCapture resume)).after.history (restored_tail before input afterCapture) := by
  have saved := member_transport (dormant before input).captured afterCapture.carrier.savedHistory
    afterCapture.carrier.heapSame afterCapture.carrier.savedSame
  exact .append _ _ _ saved

/-- A finite test on THIS original saved map/scope and computed kept prefix.
It accepts inactive scopes or a first static match retained inside that prefix. -/
def insideCheck (owners : OwnerMap) (scope : Execution.Scope) (kept : List CoreMachine.Frame) : Bool :=
  match scope,owners with
  | .none,_ => true
  | .ticket _ _,entry::_ => !CoreCallableOutsideOrigin.prefixMiss entry.handler entry.owner kept
  | .ticket _ _,[] => false

theorem scope_inside_computed
    (origin : CurrentScopeOrigin graph owners scope physical)
    (same : physical = kept ++ outside) (checked : insideCheck owners scope kept = true) :
    ScopeInside origin kept := by
  cases origin with
  | inactive canonical => exact .inactive canonical
  | @clause rest handler owner occurrence dynamicTicket saved originalPhysical front tail canonical path =>
    apply ScopeInside.clause canonical path
    by_cases inside : front.length < kept.length
    · exact inside
    have bound : kept.length ≤ front.length := Nat.le_of_not_gt inside
    obtain ⟨_,_,_,miss⟩ := CoreCallableOutsideOrigin.OwnerPath.drop_prefix path same bound
    simp [insideCheck,miss] at checked

theorem restored_scope {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (before : BeforeCapture pastRun ready capturedFrom beforeCount) (input : CaptureInput capturedFrom)
    (afterCapture : AfterCapture input current afterCount)
    (checked : insideCheck original.owners ready.plain.scope (dormant before input).kept = true) :
    CurrentScopeOrigin graph original.owners ready.plain.scope
      ((dormant before input).kept ++ (afterCapture.carrier.front ++
        .clauseBoundary (location capturedFrom input.index).installation.handler input.selectedClause.owner
          (location capturedFrom input.index).data.activation capturedFrom.state.nextOwner none ::
          (location capturedFrom input.index).outside)) :=
  CurrentScopeOrigin.restore_inside (pastRun.receipt ready).saved.origin
    (dormant_original_tail before input)
    (scope_inside_computed (pastRun.receipt ready).saved.origin (dormant_original_tail before input) checked) _

#print axioms BeforeCapture.heap
#print axioms BeforeCapture.physical
#print axioms BeforeCapture.lexical
#print axioms BeforeCapture.history
#print axioms BeforeCapture.middle
#print axioms dormant
#print axioms dormant_original_tail
#print axioms AfterCapture.middle
#print axioms AfterCapture.carrier
#print axioms HeadMember.membership
#print axioms resume_input
#print axioms restored_member
#print axioms scope_inside_computed
#print axioms restored_scope
end Ash.OneShot.CoreCallableStrictCaptureOrigins
