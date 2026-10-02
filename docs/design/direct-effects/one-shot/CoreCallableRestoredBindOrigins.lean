import CoreCallableRestoredTupleDischarge
import CoreCallableGeneratedBindConsumers
namespace Ash.OneShot.CoreCallableRestoredBindOrigins
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableCallerBarriers
open CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers CoreCallableStrictCaptureOrigins
open CoreCallableStrictCallerHeadCompatibility CoreCallableStrictOutsideHeadOrigins CoreCallableCleanupReachableTransport

/-- Structural ordinary head, preserving actual append and empty leading receipts. -/
inductive BindHead (owners : OwnerMap) (frame : CoreMachine.Frame) (plain : PlainData) :
    {physical : List CoreMachine.Frame} → {target : Stack} → GeneralHistory graph heap physical target →
    {below : List CoreMachine.Frame} → {lexical : Stack} → GeneralHistory graph heap below lexical → Type where
  | here (related : PlainFrameRel graph owners heap frame plain) (ordinary)
      (tail : GeneralHistory graph heap below lexical) : BindHead owners frame plain (.push (.ordinary related) ordinary tail) tail
  | append (first : GeneralHistory graph heap firstPhysical firstTarget) (last : GeneralHistory graph heap lastPhysical lastTarget)
      (below : GeneralHistory graph heap belowPhysical belowTarget) (member : BindHead owners frame plain first below) :
      BindHead owners frame plain (first.append last) (below.append last)
  | emptyPrefix (leading : GeneralHistory graph heap [] .nil)
      (member : BindHead owners frame plain history below) : BindHead owners frame plain (leading.append history) (leading.append below)

theorem BindHead.physical (member : BindHead owners frame plain history below) :
    historyPhysical history = frame :: historyPhysical below := by
  induction member with
  | here => rfl
  | append first last below member ih =>
    change historyPhysical first ++ historyPhysical last = frame :: (historyPhysical below ++ historyPhysical last)
    rw [ih]
    rfl
  | emptyPrefix leading member ih => exact ih

theorem BindHead.lexical (member : BindHead owners frame plain history below) :
    historyTarget history = .push (.plain plain) (historyTarget below) := by
  induction member with
  | here => rfl
  | append first last below member ih =>
    change (historyTarget first).append (historyTarget last) = .push (.plain plain) ((historyTarget below).append (historyTarget last))
    rw [ih]
    rfl
  | emptyPrefix leading member ih => exact ih

/-- Original adjacent ordinary heads, not an assertion about a desired future history. -/
inductive SecondHead (owners : OwnerMap) (frame : CoreMachine.Frame) (plain : PlainData) :
    {physical : List CoreMachine.Frame} → {target : Stack} → GeneralHistory graph heap physical target → Type where
  | direct (related : PlainFrameRel graph firstOwners heap firstFrame firstPlain) (ordinary)
      (member : BindHead owners frame plain history below) : SecondHead owners frame plain (.push (.ordinary related) ordinary history)
  | append (first : GeneralHistory graph heap firstPhysical firstTarget) (last : GeneralHistory graph heap lastPhysical lastTarget)
      (member : SecondHead owners frame plain first) : SecondHead owners frame plain (first.append last)
  | crossed (first : GeneralHistory graph heap [firstFrame] (.push (.plain firstPlain) .nil))
      (last : GeneralHistory graph heap lastPhysical lastTarget) (member : BindHead owners frame plain last below) :
      SecondHead owners frame plain (first.append last)

/-- Full saved metadata at an ordinary lexical position. Non-ordinary receipts
are not reconstructed from erased physical frames. -/
structure OrdinaryMetadata where
  owners : OwnerMap
  frame : CoreMachine.Frame
  plain : PlainData

def stackLength : Stack → Nat
  | .nil => 0
  | .push _ tail => stackLength tail + 1
  | .live _ _ _ _ _ tail => stackLength tail + 1
  | .spent _ _ _ tail => stackLength tail + 1

theorem stackLength_append (first last : Stack) :
    stackLength (first.append last) = stackLength first + stackLength last := by
  induction first <;> simp_all [Stack.append,stackLength] <;> omega

noncomputable def ordinaryAt (index : Nat)
    (history : GeneralHistory graph heap physical target) : Option OrdinaryMetadata := by
  induction history generalizing index with
  | @push owners core target physical lexical carrier ordinary tail ih =>
    exact match index,target with
      | 0,.plain plain => some ⟨owners,core,plain⟩
      | 0,_ => none
      | n+1,_ => ih n
  | @append firstPhysical firstTarget lastPhysical lastTarget first last ihFirst ihLast =>
    exact if index < stackLength firstTarget then ihFirst index else ihLast (index-stackLength firstTarget)
  | _ => exact none

theorem BindHead.metadata (member : BindHead owners frame plain history below) :
    ordinaryAt 0 history = some ⟨owners,frame,plain⟩ := by
  induction member with
  | here => rfl
  | append first last below member ih =>
    change (if 0 < stackLength (historyTarget first) then ordinaryAt 0 first else ordinaryAt (0-stackLength (historyTarget first)) last) = _
    have positive : 0 < stackLength (historyTarget first) := by rw [member.lexical]; simp [stackLength]
    rw [if_pos positive]
    exact ih
  | emptyPrefix leading member ih => simpa only [ordinaryAt,stackLength,Nat.lt_irrefl,if_false,Nat.sub_zero] using ih

theorem SecondHead.length (member : SecondHead owners frame plain history) :
    2 ≤ stackLength (historyTarget history) := by
  induction member with
  | direct related ordinary previous =>
    have same := congrArg stackLength previous.lexical
    simp only [historyTarget,stackLength] at same ⊢
    omega
  | append first last previous ih =>
    simp only [historyTarget,stackLength_append] at ih ⊢
    omega
  | crossed first last previous =>
    have same := congrArg stackLength previous.lexical
    simp only [historyTarget,stackLength_append,stackLength] at same ⊢
    omega

theorem SecondHead.metadata (member : SecondHead owners frame plain history) :
    ordinaryAt 1 history = some ⟨owners,frame,plain⟩ := by
  induction member with
  | direct related ordinary previous => exact previous.metadata
  | append first last previous ih =>
    change (if 1 < stackLength (historyTarget first) then ordinaryAt 1 first else ordinaryAt (1-stackLength (historyTarget first)) last) = _
    have positive : 1 < stackLength (historyTarget first) := by have := previous.length; omega
    rw [if_pos positive]
    exact ih
  | crossed first last previous =>
    simpa only [ordinaryAt,stackLength,Nat.lt_irrefl,if_false,Nat.sub_self] using previous.metadata

theorem HeadMember.position_shift {graph : Graph} {heap : CoreMachine.Heap}
    {history : GeneralHistory graph heap physical target}
    {below : GeneralHistory graph heap belowPhysical belowTarget}
    (member : HeadMember firstOwners firstFrame firstPlain history below) (n : Nat) :
    ordinaryAt (n+1) history = ordinaryAt n below := by
  induction member with
  | here related ordinary tail => rfl
  | append first last below member ih =>
    change (if n+1 < stackLength (historyTarget first) then ordinaryAt (n+1) first else ordinaryAt ((n+1)-stackLength (historyTarget first)) last) =
      (if n < stackLength (historyTarget below) then ordinaryAt n below else ordinaryAt (n-stackLength (historyTarget below)) last)
    have length : stackLength (historyTarget first) = stackLength (historyTarget below)+1 := by
      simpa only [historyTarget,stackLength] using congrArg stackLength member.lexical
    by_cases lower : n < stackLength (historyTarget below)
    · have upper : n+1 < stackLength (historyTarget first) := by omega
      rw [if_pos upper,if_pos lower,ih]
    · have upper : ¬ n+1 < stackLength (historyTarget first) := by omega
      have index : n+1-stackLength (historyTarget first) = n-stackLength (historyTarget below) := by omega
      rw [if_neg upper,if_neg lower,index]

theorem SecondHead.below_metadata {graph : Graph} {heap : CoreMachine.Heap}
    {history : GeneralHistory graph heap physical target}
    {below : GeneralHistory graph heap belowPhysical belowTarget}
    (first : HeadMember firstOwners firstFrame firstPlain history below)
    (second : SecondHead owners frame plain history) :
    ordinaryAt 0 below = some ⟨owners,frame,plain⟩ := by
  rw [← HeadMember.position_shift first 0]
  exact second.metadata

theorem stackLength_zero (empty : stackLength target = 0) : target = .nil := by
  cases target <;> simp_all [stackLength]

theorem GeneralHistory.empty_physical (history : GeneralHistory graph heap physical target)
    (empty : target = .nil) : physical = [] := by
  induction history with
  | nil => rfl
  | retained receipt => cases empty; cases receipt; rfl
  | append first last ihFirst ihLast =>
    have lengths := congrArg stackLength empty
    simp only [stackLength_append,stackLength] at lengths
    have a : stackLength (historyTarget first) = 0 := by simp only [historyTarget]; omega
    have b : stackLength (historyTarget last) = 0 := by simp only [historyTarget]; omega
    rw [ihFirst (stackLength_zero a),ihLast (stackLength_zero b)]
    rfl
  | _ => cases empty

private theorem bind_head_produced {graph : Graph} {heap : CoreMachine.Heap}
    (history : GeneralHistory graph heap physical target)
    (same : ordinaryAt 0 history = some ⟨owners,.bind binder body environment,plain⟩) :
    ∃ tailPhysical tailTarget, Nonempty (Σ tail : GeneralHistory graph heap tailPhysical tailTarget,
      BindHead owners (.bind binder body environment) plain history tail) := by
  induction history with
  | nil | retained | handler | running | unwinding | closing | live | spent => cases same
  | @push savedOwners core target physical lexical carrier ordinary tail ih =>
    cases target with
    | plain savedPlain =>
      have metadata := Option.some.inj same
      have ownerSame := congrArg OrdinaryMetadata.owners metadata
      have frameSame := congrArg OrdinaryMetadata.frame metadata
      have plainSame := congrArg OrdinaryMetadata.plain metadata
      simp only at ownerSame frameSame plainSame
      cases ownerSame; cases frameSame; cases plainSame
      cases carrier with
      | ordinary related => exact ⟨_,_,⟨⟨tail,.here related ordinary tail⟩⟩⟩
      | initializer related => cases related
      | request related => cases related
      | resume related => cases related
      | boundary related => cases related
    | _ => cases same
  | @append firstPhysical firstTarget lastPhysical lastTarget first last ihFirst ihLast =>
    by_cases positive : 0 < stackLength firstTarget
    · have lower : ordinaryAt 0 first = some ⟨owners,.bind binder body environment,plain⟩ := by
        simpa only [ordinaryAt,positive,if_true] using same
      obtain ⟨p,t,⟨⟨below,member⟩⟩⟩ := ihFirst lower
      exact ⟨_,_,⟨⟨below.append last,.append first last below member⟩⟩⟩
    · have empty : firstTarget = .nil := stackLength_zero (by omega)
      have physicalEmpty := GeneralHistory.empty_physical first empty
      cases empty; cases physicalEmpty
      have lower : ordinaryAt 0 last = some ⟨owners,.bind binder body environment,plain⟩ := by
        simpa only [ordinaryAt,stackLength,Nat.lt_irrefl,if_false,Nat.sub_zero] using same
      obtain ⟨p,t,⟨⟨below,member⟩⟩⟩ := ihLast lower
      exact ⟨_,_,⟨⟨first.append below,.emptyPrefix first member⟩⟩⟩

theorem SecondHead.pullback {graph : Graph} {heap : CoreMachine.Heap}
    {history : GeneralHistory graph heap physical target}
    {below : GeneralHistory graph heap belowPhysical belowTarget}
    (first : HeadMember firstOwners firstFrame firstPlain history below)
    (second : SecondHead owners (.bind binder body environment) plain history) :
    ∃ tailPhysical tailTarget, Nonempty (Σ tail : GeneralHistory graph heap tailPhysical tailTarget,
      BindHead owners (.bind binder body environment) plain below tail) :=
  bind_head_produced below (SecondHead.below_metadata first second)

structure BindBelow {graph : Graph} {heap : CoreMachine.Heap}
    (owners : OwnerMap) (binder body : Nat) (environment : Environment) (plain : PlainData)
    {physical : List CoreMachine.Frame} {target : Stack}
    (whole : GeneralHistory graph heap physical target) where
  physical : List CoreMachine.Frame
  target : Stack
  history : GeneralHistory graph heap physical target
  member : BindHead owners (.bind binder body environment) plain whole history

private noncomputable def bind_below {graph : Graph} {heap : CoreMachine.Heap}
    (history : GeneralHistory graph heap physical target)
    (same : ordinaryAt 0 history = some ⟨owners,.bind binder body environment,plain⟩) :
    BindBelow owners binder body environment plain history :=
  Classical.choice (by
    obtain ⟨p,t,⟨⟨tail,member⟩⟩⟩ := bind_head_produced history same
    exact ⟨⟨p,t,tail,member⟩⟩)

private noncomputable def heap_transport {graph : Graph} {oldHeap nextHeap : CoreMachine.Heap}
    (history : GeneralHistory graph oldHeap physical target) (same : nextHeap = oldHeap) :
    GeneralHistory graph nextHeap physical target := by cases same; exact history

noncomputable def BindBelow.transport {graph : Graph} {oldHeap nextHeap : CoreMachine.Heap}
    {physical : List CoreMachine.Frame} {target : Stack}
    {oldHistory : GeneralHistory graph oldHeap physical target}
    (below : BindBelow owners binder body environment plain oldHistory)
    (nextHistory : GeneralHistory graph nextHeap physical target)
    (heapSame : nextHeap = oldHeap) (historySame : HEq nextHistory oldHistory) :
    BindBelow owners binder body environment plain nextHistory := by
  cases heapSame
  cases eq_of_heq historySame
  exact below

noncomputable def BindBelow.append {graph : Graph} {heap : CoreMachine.Heap}
    {physical : List CoreMachine.Frame} {target : Stack}
    {whole : GeneralHistory graph heap physical target}
    (below : BindBelow owners binder body environment plain whole)
    (last : GeneralHistory graph heap lastPhysical lastTarget) :
    BindBelow owners binder body environment plain (whole.append last) :=
  ⟨below.physical ++ lastPhysical,below.target.append lastTarget,below.history.append last,
    .append whole last below.history below.member⟩

noncomputable def BindBelow.same_heap {graph : Graph} {oldHeap nextHeap : CoreMachine.Heap}
    {physical : List CoreMachine.Frame} {target : Stack}
    {whole : GeneralHistory graph oldHeap physical target}
    (below : BindBelow owners binder body environment plain whole) (same : nextHeap = oldHeap) :
    BindBelow owners binder body environment plain (heap_transport whole same) := by
  cases same
  exact below

noncomputable def BindHead.heap_weaken {graph : Graph} {heap larger : CoreMachine.Heap}
    {physical belowPhysical : List CoreMachine.Frame} {target belowTarget : Stack}
    {whole : GeneralHistory graph heap physical target} {below : GeneralHistory graph heap belowPhysical belowTarget}
    (member : BindHead owners frame plain whole below) (extension : HeapExtends heap larger) :
    BindHead owners frame plain (whole.heap_weaken extension) (below.heap_weaken extension) := by
  induction member with
  | here related ordinary tail => exact .here (related.heap_weaken extension) ordinary (tail.heap_weaken extension)
  | append first last below member ih => exact .append _ _ _ ih
  | emptyPrefix leading member ih => exact .emptyPrefix _ ih

noncomputable def BindBelow.heap_weaken {graph : Graph} {heap larger : CoreMachine.Heap}
    {physical : List CoreMachine.Frame} {target : Stack}
    {whole : GeneralHistory graph heap physical target}
    (below : BindBelow owners binder body environment plain whole) (extension : HeapExtends heap larger) :
    BindBelow owners binder body environment plain (whole.heap_weaken extension) :=
  ⟨below.physical,below.target,below.history.heap_weaken extension,below.member.heap_weaken extension⟩

theorem BindBelow.same_heap_physical {graph : Graph} {oldHeap nextHeap : CoreMachine.Heap}
    {physical : List CoreMachine.Frame} {target : Stack}
    {whole : GeneralHistory graph oldHeap physical target}
    (below : BindBelow owners binder body environment plain whole) (same : nextHeap = oldHeap) :
    (below.same_heap same).physical = below.physical := by cases same; rfl

private theorem drop_bind_split {graph : Graph} {heap otherHeap : CoreMachine.Heap}
    {whole : GeneralHistory graph heap physical target}
    {kept : GeneralHistory graph otherHeap keptPhysical keptTarget}
    (original : BindBelow owners binder body environment plain whole)
    (captured : BindBelow owners binder body environment plain kept)
    (same : physical = keptPhysical ++ outside) :
    original.physical = captured.physical ++ outside := by
  have a := original.member.physical
  have b := captured.member.physical
  simp only [historyPhysical] at a b
  rw [a,b,List.cons_append] at same
  exact (List.cons.inj same).2

inductive BindScopeReady (graph : Graph) (owners : OwnerMap) (scope : Execution.Scope)
    (kept : List CoreMachine.Frame) (selectedOwners : OwnerMap) (selectedScope : Execution.Scope) : Type where
  | inside (checked : insideCheck owners scope kept = true)
  | outside (unique : UniqueHandlerSites graph)
      (metadata : savedCallerHeadCheck owners scope selectedOwners selectedScope = true)
      (position : callerOutsideCheck owners scope kept = true)

private theorem scope_restored {graph : Graph}
    (origin : CurrentScopeOrigin graph owners scope physical)
    (same : physical = kept ++ outside)
    (ready : BindScopeReady graph owners scope kept selectedOwners data.scope)
    (past : GeneralClausePast graph selectedOwners handler owner occurrence dynamicTicket captured data)
    {addedHistory : GeneralHistory graph heap addedPhysical addedTarget}
    (front : PassFront (match owners with | [] => 0 | e::_ => e.handler)
      (match owners with | [] => 0 | e::_ => e.owner) addedHistory) :
    CurrentScopeOrigin graph owners scope
      (kept ++ (addedPhysical ++ .clauseBoundary handler owner occurrence dynamicTicket none :: outside)) := by
  cases ready with
  | inside checked => exact CurrentScopeOrigin.restore_inside origin same (scope_inside_computed origin same checked) _
  | outside unique metadata position =>
    cases owners <;> simpa only [List.append_assoc,List.singleton_append] using
      original_scope_restored origin same position past unique metadata front

private theorem empty_locations (history : GeneralHistory graph heap physical target)
    (empty : target = .nil) : handler_locations history = [] := by
  induction history with
  | nil | retained => rfl
  | append first last ihFirst ihLast =>
    have lengths := congrArg stackLength empty
    simp only [stackLength_append,stackLength] at lengths
    have a : stackLength (historyTarget first) = 0 := by simp only [historyTarget]; omega
    have b : stackLength (historyTarget last) = 0 := by simp only [historyTarget]; omega
    change (handler_locations first).map (fun location => location.suffix last) ++
      (handler_locations last).map (fun location => location.prepend first) = []
    rw [ihFirst (stackLength_zero a),ihLast (stackLength_zero b)]
    rfl
  | _ => cases empty

def BindHead.whole {graph : Graph} {heap : CoreMachine.Heap}
    {physical belowPhysical : List CoreMachine.Frame} {target belowTarget : Stack}
    {history : GeneralHistory graph heap physical target}
    {below : GeneralHistory graph heap belowPhysical belowTarget}
    (_member : BindHead owners frame plain history below) : GeneralHistory graph heap physical target := history

theorem BindHead.selected_before {graph : Graph} {heap : CoreMachine.Heap}
    {physical belowPhysical : List CoreMachine.Frame} {target belowTarget : Stack}
    {history : GeneralHistory graph heap physical target}
    {below : GeneralHistory graph heap belowPhysical belowTarget}
    (member : BindHead owners frame plain history below)
    (selected : HandlerLocation graph heap physical target)
    (present : selected ∈ handler_locations history) :
    ∃ p t, Nonempty (Σ tail : GeneralHistory graph heap p t,
      BindHead owners frame plain selected.before tail) := by
  induction member with
  | here related ordinary tail =>
    simp only [handler_locations] at present
    obtain ⟨lower,_,same⟩ := List.mem_map.mp present
    cases same
    exact ⟨_,_,⟨⟨GeneralHistory.nil.append lower.before,
      .append (.push (.ordinary related) ordinary .nil) lower.before .nil (.here related ordinary .nil)⟩⟩⟩
  | append first last below member ih =>
    simp only [handler_locations,List.mem_append] at present
    cases present with
    | inl present =>
      obtain ⟨lower,lowerPresent,same⟩ := List.mem_map.mp present
      cases same
      obtain ⟨p,t,⟨⟨tail,found⟩⟩⟩ := ih lower lowerPresent
      exact ⟨_,_,⟨⟨tail,found⟩⟩⟩
    | inr present =>
      obtain ⟨lower,_,same⟩ := List.mem_map.mp present
      cases same
      exact ⟨_,_,⟨⟨below.append lower.before,.append first lower.before below member⟩⟩⟩
  | emptyPrefix leading member ih =>
    change selected ∈ (handler_locations leading).map (fun location => location.suffix (BindHead.whole member)) ++
      (handler_locations (BindHead.whole member)).map (fun location => location.prepend leading) at present
    rw [empty_locations leading rfl] at present
    simp only [List.map_nil,List.nil_append] at present
    obtain ⟨lower,lowerPresent,same⟩ := List.mem_map.mp present
    cases same
    obtain ⟨p,t,⟨⟨tail,found⟩⟩⟩ := ih lower lowerPresent
    exact ⟨_,_,⟨⟨leading.append tail,.emptyPrefix leading found⟩⟩⟩

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

private theorem adjacent_selected {graph : Graph} {heap : CoreMachine.Heap}
    (first : PlainFrameRel graph firstOwners heap firstFrame firstPlain) (firstOrdinary)
    (second : PlainFrameRel graph owners heap (.bind binder body environment) plain) (secondOrdinary)
    (tail : GeneralHistory graph heap physical target)
    (index : Fin (handler_locations (.push (.ordinary first) firstOrdinary
      (.push (.ordinary second) secondOrdinary tail))).length) :
    Nonempty (SecondHead owners (.bind binder body environment) plain
      (((handler_locations (.push (.ordinary first) firstOrdinary
        (.push (.ordinary second) secondOrdinary tail)))[index]).before.append
        (.handler ((handler_locations (.push (.ordinary first) firstOrdinary
          (.push (.ordinary second) secondOrdinary tail)))[index]).installation
          ((handler_locations (.push (.ordinary first) firstOrdinary
            (.push (.ordinary second) secondOrdinary tail)))[index]).header .nil))) := by
  obtain ⟨middle,present,outerSame⟩ := pushed_location first firstOrdinary
    (.push (.ordinary second) secondOrdinary tail) index
  simp only [handler_locations] at present
  obtain ⟨lower,_,innerSame⟩ := List.mem_map.mp present
  rw [outerSame,← innerSame]
  exact ⟨.append _ _ (.crossed (.push (.ordinary first) firstOrdinary .nil) _
    (.append (.push (.ordinary second) secondOrdinary .nil) _ .nil
      (.here second secondOrdinary .nil)))⟩

private theorem adjacent_current {graph : Graph} {heap originalHeap : CoreMachine.Heap}
    (first : PlainFrameRel graph firstOwners originalHeap firstFrame firstPlain) (firstOrdinary)
    (second : PlainFrameRel graph owners originalHeap (.bind binder body environment) plain) (secondOrdinary)
    (tail : GeneralHistory graph originalHeap originalPhysical originalTarget)
    (history : GeneralHistory graph heap physical target)
    (heapSame : heap = originalHeap)
    (physicalSame : physical = firstFrame :: .bind binder body environment :: originalPhysical)
    (targetSame : target = .push (.plain firstPlain) (.push (.plain plain) originalTarget))
    (same : HEq history (GeneralHistory.push (.ordinary first) firstOrdinary (GeneralHistory.push (.ordinary second) secondOrdinary tail)))
    (index : Fin (handler_locations history).length) :
    Nonempty (SecondHead owners (.bind binder body environment) plain
      (((handler_locations history)[index]).before.append
        (.handler ((handler_locations history)[index]).installation ((handler_locations history)[index]).header .nil))) := by
  cases heapSame
  cases physicalSame
  cases targetSame
  cases eq_of_heq same
  exact adjacent_selected first firstOrdinary second secondOrdinary tail index

private theorem adjacent_general {graph : Graph} {heap : CoreMachine.Heap}
    (first : PlainFrameRel graph firstOwners heap firstFrame firstPlain) (ordinary)
    (tail : GeneralHistory graph heap physical target)
    (below : GeneralHistory graph heap belowPhysical belowTarget)
    (second : BindHead owners frame plain tail below)
    (index : Fin (handler_locations (.push (.ordinary first) ordinary tail)).length) :
    Nonempty (SecondHead owners frame plain
      (((handler_locations (.push (.ordinary first) ordinary tail))[index]).before.append
        (.handler ((handler_locations (.push (.ordinary first) ordinary tail))[index]).installation
          ((handler_locations (.push (.ordinary first) ordinary tail))[index]).header .nil))) := by
  obtain ⟨lower,present,same⟩ := pushed_location first ordinary tail index
  obtain ⟨p,t,⟨⟨remaining,found⟩⟩⟩ := second.selected_before lower present
  rw [same]
  exact ⟨.append _ _ (.crossed (.push (.ordinary first) ordinary .nil) _ found)⟩

private theorem adjacent_general_current {graph : Graph} {heap originalHeap : CoreMachine.Heap}
    (first : PlainFrameRel graph firstOwners originalHeap firstFrame firstPlain) (ordinary)
    (tail : GeneralHistory graph originalHeap originalPhysical originalTarget)
    (below : BindBelow owners binder body environment plain tail)
    (history : GeneralHistory graph heap physical target)
    (heapSame : heap = originalHeap)
    (physicalSame : physical = firstFrame :: originalPhysical)
    (targetSame : target = .push (.plain firstPlain) originalTarget)
    (same : HEq history (GeneralHistory.push (.ordinary first) ordinary tail))
    (index : Fin (handler_locations history).length) :
    Nonempty (SecondHead owners (.bind binder body environment) plain
      (((handler_locations history)[index]).before.append
        (.handler ((handler_locations history)[index]).installation ((handler_locations history)[index]).header .nil))) := by
  cases heapSame
  cases physicalSame
  cases targetSame
  cases eq_of_heq same
  exact adjacent_general first ordinary tail below.history below.member index

section Original
variable {graph : Graph} {bindBefore : Endpoint graph} (binding : BindInput bindBefore)
variable (ready : EntryReady .pair (bind_result binding).after)
variable (pastRun : Prefix graph (bind_result binding).after)
variable {captured : Endpoint graph}
variable (before : BeforeCapture pastRun ready captured count) (input : CaptureInput captured)

private theorem original_bind_related : PlainFrameRel graph binding.owners bindBefore.state.heap
    (.bind binding.binder.id binding.body binding.environment) binding.plain :=
  binding.past.saved.saved.related.heap_weaken (by rw [binding.predecessor]; exact fun _ _ h => h)

include ready pastRun before in
theorem first_selected_adjacent : Nonempty (SecondHead binding.owners
    (.bind binding.binder.id binding.body binding.environment) binding.plain
    ((location captured input.index).before.append
      (.handler (location captured input.index).installation (location captured input.index).header .nil))) := by
  exact adjacent_current (pastRun.receipt ready).saved.related (by trivial)
    (original_bind_related binding) (by trivial) bindBefore.history captured.history
    (BeforeCapture.heap before) (BeforeCapture.physical before) (BeforeCapture.lexical before)
    (BeforeCapture.history before) input.index

noncomputable def first_kept_bind : BindBelow binding.owners binding.binder.id binding.body binding.environment binding.plain
    (CoreCallableStrictCaptureOrigins.dormant before input).keptHistory :=
  bind_below _ (SecondHead.below_metadata (CoreCallableStrictCaptureOrigins.dormant before input).captured
    (Classical.choice (first_selected_adjacent binding ready pastRun before input)))

variable {current : Endpoint graph} (after : AfterCapture input current afterCount)
noncomputable def first_restored_bind : BindBelow binding.owners binding.binder.id binding.body binding.environment binding.plain
    (CoreCallableStrictCaptureOrigins.restored_tail before input after) :=
  ((first_kept_bind binding ready pastRun before input).same_heap after.carrier.heapSame).append
    (after.carrier.frontHistory.append (.spent (capture_data input).installation after.carrier.header after.carrier.outsideHistory))


theorem first_original_bind_tail : bindBefore.physical =
    (first_kept_bind binding ready pastRun before input).physical ++ (location captured input.index).outside := by
  have split := CoreCallableStrictCaptureOrigins.dormant_original_tail before input
  have head := (first_kept_bind binding ready pastRun before input).member.physical
  simp only [historyPhysical] at head
  change .bind binding.binder.id binding.body binding.environment :: bindBefore.physical = _ at split
  rw [head,List.cons_append] at split
  exact (List.cons.inj split).2

theorem first_bind_scope
    (checked : BindScopeReady graph binding.owners binding.plain.scope
      (first_kept_bind binding ready pastRun before input).physical
      (location captured input.index).owners (location captured input.index).data.scope) :
    CurrentScopeOrigin graph binding.owners binding.plain.scope
      (first_restored_bind binding ready pastRun before input after).physical := by
  have produced := scope_restored binding.past.saved.saved.origin
    (first_original_bind_tail binding ready pastRun before input) checked (capture_data input).installation
    (AfterCapture.caller_front_pass after _ _)
  change CurrentScopeOrigin graph binding.owners binding.plain.scope
    ((BindBelow.same_heap _ after.carrier.heapSame).physical ++ _)
  rw [BindBelow.same_heap_physical]
  exact produced

variable (resume : ResumeReady input current)
variable (installed : CoreCallableStrictCallerHeadConsumers.ReturnedReady before input after resume)
variable {secondCaptured secondCurrent : Endpoint graph}
variable (secondBefore : CoreCallableRestoredTupleHeads.RightBefore installed secondCaptured secondCount)
variable (secondInput : CaptureInput secondCaptured)

include ready pastRun before after resume installed secondBefore in
theorem second_selected_adjacent : Nonempty (SecondHead binding.owners
    (.bind binding.binder.id binding.body binding.environment) binding.plain
    ((location secondCaptured secondInput.index).before.append
      (.handler (location secondCaptured secondInput.index).installation
        (location secondCaptured secondInput.index).header .nil))) := by
  exact adjacent_general_current (CoreCallableRestoredTupleHeads.installed_related installed) (by trivial)
    (CoreCallableStrictCaptureOrigins.restored_tail before input after)
    (first_restored_bind binding ready pastRun before input after) secondCaptured.history
    (CoreCallableRestoredTupleHeads.RightBefore.heap installed secondBefore)
    (CoreCallableRestoredTupleHeads.RightBefore.physical installed secondBefore)
    (CoreCallableRestoredTupleHeads.RightBefore.lexical installed secondBefore)
    (CoreCallableRestoredTupleHeads.RightBefore.history installed secondBefore) secondInput.index

noncomputable def second_kept_bind : BindBelow binding.owners binding.binder.id binding.body binding.environment binding.plain
    (CoreCallableRestoredTupleHeads.dormant installed secondBefore secondInput).keptHistory :=
  bind_below _ (SecondHead.below_metadata (CoreCallableRestoredTupleHeads.dormant installed secondBefore secondInput).captured
    (Classical.choice (second_selected_adjacent binding ready pastRun before input after resume installed secondBefore secondInput)))

variable (secondAfter : AfterCapture secondInput secondCurrent secondAfterCount)
variable (secondResume : ResumeReady secondInput secondCurrent)

noncomputable def second_restored_bind : BindBelow binding.owners binding.binder.id binding.body binding.environment binding.plain
    (CoreCallableRestoredTupleHeads.restored_tail installed secondBefore secondInput secondAfter) :=
  ((second_kept_bind binding ready pastRun before input after resume installed secondBefore secondInput).same_heap secondAfter.carrier.heapSame).append
    (secondAfter.carrier.frontHistory.append (.spent (capture_data secondInput).installation secondAfter.carrier.header secondAfter.carrier.outsideHistory))

noncomputable def discharged_bind : BindBelow binding.owners binding.binder.id binding.body binding.environment binding.plain
    (CoreCallableRestoredTupleDischarge.tuple_after installed secondBefore secondInput secondAfter secondResume).history :=
  (second_restored_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter).heap_weaken
    (heap_append secondCurrent.state.heap [.pair resume.value secondResume.value])

theorem second_original_bind_tail :
    (first_restored_bind binding ready pastRun before input after).physical =
    (second_kept_bind binding ready pastRun before input after resume installed secondBefore secondInput).physical ++
      (location secondCaptured secondInput.index).outside :=
  drop_bind_split (first_restored_bind binding ready pastRun before input after)
    (second_kept_bind binding ready pastRun before input after resume installed secondBefore secondInput)
    (CoreCallableRestoredTupleHeads.dormant_original_tail installed secondBefore secondInput)

theorem second_bind_scope
    (firstChecked : BindScopeReady graph binding.owners binding.plain.scope
      (first_kept_bind binding ready pastRun before input).physical
      (location captured input.index).owners (location captured input.index).data.scope)
    (secondChecked : BindScopeReady graph binding.owners binding.plain.scope
      (second_kept_bind binding ready pastRun before input after resume installed secondBefore secondInput).physical
      (location secondCaptured secondInput.index).owners (location secondCaptured secondInput.index).data.scope) :
    CurrentScopeOrigin graph binding.owners binding.plain.scope
      (second_restored_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter).physical := by
  have produced := scope_restored (first_bind_scope binding ready pastRun before input after firstChecked)
    (second_original_bind_tail binding ready pastRun before input after resume installed secondBefore secondInput)
    secondChecked (capture_data secondInput).installation (AfterCapture.caller_front_pass secondAfter _ _)
  change CurrentScopeOrigin graph binding.owners binding.plain.scope
    ((BindBelow.same_heap _ secondAfter.carrier.heapSame).physical ++ _)
  rw [BindBelow.same_heap_physical]
  exact produced

theorem discharged_bind_scope
    (firstChecked : BindScopeReady graph binding.owners binding.plain.scope
      (first_kept_bind binding ready pastRun before input).physical
      (location captured input.index).owners (location captured input.index).data.scope)
    (secondChecked : BindScopeReady graph binding.owners binding.plain.scope
      (second_kept_bind binding ready pastRun before input after resume installed secondBefore secondInput).physical
      (location secondCaptured secondInput.index).owners (location secondCaptured secondInput.index).data.scope) :
    CurrentScopeOrigin graph binding.owners binding.plain.scope
      (discharged_bind binding ready pastRun before input after resume installed secondBefore secondInput secondAfter secondResume).physical :=
  second_bind_scope binding ready pastRun before input after resume installed secondBefore secondInput secondAfter firstChecked secondChecked

end Original

#print axioms BindHead.physical
#print axioms BindHead.lexical
#print axioms BindHead.metadata
#print axioms SecondHead.length
#print axioms SecondHead.metadata
#print axioms HeadMember.position_shift
#print axioms SecondHead.below_metadata
#print axioms SecondHead.pullback
#print axioms first_selected_adjacent
#print axioms BindHead.selected_before
#print axioms first_kept_bind
#print axioms first_restored_bind
#print axioms second_selected_adjacent
#print axioms second_kept_bind
#print axioms second_restored_bind
#print axioms discharged_bind
#print axioms first_original_bind_tail
#print axioms first_bind_scope
#print axioms second_original_bind_tail
#print axioms second_bind_scope
#print axioms discharged_bind_scope
end Ash.OneShot.CoreCallableRestoredBindOrigins
