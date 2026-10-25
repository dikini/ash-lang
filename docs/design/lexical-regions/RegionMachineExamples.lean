import RegionExamples

namespace Ash.Regions.Examples

/-- A preexisting outside return frame belongs to the entry control, not a region allocation. -/
def callerFrame (s : State 2 2 1) : State 2 2 1 :=
  { s with returnContexts := [(none, none)], returnCuts := [0] }

def modelMachine (s : State 2 2 1) : Machine 2 2 1 := ⟨s, fun _ => none, fun _ => none⟩
def noInlineLayout : Layout 2 2 := fun _ => []

theorem initial_machine_safe : Safe noInlineLayout (modelMachine (callerFrame empty)) := by
  have contexts : SavedContextsSafe (callerFrame empty) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r found
      exact empty_live r
    · intro p found; cases found
    · intro t c found; cases found
    · intro frame member
      have same : frame = (none, none) := List.mem_singleton.mp member
      subst frame
      constructor
      · intro r found; cases found
      · intro p found; cases found
  refine ⟨⟨⟨empty_valid, ?_, ?_, ?_, contexts⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i visible; cases visible
  · intro i o found; cases found
  · refine ⟨by decide, ?_⟩
    intro t c found; cases found
  · intro i v found; cases found
  · intro r _; exact empty_live r
  · intro r info parent found _ enclosing
    have same : info = liveRegion := Option.some.inj found.symm
    subst info
    cases enclosing
  · intro r c found; cases found
  · intro t c found; cases found

theorem construction_keeps_caller_frame (s next : State 2 2 1)
    (step : ConstructionStep s next) : ConstructionStep (callerFrame s) (callerFrame next) := by
  cases step with
  | request i req owner noPending freshReq fresh found phase callback cut =>
      exact .request _ i req owner noPending freshReq fresh found phase callback cut
  | supply i req reply continuation pending slot target registered fresh admitted =>
      exact .supply _ i req reply continuation pending slot target registered fresh admitted
  | initializeSlot i o deps fields found pending live guarded =>
      exact .initializeSlot _ i o deps fields found pending live guarded
  | publish group ready => exact .publish _ group ready
  | drop group noIncoming => exact .drop _ group noIncoming

theorem cyclic_machine_trace :
    Trace noInlineLayout (modelMachine (callerFrame empty)) (modelMachine (callerFrame usableCycle)) := by
  exact .next _ _ _ (.request _ 0 requestLeft liveRegion
      (construction_keeps_caller_frame _ _ request0_admitted) rfl (by intro c found; cases found))
    (.next _ _ _ (.supply _ 0 requestLeft (replyLeft 0) (continuation 0)
      (construction_keeps_caller_frame _ _ supply0_admitted) rfl (by intro c found; cases found))
    (.next _ _ _ (.request _ 1 requestLeft liveRegion
      (construction_keeps_caller_frame _ _ request1_admitted)
      rfl (by intro c found; cases found))
    (.next _ _ _ (.supply _ 1 requestLeft (replyLeft 1) (continuation 1)
      (construction_keeps_caller_frame _ _ supply1_admitted)
      rfl (by intro c found; cases found))
    (.next _ _ _ (.initializeSlot _ 0 privateObject [] [1]
      (construction_keeps_caller_frame _ _ initialize0_admitted) (by intro c found; cases found))
    (.next _ _ _ (.initializeSlot _ 1 privateObject [] [0]
      (construction_keeps_caller_frame _ _ initialize1_admitted) (by intro c found; cases found))
    (.next _ _ _ (.publish _ [0, 1] cyclic_group_ready
      (by intro i _; rfl) (by intro i o _ _ c found; cases found)) (.refl _)))))))

theorem cyclic_machine_safe : Safe noInlineLayout (modelMachine (callerFrame usableCycle)) :=
  trace_preserves _ _ _ initial_machine_safe cyclic_machine_trace

/-- Exact three-step empty-action release, with no omission of release start or return. -/
def releaseCursor (r : Fin nr) (info : Region nr) : CloseCursor nr :=
  { owner := r, association := info.association, initial := [], remaining := [] }

def closeReady (m : Machine nr no nt) (r : Fin nr) (info : Region nr) : Machine nr no nt :=
  advanceCleanup (beginClose m r info []) r (startRelease (releaseCursor r info))

theorem release_ready_same_heap (layout : Layout nr no) (m next : Machine nr no nt) (r : Fin nr)
    (heap : next.heap = m.heap) (roots : next.roots = m.roots)
    (ready : ReleaseReady layout m r) : ReleaseReady layout next r := by
  exact ⟨by simpa [heap] using ready.contexts, by simpa [heap] using ready.uses,
    by simpa [heap] using ready.children, by simpa [heap, roots] using ready.views,
    by simpa [heap] using ready.frames, by simpa [heap] using ready.providers⟩

theorem empty_release_trace (layout : Layout nr no) (m : Machine nr no nt)
    (r : Fin nr) (info : Region nr) (rest : List (Fin nr))
    (found : m.heap.regions r = some info) (live : info.phase = .live)
    (top : m.heap.completionOrder = r :: rest) (fresh : m.closing r = none)
    (recorded : [] = m.heap.cleanupActions r) (ready : ReleaseReady layout m r) :
    Trace layout m (closeReady m r info) := by
  refine .next _ _ _ (.beginClose m r info rest [] found live top fresh recorded)
    (.next _ _ _ (.cleanup _ r (releaseCursor r info) (startRelease (releaseCursor r info)) ?_ ?_
      (.release _ rfl rfl rfl) (by intro impossible; cases impossible) (fun _ => release_ready_same_heap layout m _ r rfl rfl ready)) (.refl _))
  · simp [beginClose, replace, releaseCursor]
  · change r ∈ m.heap.completionOrder
    rw [top]
    exact List.mem_cons_self

theorem no_access_release_ready (layout : Layout nr no) (m : Machine nr no nt) (r : Fin nr)
    (notSelected : m.heap.selected ≠ some r) (noPending : m.heap.pending = none)
    (noTickets : ∀ t, m.heap.tickets t = none) (noFrames : m.heap.returnContexts = [])
    (noRoots : ∀ i, m.roots i = none) (noExposed : ∀ i, m.heap.exposed i = false)
    (noParents : ∀ q info, m.heap.regions q = some info → info.parent = none)
    (noProviderViews : ∀ q info, m.heap.regions q = some info → info.precedingContext = none) :
    ReleaseReady layout m r := by
  refine ⟨⟨notSelected, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro p found; simp [noPending] at found
  · intro t c found; simp [noTickets t] at found
  · intro frame member; simp [noFrames] at member
  · intro i o visible; simp [noExposed i] at visible
  · intro q info found _ enclosing
    simp [noParents q info found] at enclosing
  · intro i v found; simp [noRoots i] at found
  · intro t c found; simp [noTickets t] at found
  · intro q info found _ enclosing
    simp [noProviderViews q info found] at enclosing

def afterCycleReturn : Machine 2 2 1 :=
  returnMachine (modelMachine (callerFrame usableCycle)) (none, none) [] 0 []

theorem cyclic_return_admitted :
    Transition noInlineLayout (modelMachine (callerFrame usableCycle)) afterCycleReturn :=
  .returnService _ (none, none) [] 0 [] rfl rfl rfl

def afterCycleDrop : Machine 2 2 1 :=
  { afterCycleReturn with heap := dropAccess afterCycleReturn.heap [0, 1] }

theorem cyclic_drop_admitted : Transition noInlineLayout afterCycleReturn afterCycleDrop := by
  apply Transition.dropAccess _ [0, 1]
  · intro i o _ outside _
    have covers : i ∈ ([0, 1] : List O) := (by decide : ∀ j : O, j ∈ ([0, 1] : List O)) i
    exact False.elim (outside covers)
  · intro i v found; cases found

def rightReleased := closeReady afterCycleDrop right liveRegion

def rightClosed := completeMachineClose rightReleased right liveRegion [left]

theorem right_release_ready : ReleaseReady noInlineLayout afterCycleDrop right := by
  apply no_access_release_ready
  · intro impossible; cases impossible
  · rfl
  · intro t; rfl
  · rfl
  · intro i; rfl
  · intro i
    change (if i ∈ ([0, 1] : List O) then false else afterCycleReturn.heap.exposed i) = false
    rw [if_pos ((by decide : ∀ j : O, j ∈ ([0, 1] : List O)) i)]
  · intro q info found
    change some liveRegion = some info at found
    have eq := Option.some.inj found
    subst info
    rfl
  · intro q info found
    change some liveRegion = some info at found
    have eq := Option.some.inj found
    subst info
    rfl

theorem right_finish_admitted : Transition noInlineLayout rightReleased rightClosed := by
  apply Transition.finishClose _ right liveRegion [left] (startRelease (releaseCursor right liveRegion))
  · simp [rightReleased, closeReady, advanceCleanup, replace]
  · exact ⟨rfl, rfl, rfl⟩
  · rfl
  · rfl
  · exact release_ready_same_heap noInlineLayout afterCycleDrop rightReleased right rfl rfl right_release_ready

def leftReleased := closeReady rightClosed left liveRegion

def cycleBulkClosed := completeMachineClose leftReleased left liveRegion []

theorem left_release_ready : ReleaseReady noInlineLayout rightClosed left := by
  apply no_access_release_ready
  · intro impossible; cases impossible
  · rfl
  · intro t; rfl
  · rfl
  · intro i; rfl
  · intro i
    have oldAbsent : rightReleased.heap.exposed i = false := by
      change afterCycleDrop.heap.exposed i = false
      change (if i ∈ ([0, 1] : List O) then false else afterCycleReturn.heap.exposed i) = false
      rw [if_pos ((by decide : ∀ j : O, j ∈ ([0, 1] : List O)) i)]
    change (closeRegion rightReleased.heap right liveRegion).exposed i = false
    cases atSlot : rightReleased.heap.objects i with
    | none => simp [closeRegion, atSlot]
    | some o => simp [closeRegion, atSlot, oldAbsent]
  · intro q info found
    change (replace (fun _ => some liveRegion) right (some { liveRegion with phase := .closed })) q = some info at found
    by_cases same : q = right
    · subst q
      simp [replace] at found
      subst info
      rfl
    · simp [replace, same] at found
      subst info
      rfl
  · intro q info found
    change (replace (fun _ => some liveRegion) right (some { liveRegion with phase := .closed })) q = some info at found
    by_cases same : q = right
    · subst q
      simp [replace] at found
      subst info
      rfl
    · simp [replace, same] at found
      subst info
      rfl

theorem left_finish_admitted : Transition noInlineLayout leftReleased cycleBulkClosed := by
  apply Transition.finishClose _ left liveRegion [] (startRelease (releaseCursor left liveRegion))
  · simp [leftReleased, closeReady, advanceCleanup, replace]
  · exact ⟨rfl, rfl, rfl⟩
  · rfl
  · rfl
  · exact release_ready_same_heap noInlineLayout rightClosed leftReleased left rfl rfl left_release_ready

end Ash.Regions.Examples

#print axioms Ash.Regions.Examples.initial_machine_safe
#print axioms Ash.Regions.Examples.cyclic_machine_trace
#print axioms Ash.Regions.Examples.cyclic_machine_safe
#print axioms Ash.Regions.Examples.empty_release_trace
#print axioms Ash.Regions.Examples.right_finish_admitted
#print axioms Ash.Regions.Examples.left_finish_admitted

namespace Ash.Regions.Examples

theorem trace_append (layout : Layout nr no) (a b c : Machine nr no nt)
    (first : Trace layout a b) (second : Trace layout b c) : Trace layout a c := by
  induction first with
  | refl => exact second
  | next a mid b step rest ih => exact .next a mid c step (ih second)

/-- Private cyclic initialization, usable graph, drop and both ordered bulk closes are admitted. -/
theorem cyclic_full_trace :
    Trace noInlineLayout (modelMachine (callerFrame empty)) cycleBulkClosed := by
  apply trace_append _ _ _ _ cyclic_machine_trace
  refine .next _ _ _ cyclic_return_admitted (.next _ _ _ cyclic_drop_admitted ?_)
  apply trace_append _ _ _ _ (empty_release_trace _ afterCycleDrop right liveRegion [left] rfl rfl rfl rfl rfl right_release_ready)
  refine .next _ _ _ right_finish_admitted ?_
  apply trace_append _ _ _ _ (empty_release_trace _ rightClosed left liveRegion [] rfl rfl rfl rfl rfl left_release_ready)
  exact .next _ _ _ left_finish_admitted (.refl _)

theorem cyclic_full_trace_safe : Safe noInlineLayout cycleBulkClosed :=
  trace_preserves _ _ _ initial_machine_safe cyclic_full_trace

/-- Bulk close follows owner identity, without traversing the cyclic data edges. -/
theorem cyclic_bulk_retired (i : O) :
    ∃ o, cycleBulkClosed.heap.objects i = some o ∧ o.phase = .retired ∧ o.region = left := by
  have alternatives : i = 0 ∨ i = 1 := (by decide : ∀ j : O, j = 0 ∨ j = 1) i
  rcases alternatives with same | same
  · subst i
    exact ⟨{ initializedObject 1 with phase := .retired }, rfl, rfl, rfl⟩
  · subst i
    exact ⟨{ initializedObject 0 with phase := .retired }, rfl, rfl, rfl⟩

theorem empty_machine_safe : Safe noInlineLayout (modelMachine empty) := by
  have full := initial_machine_safe
  have contexts : SavedContextsSafe empty := by
    refine ⟨full.1.1.2.2.2.2.1, full.1.1.2.2.2.2.2.1,
      full.1.1.2.2.2.2.2.2.1, ?_⟩
    intro frame impossible; cases impossible
  exact ⟨⟨⟨empty_valid, full.1.1.2.1, full.1.1.2.2.1, full.1.1.2.2.2.1, contexts⟩,
    full.1.2.1, full.1.2.2.1, full.1.2.2.2.1, full.1.2.2.2.2⟩, full.2⟩

def nestedRequest : Requirements 2 := ⟨right, 8, 8⟩
def nestedReply : Backing 2 2 := ⟨right, 1, association, 8, 8⟩
def nestedContinuation : Pending 2 2 :=
  { object := 1, selected := right, nextInitializer := 0, operandHistory := 7,
    continuationContext := none, continuationCut := 0 }
def nestedPrivate : Object 2 2 := ⟨right, .pending, [], [], 0⟩

def outerService := modelMachine request0
def suspendedService := suspendMachine outerService
def nestedRequested : Machine 2 2 1 :=
  { suspendedService with heap := requestStorage suspendedService.heap 1 nestedRequest liveRegion }
def nestedSupplied : Machine 2 2 1 :=
  { nestedRequested with heap := supplyStorage nestedRequested.heap 1 nestedRequest nestedReply nestedContinuation }
def nestedInitialized : Machine 2 2 1 :=
  { nestedSupplied with heap := initializeSlot nestedSupplied.heap 1 nestedPrivate [] [] }
def outerRestored := returnMachine nestedInitialized (none, some (continuation 0)) [] 0 []
def outerSuppliedAgain : Machine 2 2 1 :=
  { outerRestored with heap := supplyStorage outerRestored.heap 0 requestLeft (replyLeft 0) (continuation 0) }

theorem nested_request_admitted : Transition noInlineLayout suspendedService nestedRequested := by
  apply Transition.request _ 1 nestedRequest liveRegion
  · apply ConstructionStep.request _ 1 nestedRequest liveRegion
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro r found; cases found
    · exact List.mem_cons_self
  · rfl
  · intro c found; cases found

theorem nested_supply_admitted : Transition noInlineLayout nestedRequested nestedSupplied := by
  apply Transition.supply _ 1 nestedRequest nestedReply nestedContinuation
  · apply ConstructionStep.supply _ 1 nestedRequest nestedReply nestedContinuation
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ⟨rfl, rfl, Nat.le_refl _, by decide, rfl, liveRegion, rfl, rfl, rfl⟩
  · rfl
  · intro c found; cases found

theorem nested_initialize_admitted : Transition noInlineLayout nestedSupplied nestedInitialized := by
  apply Transition.initializeSlot _ 1 nestedPrivate [] []
  · apply ConstructionStep.initializeSlot _ 1 nestedPrivate [] [] rfl rfl
    · intro r member; cases member
    · intro j member; cases member
  · intro c found; cases found

theorem outer_supply_restored_admitted : Transition noInlineLayout outerRestored outerSuppliedAgain := by
  apply Transition.supply _ 0 requestLeft (replyLeft 0) (continuation 0)
  · apply ConstructionStep.supply _ 0 requestLeft (replyLeft 0) (continuation 0)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ⟨rfl, rfl, Nat.le_refl _, by decide, rfl, liveRegion, rfl, rfl, rfl⟩
  · rfl
  · intro c found; cases found

theorem nested_supply_trace : Trace noInlineLayout (modelMachine empty) outerSuppliedAgain := by
  exact .next _ _ _ (.request _ 0 requestLeft liveRegion request0_admitted rfl (by intro c found; cases found))
    (.next _ _ _ (.suspend _)
    (.next _ _ _ nested_request_admitted
    (.next _ _ _ nested_supply_admitted
    (.next _ _ _ nested_initialize_admitted
    (.next _ _ _ (.returnService _ (none, some (continuation 0)) [] 0 [] rfl rfl rfl)
    (.next _ _ _ outer_supply_restored_admitted (.refl _)))))))

theorem nested_supply_trace_safe : Safe noInlineLayout outerSuppliedAgain :=
  trace_preserves _ _ _ empty_machine_safe nested_supply_trace

theorem outer_request_not_replayed :
    outerRestored.heap.pending = some (continuation 0) ∧
    outerRestored.heap.operandHistory = empty.operandHistory ∧
    outerSuppliedAgain.heap.backing 0 = some (replyLeft 0) ∧
    outerSuppliedAgain.heap.backing 1 = some nestedReply := ⟨rfl, rfl, rfl, rfl⟩

def nestedRefused := refuseMachine nestedRequested 1
def restoredAfterRefusal := returnMachine nestedRefused (none, some (continuation 0)) [] 0 []

theorem nested_refusal_trace : Trace noInlineLayout (modelMachine empty) restoredAfterRefusal := by
  exact .next _ _ _ (.request _ 0 requestLeft liveRegion request0_admitted rfl (by intro c found; cases found))
    (.next _ _ _ (.suspend _)
    (.next _ _ _ nested_request_admitted
    (.next _ _ _ (.refuseBeforeStorage _ 1 nestedContinuation rfl rfl rfl rfl)
    (.next _ _ _ (.returnService _ (none, some (continuation 0)) [] 0 [] rfl rfl rfl) (.refl _)))))

theorem nested_refusal_safe : Safe noInlineLayout restoredAfterRefusal :=
  trace_preserves _ _ _ empty_machine_safe nested_refusal_trace

theorem nested_refusal_has_no_fake_storage :
    restoredAfterRefusal.heap.objects 1 = none ∧ restoredAfterRefusal.heap.backing 1 = none ∧
    restoredAfterRefusal.heap.pending = some (continuation 0) ∧
    restoredAfterRefusal.heap.operandHistory = empty.operandHistory := ⟨rfl, rfl, rfl, rfl⟩

/-- The extent premise is necessary even if owner and identity are correct. -/
theorem insufficient_storage_rejected :
    ¬ ReplyAdmitted empty 0 ⟨left, 16, 8⟩ (replyLeft 0) := by
  intro admitted
  exact (by decide : ¬ 16 ≤ 8) admitted.2.2.1

/-- A wrong owner cannot be repaired by a matching layout or current default. -/
theorem wrong_owner_reply_rejected :
    ¬ ReplyAdmitted empty 1 requestLeft nestedReply := by
  intro admitted
  exact (by decide : right ≠ left) admitted.1

/-- Releasing while actions remain would violate the cursor invariant. -/
def twoActions : CloseCursor 2 :=
  { owner := right, association := association, initial := [17, 23], remaining := [17, 23] }

theorem early_release_breaks_order : ¬ CursorOrdered (startRelease twoActions) := by
  intro ordered
  have absent := (ordered.2 (by decide)).2
  cases absent

theorem running_action_not_complete : ¬ CursorComplete (startAction twoActions 17 [23]) := by
  intro complete
  cases complete.1

def closingRight := beginClose (modelMachine empty) right liveRegion [17, 23]
def innerCapture : Captured 2 2 :=
  { selected := some right, pending := none, completionOrder := [right] }

theorem unfinished_close_cannot_be_discarded : ¬ DiscardAllowed closingRight innerCapture := by
  intro allowed
  have absent := allowed.1 right (by simp [innerCapture])
  simp [closingRight, beginClose, replace] at absent

/-- A captured cursor is dormant; resumption preserves that exact cursor record. -/
def capturedClosing := captureFull closingRight 0 [right] [left] (some left) 0 [] [] [] []

theorem captured_cleanup_not_active : ¬ ActiveCursor capturedClosing right := by
  simp [ActiveCursor, capturedClosing, captureFull, saveMachineFrames, saveFrames,
    captureMachine, capture, left, right]

theorem captured_cursor_unchanged : capturedClosing.closing = closingRight.closing := rfl

end Ash.Regions.Examples

#print axioms Ash.Regions.Examples.cyclic_full_trace
#print axioms Ash.Regions.Examples.cyclic_full_trace_safe
#print axioms Ash.Regions.Examples.cyclic_bulk_retired
#print axioms Ash.Regions.Examples.nested_supply_trace
#print axioms Ash.Regions.Examples.nested_supply_trace_safe
#print axioms Ash.Regions.Examples.outer_request_not_replayed
#print axioms Ash.Regions.Examples.nested_refusal_trace
#print axioms Ash.Regions.Examples.nested_refusal_safe
#print axioms Ash.Regions.Examples.nested_refusal_has_no_fake_storage
#print axioms Ash.Regions.Examples.insufficient_storage_rejected
#print axioms Ash.Regions.Examples.wrong_owner_reply_rejected
#print axioms Ash.Regions.Examples.early_release_breaks_order
#print axioms Ash.Regions.Examples.running_action_not_complete
#print axioms Ash.Regions.Examples.unfinished_close_cannot_be_discarded
#print axioms Ash.Regions.Examples.captured_cleanup_not_active
#print axioms Ash.Regions.Examples.captured_cursor_unchanged

namespace Ash.Regions.Examples

/-- F1: dropping every whole alias does not erase irreversible publication history. -/
theorem dropped_whole_cannot_republish : ¬ GroupReady outerDropped [0] := by
  exact published_record_cannot_republish outerInitialized [0] [0] 0 (by simp)

/-- F2: the exact previously admitted prefix has a distinct current request. -/
theorem unrelated_request_prefix :
    Trace noInlineLayout (modelMachine empty) (modelMachine request1) := by
  exact .next _ _ _ (.request _ 0 requestLeft liveRegion request0_admitted rfl
      (by intro c found; cases found))
    (.next _ _ _ (.supply _ 0 requestLeft (replyLeft 0) (continuation 0) supply0_admitted rfl
      (by intro c found; cases found))
    (.next _ _ _ (.request _ 1 requestLeft liveRegion request1_admitted rfl
      (by intro c found; cases found)) (.refl _)))

theorem unrelated_pending_refusal_guard_rejects : request1.pending ≠ none := by
  intro impossible
  cases impossible

/-- F4: initializing a guarded container does not publish its unfinished graph. -/
theorem guarded_container_not_inline_readable :
    ¬ ViewSafe InlineAccess.inlineLayout initialized0 InlineAccess.independentPart := by
  rintro ⟨o, found, ready, resident, published, rest⟩
  cases published

/-- F3: a running release denies source access, and successful return is bulk retirement. -/
def cycleInlineLayout : Layout 2 2 := fun _ => [[]]
def cycleInline : View 2 := ⟨0, some 0⟩

theorem source_view_denied_during_release : ¬ ViewAvailable cycleInlineLayout leftReleased cycleInline := by
  intro available
  have atSlot : leftReleased.heap.objects 0 = some (initializedObject 1) := rfl
  have denied := (available (initializedObject 1) atSlot).1
  exact running_release_unavailable leftReleased left (startRelease (releaseCursor left liveRegion))
    (by simp [leftReleased, closeReady, advanceCleanup, replace]) rfl denied

theorem retired_cycle_not_inline_readable : ¬ ViewSafe cycleInlineLayout cycleBulkClosed.heap cycleInline := by
  rintro ⟨o, found, ready, rest⟩
  have actual : cycleBulkClosed.heap.objects 0 = some { initializedObject 1 with phase := .retired } := rfl
  have same := Option.some.inj (found.symm.trans actual)
  subst o
  cases ready with
  | inl impossible => cases impossible
  | inr impossible => cases impossible

/-- A2: the caller cannot silently replace recorded cleanup obligations with an empty list. -/
def twoRecordedActions : State 2 2 1 :=
  { empty with cleanupActions := replace empty.cleanupActions right [17, 23] }

theorem omitted_cleanup_list_rejected : [] ≠ twoRecordedActions.cleanupActions right := by
  simp [twoRecordedActions, replace]

/-- A3: a live service retains its saved provider selection even without object records. -/
def retainedProvider : Region 2 := { liveRegion with precedingContext := some right }
def retainedProviderState : State 2 2 1 :=
  { empty with regions := replace empty.regions left (some retainedProvider) }

theorem service_view_blocks_younger_close : ¬ NoProviderContext retainedProviderState right := by
  intro absent
  have blocked := absent left retainedProvider (by simp [retainedProviderState, replace])
    (Or.inr rfl)
  exact blocked rfl

/-- A1: setup must authenticate the actual selected context, rather than an arbitrary live one. -/
theorem arbitrary_saved_setup_rejected :
    (some right : Option R) ≠ empty.selected := by decide

theorem arbitrary_saved_cut_rejected : 17 ≠ empty.currentCut := by decide

end Ash.Regions.Examples

#print axioms Ash.Regions.Examples.dropped_whole_cannot_republish
#print axioms Ash.Regions.Examples.unrelated_request_prefix
#print axioms Ash.Regions.Examples.unrelated_pending_refusal_guard_rejects
#print axioms Ash.Regions.Examples.guarded_container_not_inline_readable
#print axioms Ash.Regions.Examples.source_view_denied_during_release
#print axioms Ash.Regions.Examples.retired_cycle_not_inline_readable
#print axioms Ash.Regions.Examples.omitted_cleanup_list_rejected
#print axioms Ash.Regions.Examples.service_view_blocks_younger_close
#print axioms Ash.Regions.Examples.arbitrary_saved_setup_rejected
#print axioms Ash.Regions.Examples.arbitrary_saved_cut_rejected


namespace Ash.Regions.Examples

theorem empty_service_contexts : ServiceContextsSafe empty := by
  intro r info found _ q selected
  have same : info = liveRegion := Option.some.inj found.symm
  subst info
  cases selected

theorem initial_coherent : Coherent noInlineLayout (modelMachine (callerFrame empty)) := by
  exact ⟨initial_machine_safe, empty_service_contexts, by intro r c found; cases found⟩

theorem empty_coherent : Coherent noInlineLayout (modelMachine empty) :=
  ⟨empty_machine_safe, empty_service_contexts, by intro r c found; cases found⟩

theorem cyclic_full_trace_coherent : Coherent noInlineLayout cycleBulkClosed :=
  trace_coherent_preserves _ _ _ initial_coherent cyclic_full_trace

theorem nested_supply_coherent : Coherent noInlineLayout outerSuppliedAgain :=
  trace_coherent_preserves _ _ _ empty_coherent nested_supply_trace

theorem nested_refusal_coherent : Coherent noInlineLayout restoredAfterRefusal :=
  trace_coherent_preserves _ _ _ empty_coherent nested_refusal_trace

/-- Cleanup obligations are the recorded list, not a caller-selected surrogate. -/
def recordedMachine := modelMachine (callerFrame twoRecordedActions)
def recordedBegin := beginClose recordedMachine right liveRegion [17, 23]
def firstRunning := advanceCleanup recordedBegin right (startAction twoActions 17 [23])
def actionCaptured := captureFull firstRunning 0 [right] [left] (some left) 0 [] [(none, none)] [] [0]
def actionTicket : Captured 2 2 :=
  { selected := some left, pending := none, completionOrder := [right], cut := 0,
    frames := [], frameCuts := [] }
def actionResumed := resumeFull actionCaptured 0 actionTicket
def actionReturned := returnMachine actionResumed (some left, none) [(none, none)] 0 [0]
def actionOutsideReturned := returnMachine actionReturned (none, none) [] 0 []
def firstFinished := advanceCleanup actionOutsideReturned right (finishAction (startAction twoActions 17 [23]) 17)
def secondRunning := advanceCleanup firstFinished right
  (startAction (finishAction (startAction twoActions 17 [23]) 17) 23 [])
def secondFinished := advanceCleanup secondRunning right
  (finishAction (startAction (finishAction (startAction twoActions 17 [23]) 17) 23 []) 23)
def actionsComplete : CloseCursor 2 :=
  finishAction (startAction (finishAction (startAction twoActions 17 [23]) 17) 23 []) 23

theorem recorded_coherent : Coherent noInlineLayout recordedMachine :=
  ⟨initial_machine_safe, empty_service_contexts, by intro r c found; cases found⟩

theorem waiting_cleanup_admitted (layout : Layout nr no) (m : Machine nr no nt)
    (r : Fin nr) (c next : CloseCursor nr) (found : m.closing r = some c)
    (active : ActiveCursor m r) (step : CleanupStep c next) (waiting : next.release = .waiting) :
    Transition layout m (advanceCleanup m r next) := by
  exact .cleanup _ r c next found active step
    (by rw [waiting]; decide) (by intro running; rw [waiting] at running; cases running)

theorem recorded_action_prefix : Trace noInlineLayout recordedMachine actionOutsideReturned := by
  refine .next _ _ _ (.beginClose _ right liveRegion [left] [17, 23] rfl rfl rfl rfl rfl) ?_
  refine .next _ _ _ (waiting_cleanup_admitted _ _ right twoActions _ ?_ ?_
    (.start _ 17 [23] rfl rfl rfl) rfl) ?_
  · simp [beginClose, replace, twoActions, liveRegion]
  · change right ∈ ([right, left] : List R); simp
  refine .next _ _ _ (.capture firstRunning 0 [right] [left] (some left) 0 [] [(none, none)] [] [0]
    rfl rfl ?_ rfl rfl rfl ?_) ?_
  · intro q found
    have same := Option.some.inj found
    subst q
    exact empty_live left
  · intro q found
    have same := Option.some.inj found
    subst q
    intro c atSlot
    simp [firstRunning, advanceCleanup, recordedBegin, beginClose, replace, left, right, recordedMachine, modelMachine] at atSlot
  refine .next _ _ _ (.resume _ 0 actionTicket ?_) ?_
  · rfl
  exact .next _ _ _ (.returnService _ (some left, none) [(none, none)] 0 [0] rfl rfl rfl)
    (.next _ _ _ (.returnService _ (none, none) [] 0 [] rfl rfl rfl) (.refl _))

theorem recorded_action_finish_trace : Trace noInlineLayout actionOutsideReturned secondFinished := by
  refine .next _ _ _ (waiting_cleanup_admitted _ actionOutsideReturned right (startAction twoActions 17 [23]) _ rfl ?_ (.finish _ 17 rfl) rfl) ?_
  · change right ∈ ([right, left] : List R); simp
  refine .next _ _ _ (waiting_cleanup_admitted _ firstFinished right (finishAction (startAction twoActions 17 [23]) 17) _ (by simp [firstFinished, advanceCleanup, replace]) ?_
    (.start _ 23 [] rfl rfl rfl) rfl) ?_
  · change right ∈ ([right, left] : List R); simp
  refine .next _ _ _ (waiting_cleanup_admitted _ secondRunning right (startAction (finishAction (startAction twoActions 17 [23]) 17) 23 []) _ (by simp [secondRunning, advanceCleanup, replace]) ?_
    (.finish _ 23 rfl) rfl) (.refl _)
  change right ∈ ([right, left] : List R); simp

theorem captured_action_exact :
    actionCaptured.closing right = some (startAction twoActions 17 [23]) ∧
    actionCaptured.heap.completionOrder = [left] ∧
    actionCaptured.heap.returnContexts = [(none, none)] ∧
    actionResumed.closing right = some (startAction twoActions 17 [23]) ∧
    actionResumed.heap.completionOrder = [right, left] ∧
    actionResumed.heap.returnContexts = [(some left, none), (none, none)] ∧
    actionResumed.heap.tickets 0 = none := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem captured_unfinished_discard_rejected : ¬ DiscardAllowed actionCaptured actionTicket := by
  intro allowed
  have absent := allowed.1 right (by simp [actionTicket])
  simp [actionCaptured, captureFull, saveMachineFrames, captureMachine, firstRunning, advanceCleanup, replace] at absent

theorem actions_release_ready : ReleaseReady noInlineLayout secondFinished right := by
  apply no_access_release_ready
  · intro impossible; cases impossible
  · rfl
  · intro t
    have unique : t = 0 := Subsingleton.elim _ _
    subst t
    rfl
  · rfl
  · intro i; rfl
  · intro i; rfl
  · intro q info found
    have same : info = liveRegion := Option.some.inj found.symm
    subst info; rfl
  · intro q info found
    have same : info = liveRegion := Option.some.inj found.symm
    subst info; rfl

def actionsReleased := advanceCleanup secondFinished right (startRelease actionsComplete)
def actionsClosed := completeMachineClose actionsReleased right liveRegion [left]

theorem recorded_cleanup_trace : Trace noInlineLayout recordedMachine actionsClosed := by
  apply trace_append _ _ _ _ recorded_action_prefix
  apply trace_append _ _ _ _ recorded_action_finish_trace
  refine .next _ _ _ (.cleanup _ right actionsComplete (startRelease actionsComplete)
    (by simp [secondFinished, advanceCleanup, replace, actionsComplete]) ?_ (.release _ rfl rfl rfl)
    (by decide) (fun _ => actions_release_ready)) ?_
  · change right ∈ ([right, left] : List R); simp
  exact .next _ _ _ (.finishClose actionsReleased right liveRegion [left] (startRelease actionsComplete)
    (by simp [actionsReleased, advanceCleanup, replace]) ⟨rfl, rfl, rfl⟩ rfl rfl
    (release_ready_same_heap _ secondFinished actionsReleased right rfl rfl actions_release_ready)) (.refl _)

theorem recorded_cleanup_coherent : Coherent noInlineLayout actionsClosed :=
  trace_coherent_preserves _ _ _ recorded_coherent recorded_cleanup_trace

theorem recorded_cleanup_exact :
    actionsComplete.completed = [17, 23] ∧ actionsComplete.remaining = [] ∧
    actionsClosed.heap.regions right = some { liveRegion with phase := .closed } ∧
    actionsClosed.heap.completionOrder = [left] := ⟨rfl, rfl, rfl, rfl⟩

end Ash.Regions.Examples

#print axioms Ash.Regions.Examples.initial_coherent

#print axioms Ash.Regions.Examples.empty_coherent

#print axioms Ash.Regions.Examples.cyclic_full_trace_coherent

#print axioms Ash.Regions.Examples.nested_supply_coherent

#print axioms Ash.Regions.Examples.nested_refusal_coherent

#print axioms Ash.Regions.Examples.recorded_action_prefix

#print axioms Ash.Regions.Examples.recorded_action_finish_trace

#print axioms Ash.Regions.Examples.captured_action_exact

#print axioms Ash.Regions.Examples.captured_unfinished_discard_rejected

#print axioms Ash.Regions.Examples.recorded_cleanup_trace

#print axioms Ash.Regions.Examples.recorded_cleanup_coherent

#print axioms Ash.Regions.Examples.recorded_cleanup_exact

namespace Ash.Regions.Examples

/-- Setup starts before any prospective owner or selected term has been published. -/
def vacant : State 2 2 1 :=
  { empty with regions := fun _ => none, selected := none, completionOrder := [] }
def prospective : Region 2 :=
  { phase := .preparing, association := association, parent := none,
    precedingContext := none, providerCut := 0 }
def preparedMachine := updateMachineRegion (modelMachine vacant) left prospective

theorem vacant_coherent : Coherent noInlineLayout (modelMachine vacant) := by
  simp [Coherent, Safe, MachineSafe, Invariant, Valid, ObjectsSafe, OwnersOrdered,
    ContextSafe, PublicationSafe, BackingSafe, OwnersUnique, SavedContextsSafe,
    OptionLive, PendingLive, RootsSafe, OwnersLive, Owns, ParentsLive, ClosingSafe,
    TicketFramesSafe, ServiceContextsSafe, NoReturnedCursors, modelMachine, vacant, empty]

theorem prepare_admitted : Transition noInlineLayout (modelMachine vacant) preparedMachine := by
  exact .prepare _ left prospective rfl rfl rfl rfl
    (by intro parent absent; cases absent) (by intro parent absent; cases absent)
    (by intro q absent; cases absent)

theorem setup_enter_trace : Trace noInlineLayout (modelMachine vacant)
    (enterLive preparedMachine left prospective association) :=
  .next _ _ _ prepare_admitted
    (.next _ _ _ (.enter _ left prospective association (by simp [preparedMachine, updateMachineRegion, updateRegion, replace])
      rfl (by intro parent absent; cases absent)) (.refl _))

theorem setup_enter_coherent : Coherent noInlineLayout (enterLive preparedMachine left prospective association) :=
  trace_coherent_preserves _ _ _ vacant_coherent setup_enter_trace

theorem setup_abort_trace : Trace noInlineLayout (modelMachine vacant)
    (updateMachineRegion preparedMachine left { prospective with phase := .closed }) :=
  .next _ _ _ prepare_admitted
    (.next _ _ _ (.abortPrepare _ left prospective (by simp [preparedMachine, updateMachineRegion, updateRegion, replace]) rfl)
      (.refl _))

theorem setup_abort_coherent : Coherent noInlineLayout
    (updateMachineRegion preparedMachine left { prospective with phase := .closed }) :=
  trace_coherent_preserves _ _ _ vacant_coherent setup_abort_trace

/-- Root-free initial safety is independent of the authenticated layout table. -/
theorem empty_layout_coherent (layout : Layout 2 2) : Coherent layout (modelMachine empty) := by
  have safe := empty_coherent.1
  exact ⟨⟨⟨safe.1.1, (by intro i v found; cases found), safe.1.2.2.1,
    safe.1.2.2.2.1, safe.1.2.2.2.2⟩, safe.2⟩, empty_service_contexts,
    by intro r c found; cases found⟩

def inlinePublished := modelMachine outerPublished
def inlineBound := bindView inlinePublished 0 InlineAccess.independentPart
def inlineDropped : Machine 2 2 1 := { inlineBound with heap := dropAccess inlineBound.heap [0] }
def inlineReleased := closeReady inlineDropped right liveRegion
def inlineClosed := completeMachineClose inlineReleased right liveRegion [left]

theorem outer_full_construction : Trace InlineAccess.inlineLayout (modelMachine empty) inlinePublished := by
  exact .next _ _ _ (.request _ 0 requestLeft liveRegion request0_admitted rfl (by intro c found; cases found))
    (.next _ _ _ (.supply _ 0 requestLeft (replyLeft 0) (continuation 0) supply0_admitted rfl (by intro c found; cases found))
    (.next _ _ _ (.initializeSlot _ 0 privateObject [right] [] outer_initialize_admitted
      (by intro c found; cases found))
    (.next _ _ _ (.publish _ [0] outer_group_ready (by intro i _; rfl)
      (by intro i o _ _ c found; cases found)) (.refl _))))

theorem independent_view_available : ViewAvailable InlineAccess.inlineLayout inlinePublished InlineAccess.independentPart := by
  intro o found
  constructor
  · intro c atSlot; cases atSlot
  · intro deps atPart r member
    have same : deps = [] := by simpa [InlineAccess.inlineLayout, InlineAccess.independentPart] using atPart.symm
    subst deps; cases member

theorem inline_bind_drop_trace : Trace InlineAccess.inlineLayout inlinePublished inlineDropped := by
  refine .next _ _ _ (.bind _ 0 InlineAccess.independentPart
    InlineAccess.derived_inline_parts_safe.1 (Or.inl ?_) independent_view_available) ?_
  · simp [inlinePublished, modelMachine, outerPublished, publishGroup, InlineAccess.independentPart]
  refine .next _ _ _ (.dropAccess _ [0] ?_ ?_) (.refl _)
  · intro i o visible outside found j field
    have same : i = 0 := by simpa [inlineBound, bindView, inlinePublished, modelMachine, outerPublished, publishGroup, outer_private_flags] using visible
    subst i
    exact False.elim (outside (by simp))
  · intro i v found member whole
    have same : v = InlineAccess.independentPart := by
      by_cases atZero : i = 0
      · subst i; simpa [bindView, setRoot, replace, inlinePublished, modelMachine] using found.symm
      · simp [bindView, setRoot, replace, atZero, inlinePublished, modelMachine] at found
    subst v; cases member

theorem inline_release_ready : ReleaseReady InlineAccess.inlineLayout inlineDropped right := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, ?_, ?_, ?_⟩
    · intro p absent; cases absent
    · intro t c absent; cases absent
    · intro frame absent; cases absent
  · intro i o visible
    have noFlags : inlineDropped.heap.exposed i = false := by
      change (if i ∈ ([0] : List O) then false else outerPublished.exposed i) = false
      simp [outerPublished, publishGroup, outer_private_flags]
    rw [noFlags] at visible; cases visible
  · intro q info found _ enclosing
    have same : info = liveRegion := Option.some.inj found.symm
    subst info; cases enclosing
  · intro i v found
    have same : v = InlineAccess.independentPart := by
      by_cases atZero : i = 0
      · subst i; simpa [inlineDropped, inlineBound, bindView, setRoot, replace, inlinePublished, modelMachine] using found.symm
      · simp [inlineDropped, inlineBound, bindView, setRoot, replace, atZero, inlinePublished, modelMachine] at found
    subst v
    exact InlineAccess.independent_part_avoids_younger
  · intro t c absent; cases absent
  · intro q info found _ enclosing
    have same : info = liveRegion := Option.some.inj found.symm
    subst info; cases enclosing

theorem retained_inline_release_trace : Trace InlineAccess.inlineLayout (modelMachine empty) inlineClosed := by
  apply trace_append _ _ _ _ outer_full_construction
  apply trace_append _ _ _ _ inline_bind_drop_trace
  apply trace_append _ _ _ _ (empty_release_trace _ inlineDropped right liveRegion [left]
    rfl rfl rfl rfl rfl inline_release_ready)
  exact .next _ _ _ (.finishClose inlineReleased right liveRegion [left] (startRelease (releaseCursor right liveRegion))
    (by simp [inlineReleased, closeReady, advanceCleanup, replace]) ⟨rfl, rfl, rfl⟩ rfl rfl
    (release_ready_same_heap _ inlineDropped inlineReleased right rfl rfl inline_release_ready)) (.refl _)

theorem retained_inline_coherent : Coherent InlineAccess.inlineLayout inlineClosed :=
  trace_coherent_preserves _ _ _ (empty_layout_coherent _) retained_inline_release_trace

theorem retained_inline_use : Transition InlineAccess.inlineLayout inlineClosed inlineClosed := by
  apply Transition.use inlineClosed 0
  · exact ⟨InlineAccess.independentPart, rfl, InlineAccess.independent_inline_usable_after_close⟩
  · intro v found
    have same : v = InlineAccess.independentPart := Option.some.inj found.symm
    subst v
    intro o foundObject
    have sameObject : o = outerCapturedObject := Option.some.inj (foundObject.symm.trans outer_initialized_record)
    subst o
    constructor
    · intro c atSlot
      simp [inlineClosed, completeMachineClose, replace, outerCapturedObject, left, right,
        inlineReleased, closeReady, advanceCleanup, beginClose, inlineDropped, inlineBound, bindView,
        inlinePublished, modelMachine] at atSlot
    · intro deps atPart r member
      have sameDeps : deps = [] := by simpa [InlineAccess.inlineLayout, InlineAccess.independentPart] using atPart.symm
      subst deps; cases member

end Ash.Regions.Examples

#print axioms Ash.Regions.Examples.vacant_coherent

#print axioms Ash.Regions.Examples.setup_enter_trace

#print axioms Ash.Regions.Examples.setup_enter_coherent

#print axioms Ash.Regions.Examples.setup_abort_trace

#print axioms Ash.Regions.Examples.setup_abort_coherent

#print axioms Ash.Regions.Examples.outer_full_construction

#print axioms Ash.Regions.Examples.inline_bind_drop_trace

#print axioms Ash.Regions.Examples.retained_inline_release_trace

#print axioms Ash.Regions.Examples.retained_inline_coherent

#print axioms Ash.Regions.Examples.retained_inline_use


namespace Ash.Regions.Examples

theorem other_owner_request_during_release : Transition noInlineLayout actionsReleased
    { actionsReleased with heap := requestStorage actionsReleased.heap 0 requestLeft liveRegion } := by
  apply Transition.request actionsReleased 0 requestLeft liveRegion
  · exact .request _ 0 requestLeft liveRegion rfl rfl rfl rfl rfl
      (by intro q impossible; cases impossible) (by decide)
  · rfl
  · intro c found
    simp [actionsReleased, advanceCleanup, replace, requestLeft, left, right,
      secondFinished, secondRunning, firstFinished, actionOutsideReturned, returnMachine,
      actionReturned, actionResumed, resumeFull, actionCaptured, captureFull, saveMachineFrames, captureMachine,
      firstRunning, recordedBegin, beginClose, recordedMachine, modelMachine] at found

theorem retained_inline_call : Transition InlineAccess.inlineLayout inlineClosed inlineClosed := by
  apply Transition.call inlineClosed 0
  · exact ⟨InlineAccess.independentPart, rfl, InlineAccess.independent_inline_usable_after_close⟩
  · intro v found
    have same : v = InlineAccess.independentPart := Option.some.inj found.symm
    subst v
    intro o foundObject
    have sameObject : o = outerCapturedObject := Option.some.inj (foundObject.symm.trans outer_initialized_record)
    subst o
    constructor
    · intro c atSlot
      simp [inlineClosed, completeMachineClose, replace, outerCapturedObject, left, right,
        inlineReleased, closeReady, advanceCleanup, beginClose, inlineDropped, inlineBound, bindView,
        inlinePublished, modelMachine] at atSlot
    · intro deps atPart r member
      have sameDeps : deps = [] := by simpa [InlineAccess.inlineLayout, InlineAccess.independentPart] using atPart.symm
      subst deps; cases member

end Ash.Regions.Examples

#print axioms Ash.Regions.Examples.other_owner_request_during_release
#print axioms Ash.Regions.Examples.retained_inline_call


namespace Ash.Regions.Examples

/-- An owner-free captured segment can be discarded; outside ownership is retained. -/
def discardCapture := captureFull (modelMachine empty) 0 [] [right, left] (some left) 0 [] [] [] []
def discardTicket : Captured 2 2 :=
  { selected := some left, pending := none, completionOrder := [] }

theorem admitted_discard_trace : Trace noInlineLayout (modelMachine empty)
    (discardMachine discardCapture 0 discardTicket) := by
  refine .next _ _ _ (.capture _ 0 [] [right, left] (some left) 0 [] [] [] [] rfl rfl ?_ rfl rfl rfl ?_) ?_
  · intro r found
    have same := Option.some.inj found
    subst r; exact empty_live left
  · intro r _ c absent; cases absent
  exact .next _ _ _ (.discard _ 0 discardTicket rfl
    (by simp [DiscardAllowed, discardTicket])
    (by simp [FramesDiscardAllowed, discardTicket])) (.refl _)

theorem admitted_discard_coherent : Coherent noInlineLayout (discardMachine discardCapture 0 discardTicket) :=
  trace_coherent_preserves _ _ _ empty_coherent admitted_discard_trace

end Ash.Regions.Examples

#print axioms Ash.Regions.Examples.admitted_discard_trace
#print axioms Ash.Regions.Examples.admitted_discard_coherent

namespace Ash.Regions.Examples

/-- A whole callable-shaped value remains under left; only the caller default changes. -/
def callableBound := bindView inlinePublished 0 (WholeView 0)
def callerRight := selectMachine callableBound right

theorem whole_view_available (m : Machine nr no nt) (v : View no)
    (noCursors : ∀ r, m.closing r = none) : ViewAvailable layout m v := by
  intro o _
  constructor
  · intro c found; rw [noCursors] at found; cases found
  · cases kind : v.inlinePart with
    | none => intro r _ c found; rw [noCursors] at found; cases found
    | some part => intro deps _ r _ c found; rw [noCursors] at found; cases found

theorem caller_call_trace : Trace InlineAccess.inlineLayout (modelMachine empty) callerRight := by
  apply trace_append _ _ _ _ outer_full_construction
  refine .next _ _ _ (.bind _ 0 (WholeView 0) InlineAccess.published_whole_safe
    (Or.inl (by simp [inlinePublished, modelMachine, outerPublished, publishGroup, WholeView]))
    (whole_view_available _ _ (by intro r; rfl))) ?_
  refine .next _ _ _ (.select _ right (empty_live right) (by intro c found; cases found)) ?_
  exact .next _ _ _ (.call callerRight 0
    ⟨WholeView 0, rfl, InlineAccess.published_whole_safe⟩
    (by intro v _; exact whole_view_available _ _ (by intro r; rfl))) (.refl _)

theorem caller_call_coherent : Coherent InlineAccess.inlineLayout callerRight :=
  trace_coherent_preserves _ _ _ (empty_layout_coherent _) caller_call_trace

theorem caller_default_request : Transition InlineAccess.inlineLayout callerRight
    { callerRight with heap := requestStorage callerRight.heap 1 nestedRequest liveRegion } := by
  apply Transition.request _ 1 nestedRequest liveRegion
  · exact .request _ 1 nestedRequest liveRegion rfl (by decide) (by decide) rfl rfl
      (by intro q impossible; cases impossible) (by decide)
  · rfl
  · intro c found; cases found

theorem caller_explicit_left_request : Transition InlineAccess.inlineLayout callerRight
    { callerRight with heap := requestStorage callerRight.heap 1 requestLeft liveRegion } := by
  apply Transition.request _ 1 requestLeft liveRegion
  · exact .request _ 1 requestLeft liveRegion rfl (by decide) (by decide) rfl rfl
      (by intro q impossible; cases impossible) (by decide)
  · rfl
  · intro c found; cases found

theorem call_keeps_existing_closure :
    callerRight.heap.objects 0 = some outerCapturedObject ∧
    callerRight.heap.backing 0 = some (replyLeft 0) ∧
    callerRight.heap.selected = some right ∧
    (requestStorage callerRight.heap 1 nestedRequest liveRegion).pending =
      some { object := 1, selected := right, nextInitializer := 0, operandHistory := 7,
             continuationContext := some right, continuationCut := 0 } ∧
    (requestStorage callerRight.heap 1 requestLeft liveRegion).pending =
      some { object := 1, selected := left, nextInitializer := 0, operandHistory := 7,
             continuationContext := some right, continuationCut := 0 } := ⟨rfl, rfl, rfl, rfl, rfl⟩

end Ash.Regions.Examples

#print axioms Ash.Regions.Examples.caller_call_trace
#print axioms Ash.Regions.Examples.caller_call_coherent
#print axioms Ash.Regions.Examples.caller_default_request
#print axioms Ash.Regions.Examples.caller_explicit_left_request
#print axioms Ash.Regions.Examples.call_keeps_existing_closure
