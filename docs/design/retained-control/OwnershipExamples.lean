import Ownership

/- Concrete traces test the bounded transitions; they are not Ash programs. -/
namespace Ash.RetainedControl.Examples

open Ash.RetainedControl

def p : Capture := ⟨10, [10, 11], [100], [101], [], 7, [.live], .running, 42⟩
def q : Capture := ⟨20, [20], [100], [101], [], 7, [], .finished, 21⟩
def root : Consumer := ⟨30, 7, .root⟩
def current : Consumer := ⟨31, 7, .continued⟩
def vacant : Slot := ⟨0, 0, .vacant⟩
def qSlot : Slot := ⟨1, 0, .live q⟩
def spare : Slot := ⟨2, 0, .vacant⟩
def firstKey : Key := ⟨9, 0, 0⟩

def initial : State where
  storeId := 9
  storeOwner := 5
  interpretation := 7
  maxGeneration := 2
  support := [100]
  outsideCompletion := [101]
  clause := some (p, root)
  slots := [vacant, qSlot, spare]
  active := none
  completed := []
  disposed := []
  leaked := []
  result := none
  adminSuffixClear := true
  closePhase := .armed
  closed := false
  failed := false
  incomplete := false

def suspended : State := { initial with
  clause := none
  slots := [{ vacant with phase := .live p }, qSlot, spare]
  result := some (respond root (.suspended firstKey)) }

def restored : State := { suspended with
  slots := [{ vacant with phase := .spent }, qSlot, spare]
  active := some (p, current)
  result := none }

def checkpointed : State := { restored with active := none, clause := some (p, current) }

def yieldedAgain : State := { checkpointed with
  clause := none
  slots := [{ vacant with phase := .spent }, qSlot, { spare with phase := .live p }]
  result := some (respond current (.suspended ⟨9, 2, 0⟩)) }

def pAfterResume : Capture := { p with nested := [.consumed] }
def afterResume : State := { restored with active := some (pAfterResume, current) }
def pAfterCleanup : Capture := { pAfterResume with cleanup := .finished }
def afterCleanup : State := { afterResume with active := some (pAfterCleanup, current) }
def completed : State := { afterCleanup with
  active := none
  completed := pAfterCleanup.owners ++ afterCleanup.completed
  result := some (respond current .finished) }

theorem initial_unique_slots : SlotIdsUnique initial := by
  simp [SlotIdsUnique, initial, vacant, qSlot, spare]

theorem initial_context_safe : ContextSafe initial := by
  simp [ContextSafe, Admit, initial, p, q, root, vacant, qSlot, spare]

theorem initial_unique_owners : Unique initial := by
  intro owner
  simp [allOwners, liveOwners, optionOwners, slotOwners, initial, vacant, qSlot, spare, p, q,
    List.count_cons]
  by_cases h10 : owner = 10
  · simp [h10]
  by_cases h11 : owner = 11
  · simp [h11]
  by_cases h20 : owner = 20
  · simp [h20]
  · simp [Ne.symm h10, Ne.symm h11, Ne.symm h20]

def beforeRoot : State := { initial with clause := none, slots := [vacant, spare] }
def rootStarted : State := { beforeRoot with active := some (p, root) }

theorem root_admission_starts_fresh_work : Step beforeRoot p.owners rootStarted := by
  apply Step.launch beforeRoot p root
  · rfl
  · rfl
  · simp [Admit, beforeRoot, initial, p]
  · simp [RootFresh, allOwners, liveOwners, optionOwners, slotOwners, beforeRoot,
      initial, vacant, spare]
  · intro owner
    simp [p, List.count_cons]
    by_cases h10 : owner = 10
    · simp [h10]
    by_cases h11 : owner = 11
    · simp [h11]
    · simp [Ne.symm h10, Ne.symm h11]
  · rfl
  · rfl
  · rfl
  · rfl

theorem retain_p : Step initial [] suspended := by
  apply Step.retain initial [] [qSlot, spare] vacant p root
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Admit, initial, p]
  · rfl
  · rfl
  · rfl

theorem restore_to_current_consumer : Step suspended [] restored := by
  apply Step.restore suspended [] [qSlot, spare] { vacant with phase := .live p } p current firstKey
  all_goals rfl

theorem checkpoint_running_cleanup : Step restored [] checkpointed := by
  exact Step.checkpoint restored p current rfl rfl rfl

theorem resumed_cleanup_keeps_saved_result :
    (match restored.active with | some (capture, _) => capture.savedResult | none => 0) = 42 := rfl

theorem resumed_cleanup_is_still_running :
    (match restored.active with | some (capture, _) => capture.cleanup | none => .armed) = .running := rfl

theorem nested_owner_remains_live_before_resume :
    (match restored.active with | some (capture, _) => capture.nested | none => []) = [.live] := rfl

theorem yield_again_to_current_consumer : Step checkpointed [] yieldedAgain := by
  apply Step.retain checkpointed [{ vacant with phase := .spent }, qSlot] [] spare p current
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Admit, checkpointed, restored, suspended, initial, p]
  · rfl
  · rfl
  · rfl

theorem p_nested_resume : Step restored [] afterResume := by
  exact Step.consumeNested restored p current [] [] rfl rfl rfl

theorem p_finishes_cleanup : Step afterResume [] afterCleanup := by
  exact Step.finishCleanup afterResume pAfterResume current rfl rfl rfl

theorem p_completes : Step afterCleanup [] completed := by
  apply Step.finish afterCleanup pAfterCleanup current rfl
  · simp [ReadyToFinish, pAfterCleanup, pAfterResume, p]
  · rfl

theorem current_consumer_completion_trace : Trace initial completed := by
  exact Trace.next (Trace.next (Trace.next (Trace.next (Trace.next (Trace.refl initial)
    retain_p) restore_to_current_consumer) p_nested_resume) p_finishes_cleanup) p_completes

theorem current_consumer_trace_preserves_ownership_and_context :
    Unique completed ∧ ContextSafe completed := by
  exact ⟨trace_preserves_unique current_consumer_completion_trace initial_unique_owners,
    trace_preserves_context current_consumer_completion_trace initial_context_safe⟩

theorem yield_again_returns_to_current_consumer :
    yieldedAgain.result = some (31, .someAnswer (.suspended ⟨9, 2, 0⟩)) := rfl

theorem completion_returns_to_current_consumer :
    completed.result = some (31, .someAnswer .finished) := rfl

theorem other_branch_remains_owned :
    qSlot ∈ completed.slots ∧ qSlot.phase = .live q := by
  simp [completed, afterCleanup, afterResume, restored, suspended, qSlot]

theorem p_cannot_finish_running_cleanup : ¬ ReadyToFinish p := by
  simp [ReadyToFinish, p]

theorem old_key_cannot_replay_after_any_finite_trace (later : State)
    (trace : Trace restored later) : ¬ LiveKey later firstKey := by
  apply restore_cannot_replay suspended [] [qSlot, spare] { vacant with phase := .live p }
    p current firstKey later
  · simp [SlotIdsUnique, suspended, initial, vacant, qSlot, spare]
  · rfl
  · rfl
  · rfl
  · rfl
  · exact trace

theorem shared_outer_support_is_admitted : Admit initial p ∧ Admit initial q := by
  simp [Admit, initial, p, q]

theorem preparation_refusal_retains_the_original_owner : Step initial [] initial :=
  Step.refuse initial

theorem answer_constructors_do_not_change_owned_work :
    liveOwners { restored with result := some (999, .root .finished) } = liveOwners restored := rfl

theorem retained_q_prevents_release : ¬ NoWork completed := by
  simp [NoWork, liveOwners, optionOwners, slotOwners, completed, afterCleanup, afterResume,
    restored, suspended, initial, vacant, qSlot, q, spare]

theorem reject_self_capture : ¬ Admit initial { p with owners := [5, 10] } := by
  simp [Admit, initial, p]

theorem reject_skipped_outside_completion :
    ¬ Admit initial { p with outsideCompletion := [999] } := by
  simp [Admit, initial, p]

theorem reject_branch_local_escape : ¬ Admit initial { p with exported := [10] } := by
  simp [Admit, initial, p]

theorem reject_wrong_interpretation : p.interpretation ≠ (⟨99, 8, .continued⟩ : Consumer).interpretation := by
  decide

theorem reject_captured_outside_owner : ¬ Admit initial { p with owners := [10, 100] } := by
  simp [Admit, initial, p]

theorem reject_unreferenced_outside_owner :
    ¬ Admit initial { p with owners := [10, 100], outsideSupport := [] } := by
  simp [Admit, initial, p]

theorem generation_exhaustion_has_no_recycle_capacity : ¬ (2 < initial.maxGeneration) := by decide

def failureStarted : State := { restored with failed := true }
def failureComplete : State := { failureStarted with
  clause := none
  slots := []
  active := none
  disposed := liveOwners failureStarted ++ failureStarted.disposed }
def failurePartial : State := { failureStarted with
  slots := [{ vacant with phase := .spent }, { qSlot with phase := .spent }, spare]
  disposed := q.owners ++ failureStarted.disposed }
def partialThenIncomplete : State := { failurePartial with
  clause := none
  slots := []
  active := none
  leaked := liveOwners failurePartial ++ failurePartial.leaked
  incomplete := true }
def failureIncomplete : State := { failureStarted with
  clause := none
  slots := []
  active := none
  leaked := liveOwners failureStarted ++ failureStarted.leaked
  incomplete := true }

theorem begin_failure : Step restored [] failureStarted := Step.beginFailure restored

theorem teardown_can_complete : Step failureStarted [] failureComplete :=
  Step.finishDisposal failureStarted rfl

theorem teardown_partial_disposes_q : Step failureStarted [] failurePartial := by
  apply Step.disposeSlot failureStarted [{ vacant with phase := .spent }] [spare] qSlot q
  all_goals rfl

theorem partial_teardown_then_refusal : Trace failureStarted partialThenIncomplete := by
  exact Trace.next (Trace.next (Trace.refl failureStarted) teardown_partial_disposes_q)
    (Step.refuseDisposal failurePartial rfl)

theorem partial_teardown_records_distinct_outcomes :
    partialThenIncomplete.disposed = [20] ∧
      partialThenIncomplete.leaked = [10, 11] ∧ partialThenIncomplete.incomplete = true := by
  decide

theorem teardown_can_report_incomplete : Step failureStarted [] failureIncomplete :=
  Step.refuseDisposal failureStarted rfl

theorem incomplete_is_not_a_source_cleanup :
    failureIncomplete.incomplete = true ∧ failureIncomplete.failed = true := by decide

/- Outer abandonment starts the existing armed cleanup without dropping P or Q.
   The empty-work premise below stands for the later C3 drain proof. -/
def closing : State := { suspended with closePhase := .running }
def closingP : State := { restored with closePhase := .running }
def closingCheckpoint : State := { closingP with active := none, clause := some (p, current) }
def closingYielded : State := { closingCheckpoint with
  clause := none
  slots := [{ vacant with phase := .spent }, qSlot, { spare with phase := .live p }]
  result := some (respond current (.suspended ⟨9, 2, 0⟩)) }
def closingAfterResume : State := { afterResume with closePhase := .running }
def closingAfterCleanup : State := { afterCleanup with closePhase := .running }
def closingPDone : State := { completed with closePhase := .running }
def qKey : Key := ⟨9, 1, 0⟩
def closingQ : State := { closingPDone with
  slots := [{ vacant with phase := .spent }, { qSlot with phase := .spent }, spare]
  active := some (q, current)
  result := none }
def closingQDone : State := { closingQ with
  active := none
  completed := q.owners ++ closingQ.completed
  result := some (respond current .finished) }
def drainReturned : State := { closingQDone with closePhase := .finished }
def storeReleased : State := { drainReturned with closed := true }

theorem armed_outer_close_starts_with_slots_intact : Step suspended [] closing := by
  exact Step.startOuterClose suspended rfl rfl rfl rfl rfl

theorem outer_close_restores_p : Step closing [] closingP := by
  apply Step.restore closing [] [qSlot, spare] { vacant with phase := .live p } p current firstKey
  all_goals rfl

theorem checkpoint_while_drain_runs : Step closingP [] closingCheckpoint := by
  exact Step.checkpoint closingP p current rfl rfl rfl

theorem yield_while_drain_runs : Step closingCheckpoint [] closingYielded := by
  apply Step.retain closingCheckpoint [{ vacant with phase := .spent }, qSlot] [] spare p current
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Admit, closingCheckpoint, closingP, restored, suspended, initial, p]
  · rfl
  · rfl
  · rfl

theorem running_drain_yield_trace : Trace suspended closingYielded := by
  exact Trace.next (Trace.next (Trace.next (Trace.refl suspended)
    armed_outer_close_starts_with_slots_intact) outer_close_restores_p)
    checkpoint_while_drain_runs |>.next yield_while_drain_runs

theorem running_drain_yield_keeps_q :
    closingYielded.closePhase = .running ∧ qSlot ∈ closingYielded.slots ∧
      qSlot.phase = .live q := by
  simp [closingYielded, closingCheckpoint, closingP, restored, suspended, qSlot]

theorem outer_close_runs_nested_resume : Step closingP [] closingAfterResume := by
  exact Step.consumeNested closingP p current [] [] rfl rfl rfl

theorem outer_close_finishes_p_cleanup : Step closingAfterResume [] closingAfterCleanup := by
  exact Step.finishCleanup closingAfterResume pAfterResume current rfl rfl rfl

theorem outer_close_finishes_p : Step closingAfterCleanup [] closingPDone := by
  apply Step.finish closingAfterCleanup pAfterCleanup current rfl
  · simp [ReadyToFinish, pAfterCleanup, pAfterResume, p]
  · rfl

theorem outer_close_restores_q : Step closingPDone [] closingQ := by
  apply Step.restore closingPDone [{ vacant with phase := .spent }] [spare] qSlot q current qKey
  all_goals rfl

theorem outer_close_finishes_q : Step closingQ [] closingQDone := by
  apply Step.finish closingQ q current rfl
  · simp [ReadyToFinish, q]
  · rfl

theorem no_work_after_both_roots_finish : NoWork closingQDone := by rfl

theorem outer_drain_returns_empty : Step closingQDone [] drainReturned := by
  exact Step.finishOuterClose closingQDone rfl no_work_after_both_roots_finish rfl

theorem store_release_follows_drain : Step drainReturned [] storeReleased := by
  apply Step.release drainReturned
  · exact no_work_after_both_roots_finish
  · exact Or.inr rfl
  · rfl
  · rfl

theorem outer_close_complete_trace : Trace suspended storeReleased := by
  exact Trace.next (Trace.next (Trace.next (Trace.next (Trace.next (Trace.next
    (Trace.next (Trace.next (Trace.refl suspended) armed_outer_close_starts_with_slots_intact)
      outer_close_restores_p) outer_close_runs_nested_resume) outer_close_finishes_p_cleanup)
    outer_close_finishes_p) outer_close_restores_q) outer_close_finishes_q)
    outer_drain_returns_empty |>.next store_release_follows_drain

end Ash.RetainedControl.Examples

#print axioms Ash.RetainedControl.Examples.initial_unique_owners
#print axioms Ash.RetainedControl.Examples.initial_context_safe
#print axioms Ash.RetainedControl.Examples.root_admission_starts_fresh_work
#print axioms Ash.RetainedControl.Examples.retain_p
#print axioms Ash.RetainedControl.Examples.restore_to_current_consumer
#print axioms Ash.RetainedControl.Examples.resumed_cleanup_keeps_saved_result
#print axioms Ash.RetainedControl.Examples.resumed_cleanup_is_still_running
#print axioms Ash.RetainedControl.Examples.nested_owner_remains_live_before_resume
#print axioms Ash.RetainedControl.Examples.yield_again_to_current_consumer
#print axioms Ash.RetainedControl.Examples.current_consumer_completion_trace
#print axioms Ash.RetainedControl.Examples.current_consumer_trace_preserves_ownership_and_context
#print axioms Ash.RetainedControl.Examples.running_drain_yield_trace
#print axioms Ash.RetainedControl.Examples.running_drain_yield_keeps_q
#print axioms Ash.RetainedControl.Examples.completion_returns_to_current_consumer
#print axioms Ash.RetainedControl.Examples.other_branch_remains_owned
#print axioms Ash.RetainedControl.Examples.old_key_cannot_replay_after_any_finite_trace
#print axioms Ash.RetainedControl.Examples.shared_outer_support_is_admitted
#print axioms Ash.RetainedControl.Examples.preparation_refusal_retains_the_original_owner
#print axioms Ash.RetainedControl.Examples.retained_q_prevents_release
#print axioms Ash.RetainedControl.Examples.reject_self_capture
#print axioms Ash.RetainedControl.Examples.reject_skipped_outside_completion
#print axioms Ash.RetainedControl.Examples.reject_branch_local_escape
#print axioms Ash.RetainedControl.Examples.reject_wrong_interpretation
#print axioms Ash.RetainedControl.Examples.reject_captured_outside_owner
#print axioms Ash.RetainedControl.Examples.reject_unreferenced_outside_owner
#print axioms Ash.RetainedControl.Examples.generation_exhaustion_has_no_recycle_capacity
#print axioms Ash.RetainedControl.Examples.teardown_can_report_incomplete
#print axioms Ash.RetainedControl.Examples.teardown_can_complete
#print axioms Ash.RetainedControl.Examples.partial_teardown_then_refusal
#print axioms Ash.RetainedControl.Examples.partial_teardown_records_distinct_outcomes
#print axioms Ash.RetainedControl.Examples.outer_close_complete_trace
