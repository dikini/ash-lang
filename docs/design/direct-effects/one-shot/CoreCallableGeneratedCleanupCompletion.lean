import CoreCallableGeneratedChronology
import CoreCallableCleanupActivation
namespace Ash.OneShot.CoreCallableGeneratedCleanupCompletion
open CoreSyntax CoreTranslation CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableGeneralHistory CoreCallableRunningOccurrence CoreCallableReachableResume
open CoreCallableCleanupOrigins CoreCallableCleanupReachableTransport CoreCallableOutsideOrigin
open CoreCallableGeneratedChronology

/-- A selected original running head is read from the SAME current history.
Only the running constructor and actual history appends are accepted. -/
inductive RunningHead
    (start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget)
    {heap : CoreMachine.Heap} :
    {physical : List CoreMachine.Frame} → {target : Stack} → GeneralHistory graph heap physical target → Type where
  | running (receipt : RunningReceipt graph cleanupOwners heap action environment data savedValue savedCode originalPhysical) :
      RunningHead start (.running receipt)
  | append (first : GeneralHistory graph heap firstPhysical firstTarget)
      (second : GeneralHistory graph heap secondPhysical secondTarget)
      (head : RunningHead start first) : RunningHead start (first.append second)
  | emptyPrefix (rest : GeneralHistory graph heap physical target)
      (head : RunningHead start rest) : RunningHead start ((GeneralHistory.nil (graph := graph) (heap := heap)).append rest)

structure Tail (graph : Graph) (heap : CoreMachine.Heap) where
  physical : List CoreMachine.Frame
  target : Stack
  history : GeneralHistory graph heap physical target

noncomputable def RunningHead.tail {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {history : GeneralHistory graph heap physical target} (head : RunningHead start history) : Tail graph heap :=
  match head with
  | .running _ => ⟨[],.nil,.nil⟩
  | .append _ second earlier =>
      let tail := earlier.tail
      ⟨tail.physical ++ _,tail.target.append _,tail.history.append second⟩
  | .emptyPrefix _ earlier => earlier.tail

theorem RunningHead.physical
    {heap : CoreMachine.Heap} {physical : List CoreMachine.Frame} {target : Stack}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {history : GeneralHistory graph heap physical target} (head : RunningHead start history) :
    physical = .cleanupCompletion data.identity savedValue :: head.tail.physical := by
  induction head with
  | running receipt => rfl
  | append first second earlier ih => simp only [RunningHead.tail,ih,List.cons_append]
  | emptyPrefix rest earlier ih => simpa only [List.nil_append,RunningHead.tail] using ih

theorem RunningHead.lexical
    {heap : CoreMachine.Heap} {physical : List CoreMachine.Frame} {target : Stack}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {history : GeneralHistory graph heap physical target} (head : RunningHead start history) :
    target = .push (.running data savedCode start.running.value.closed) head.tail.target := by
  induction head with
  | running receipt => rfl
  | append first second earlier ih => simp only [RunningHead.tail,ih,Stack.append]
  | emptyPrefix rest earlier ih => simpa only [Stack.append,RunningHead.tail] using ih

/-- Changed-tail guards concern the immutable receipt's original scope path.
No future receipt or desired successor is an input. -/
inductive Activation
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (generated : Generated start current count created discharged) : List CoreMachine.Frame → Type where
  | unchanged : Activation generated originalPhysical
  | inside (same : originalPhysical = kept ++ outside)
      (position : ScopeInside generated.retained_running_receipt.installed.origin kept)
      (nextOutside : List CoreMachine.Frame) : Activation generated (kept ++ nextOutside)
  | outside (same : originalPhysical = kept ++ outside)
      (position : ScopeOutside generated.retained_running_receipt.installed.origin kept)
      (inserted : GeneralHistory graph current.state.heap added addedTarget)
      (checked : outsideCheck cleanupOwners data.scope inserted = true) :
      Activation generated (kept ++ (added ++ outside))

private theorem scope_none_inside
    {scope : Execution.Scope} (origin : CurrentScopeOrigin graph owners scope physical)
    (inactive : scope = .none) : ScopeInside origin [] := by
  cases inactive
  cases origin with
  | inactive canonical => exact .inactive canonical

/-- An originally inactive saved scope remains inactive for the computed
current tail; no physical owner search or future-origin provider is needed. -/
noncomputable def Activation.inactive
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} (generated : Generated start current count created discharged)
    (inactive : data.scope = .none) (nextOutside : List CoreMachine.Frame) :
    Activation generated nextOutside :=
  .inside (kept := []) rfl (scope_none_inside generated.retained_running_receipt.installed.origin inactive) nextOutside

theorem Activation.receipt
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {generated : Generated start current count created discharged}
    (activation : Activation generated physical) :
    RunningReceipt graph cleanupOwners current.state.heap action environment data savedValue savedCode physical :=
  match activation with
  | .unchanged => generated.retained_running_receipt
  | .inside same position nextOutside => generated.retained_running_receipt.restore_inside same position nextOutside
  | .outside same position inserted checked => CoreCallableOutsideOrigin.RunningReceipt.restore_outside_checked generated.retained_running_receipt same position inserted checked

structure FinishInput
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (generated : Generated start current count created discharged) where
  head : RunningHead start current.history
  activation : Activation generated head.tail.physical
  scope : Execution.Scope
  control : current.state.control = .returned .unit
  empty : EmptyFocus current .unit scope

noncomputable def finish_result
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {generated : Generated start current count created discharged}
    (input : FinishInput generated) : Result current [] [.cleanup data.identity] := by
  let tail := input.head.tail
  let receipt := input.activation.receipt
  let after : Endpoint graph := {
    state := observedState current.state savedValue tail.physical (.cleanupFinished data.identity)
    focus := ⟨savedCode,data.scope,.nil⟩
    owners := cleanupOwners,maps := [],physical := tail.physical,lexical := tail.target
    history := tail.history,frames := rfl }
  have actual := CoreGeneralRestoration.normal_finish (base := current.state)
    receipt.installed.delayed receipt.value tail.history.related current.owners input.scope
  have frames : current.state.frames = current.physical := by
    simpa only [input.empty.maps,framesOf,List.map_nil,List.nil_append] using current.frames
  have beforeSame : returnedState current.state .unit
      (.cleanupCompletion data.identity savedValue :: tail.physical) = current.state := by
    simp only [returnedState]
    rw [← input.head.physical,← frames,← input.control]
  refine ⟨after,?_,.positive ?_⟩
  · simpa only [beforeSame] using actual.core
  · simpa only [Endpoint.point,input.empty.focus,CoreCleanupRunFrames.attach,Stack.append,
      input.head.lexical,after,tail] using actual.target

/-- Completion is a computed phase outcome. The original active receipt is
retired rather than falsely retained in the resulting current history. -/
inductive Completed
    (start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget) :
    Endpoint graph → Nat → List Owner → List Owner → Type where
  | finish (generated : Generated start current count created discharged)
      (input : FinishInput generated) :
      Completed start (finish_result input).after (count + 1) created ([.cleanup data.identity] ++ discharged)

theorem Completed.from_actual_start
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {after : Endpoint graph} (completed : Completed start after count created discharged) :
    CoreAllocationHistory.Steps graph (count + 1) (start_before start).state after.state ∧
    CoreUnwindRelation.Trace (start_before start).point.machine after.point.machine created discharged := by
  cases completed with
  | finish generated input =>
    obtain ⟨core,target⟩ := generated.from_actual_start
    refine ⟨?_,?_⟩
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using core.snoc (finish_result input).core
    · simpa only [List.append_nil] using target.append (finish_result input).matching.target_trace

theorem Completed.accounting
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {after : Endpoint graph} (completed : Completed start after count created discharged) :
    ((started start).point.machine.stack.erase.owners ++ created).Perm
      (after.point.machine.stack.erase.owners ++ discharged) := by
  cases completed with
  | finish generated input =>
    have previous := generated.accounting
    have edge := (finish_result input).matching.accounting
    apply List.perm_iff_count.mpr
    intro owner
    have previousCount := previous.count_eq owner
    have edgeCount := edge.count_eq owner
    simp only [List.count_append,List.count_nil] at previousCount edgeCount ⊢
    omega

theorem finish_restores_saved
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {generated : Generated start current count created discharged}
    (input : FinishInput generated) :
    (finish_result input).after.state.control = .returned savedValue ∧
    (finish_result input).after.focus = ⟨savedCode,data.scope,.nil⟩ ∧
    (finish_result input).after.state.frames = input.head.tail.physical := by
  exact ⟨rfl,rfl,rfl⟩

/-- Activation scope is derived from original receipt provenance and the
explicit current tail guards. TicketBound remains an explicit current provider. -/
theorem finish_current_ownership
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    {current : Endpoint graph} {generated : Generated start current count created discharged}
    (input : FinishInput generated)
    (bounded : TicketBound current.state current.lexical) :
    CurrentOwnership graph cleanupOwners (finish_result input).after.state data.scope input.head.tail.target := by
  have receipt := input.activation.receipt
  have bound : TicketBound current.state
      (.push (.running data savedCode receipt.value.closed) input.head.tail.target) := by
    rw [← input.head.lexical]
    exact bounded
  exact (normal_finish_owned (base := current.state) receipt.installed receipt.value
    input.head.tail.history.related bound current.owners input.scope).2

#print axioms RunningHead.physical
#print axioms RunningHead.lexical
#print axioms Activation.inactive
#print axioms Activation.receipt
#print axioms finish_result
#print axioms Completed.from_actual_start
#print axioms Completed.accounting
#print axioms finish_restores_saved
#print axioms finish_current_ownership
end Ash.OneShot.CoreCallableGeneratedCleanupCompletion
