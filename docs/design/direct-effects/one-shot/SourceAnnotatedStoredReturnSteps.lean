import SourceAnnotatedStoredRetirement
import SourceAnnotatedRuntimeReturnSteps

/-! Every value return carries the exact remaining packet stack. The raw
classifier, snapshot movements and ownership accounting are reused. -/
namespace Ash.OneShot.SourceAnnotatedRuntime
open SourceConsumingStoredBounds (StackBounds)

/-- Packet movement is fixed by the actual return rule. -/
inductive ReturnPackets {families : SourceDependencyCapture.Families} :
    {before after : Configuration} → {created completed : List Owner} →
    ReturnStep before after created completed →
    StackBounds families before.stack → StackBounds families after.stack → Prop where
  | plug : ReturnPackets (.plug plain value closed scope tail) (.push .plain stored) stored
  | leaveHandler : ReturnPackets (.leaveHandler handler value closed scope tail) (.push (.handler packet) stored) stored
  | leaveCell : ReturnPackets (.leaveCell identity payload answer savedScope scope value closed tail) (.push .cell stored) stored
  | startCleanup : ReturnPackets (.startCleanup action saved closed scope tail) (.push .armed stored) (.push .running stored)
  | finishCleanup : ReturnPackets (.finishCleanup action saved closed hint scope tail) (.push .running stored) stored
  | leaveClause : ReturnPackets (.leaveClause ticket answer value closed scope callerScope tail) (.spent stored) stored
  | finishClose : ReturnPackets (.finishClose identity hint scope callerScope tail) (.push .closing stored) stored
  | retire : ReturnPackets (.retire ticket hint scope tail) (.push .retiring stored) stored

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem ReturnPackets.admitted (moved : ReturnPackets step stored nextStored)
    (admitted : stored.Admitted world required) : nextStored.Admitted world required := by
  cases moved <;> cases admitted
  all_goals first | assumption | exact .push .running (by assumption)

end Ash.OneShot.SourceAnnotatedRuntime

namespace Ash.OneShot.SourceAnnotatedStoredReturns

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
variable [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExecution (ownedTickets)
open RecursiveCompletion (retiredTickets)
open OwnerPhaseTransitions (available Trace)
open SourceAnnotatedStoredBoundaries

/-- Derive the successor from the current source state and actual annotated
return transition. Neither successor typing nor future validity is assumed. -/
theorem return_preserves_snapshot {before : SourceAnnotatedRuntime.Configuration}
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families before.stack}
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      before.scope before.expression before.stack snapshot.plan snapshot.forest output demand row stored evidence)
    (step : SourceAnnotatedRuntime.ReturnStep before next created completed) :
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families next.stack,
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack nextSnapshot.plan nextSnapshot.forest output remaining row nextStored evidence ∧
      demand = retiredTickets completed ++ remaining ∧ created = [] ∧
      Trace (available (ownedTickets before.stack.erase)) (retiredTickets completed) (available (ownedTickets next.stack.erase)) ∧
      SourceAnnotatedRuntime.ReturnBounds step snapshot nextSnapshot ∧
      SourceAnnotatedRuntime.ReturnPackets step stored nextStored := by
  cases step with
  | plug plain value closed scope tail =>
      cases stored with
      | push packet stored =>
        cases packet
        obtain ⟨nextSnapshot, _, next, moved⟩ := plug_snapshot snapshot state closed
        exact ⟨_, _, nextSnapshot, next, rfl, rfl, .nil, .plug (closed := closed) moved, .plug (closed := closed)⟩
  | leaveHandler handler value closed scope tail =>
      cases stored with
      | push packet stored =>
        cases packet
        obtain ⟨nextSnapshot, next, moved⟩ := leave_handler_snapshot snapshot state closed.1
        exact ⟨_, _, nextSnapshot, next, rfl, rfl, .nil, .leaveHandler (closed := closed) moved, .leaveHandler (closed := closed)⟩
  | leaveCell identity payload answer savedScope scope value closed tail =>
      cases stored with
      | push packet stored =>
        cases packet
        obtain ⟨nextSnapshot, next, moved⟩ := leave_cell_snapshot snapshot state closed.1
        exact ⟨_, _, nextSnapshot, next, rfl, rfl, .nil, .leaveCell (closed := closed) moved, .leaveCell (closed := closed)⟩
  | startCleanup action saved closed scope tail =>
      cases stored with
      | push packet stored =>
        cases packet
        obtain ⟨nextSnapshot, next, moved⟩ := start_cleanup_snapshot snapshot state closed
        exact ⟨_, _, nextSnapshot, next, rfl, rfl, .nil, .startCleanup (closed := closed) moved, .startCleanup (closed := closed)⟩
  | finishCleanup action saved closed hint scope tail =>
      cases stored with
      | push packet stored =>
        cases packet
        obtain ⟨nextSnapshot, next, moved⟩ := finish_cleanup_snapshot snapshot state
        exact ⟨_, _, nextSnapshot, next, rfl, rfl, .nil, .finishCleanup (closed := closed) moved, .finishCleanup (closed := closed)⟩
  | leaveClause ticket answer value closed scope callerScope tail =>
      cases stored with
      | spent stored =>
        obtain ⟨nextSnapshot, next, moved⟩ := leave_clause_snapshot snapshot state closed.1
        exact ⟨_, _, nextSnapshot, next, rfl, rfl, .nil, .leaveClause (closed := closed) moved, .leaveClause (closed := closed)⟩
  | finishClose identity hint scope callerScope tail =>
      cases stored with
      | push packet stored =>
        cases packet
        obtain ⟨nextSnapshot, next, moved⟩ := finish_close_snapshot snapshot state
        exact ⟨_, _, nextSnapshot, next, rfl, rfl, .nil, .finishClose moved, .finishClose⟩
  | retire ticket hint scope tail =>
      cases stored with
      | push packet stored =>
        cases packet
        obtain ⟨remaining, nextSnapshot, same, preserved, moved, transition⟩ :=
          SourceAnnotatedStoredRetirement.retire_snapshot snapshot state
        exact ⟨_, remaining, nextSnapshot, preserved, same, rfl, transition, .retire moved, .retire⟩
theorem raw_return_preserves_snapshot {before : SourceAnnotatedRuntime.Configuration}
    {families : SourceDependencyFrames.Families}
    {stored : SourceConsumingStoredBounds.StackBounds families before.stack}
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      before.scope before.expression before.stack snapshot.plan snapshot.forest output demand row stored evidence)
    (step : ScopedExecution.RawStep before.erase rawNext created completed)
    (isValue : before.expression.erase.IsValue) :
    ∃ next : SourceAnnotatedRuntime.Configuration,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds families next.stack, ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
      next.erase = rawNext ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack nextSnapshot.plan nextSnapshot.forest output remaining row nextStored evidence ∧
      demand = retiredTickets completed ++ remaining ∧ created = [] ∧
      Trace (available (ownedTickets before.stack.erase)) (retiredTickets completed) (available (ownedTickets next.stack.erase)) ∧
      (∃ lifted : SourceAnnotatedRuntime.ReturnStep before next created completed,
        SourceAnnotatedRuntime.ReturnBounds lifted snapshot nextSnapshot ∧
        SourceAnnotatedRuntime.ReturnPackets lifted stored nextStored) := by
  obtain ⟨next, lifted, same⟩ := SourceAnnotatedRuntime.ReturnStep.of_raw step isValue
  obtain ⟨nextStored, remaining, nextSnapshot, preserved, consumed, allocated, trace, moved, packets⟩ := return_preserves_snapshot snapshot state lifted
  exact ⟨next, nextStored, remaining, nextSnapshot, same, preserved, consumed, allocated, trace, ⟨lifted, moved, packets⟩⟩

end Ash.OneShot.SourceAnnotatedStoredReturns

#print axioms Ash.OneShot.SourceAnnotatedRuntime.ReturnPackets.admitted
#print axioms Ash.OneShot.SourceAnnotatedStoredReturns.return_preserves_snapshot
#print axioms Ash.OneShot.SourceAnnotatedStoredReturns.raw_return_preserves_snapshot
