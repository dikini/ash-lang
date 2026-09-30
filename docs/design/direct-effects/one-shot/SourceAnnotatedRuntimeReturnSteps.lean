import SourceAnnotatedRuntimeRetirement

/-! Value-return transitions retain the actual annotated code and saved frames.
Their source preservation includes retirement and exact owner consumption. -/
namespace Ash.OneShot.SourceAnnotatedRuntime
open ScopedExpressions (ClosedValue)
open ScopedExecution (Scope)
open SourceAnnotatedCode (Term)

inductive ReturnStep : Configuration → Configuration → List Owner → List Owner → Prop where
  | plug (plain : Plain) (value : Term) (closed : ClosedValue value.erase) (scope : Scope) (tail : Stack) :
      ReturnStep ⟨value, scope, .push (.plain plain) tail⟩ ⟨plain.context.plug value, plain.scope, tail⟩ [] []
  | leaveHandler (handler : Handler) (value : Term) (closed : ClosedValue value.erase)
      (scope : Scope) (tail : Stack) :
      ReturnStep ⟨value, scope, .push (.handler handler) tail⟩ ⟨value, handler.scope, tail⟩ [] []
  | leaveCell (identity : Nat) (payload : Int) (answer : Ty) (savedScope scope : Scope)
      (value : Term) (closed : ClosedValue value.erase) (tail : Stack) :
      ReturnStep ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩
        ⟨value, savedScope, tail⟩ [] [.resource identity]
  | startCleanup (action : Action) (saved : Term) (closed : ClosedValue saved.erase)
      (scope : Scope) (tail : Stack) :
      ReturnStep ⟨saved, scope, .push (.armed action) tail⟩
        ⟨.app .unit action.action (.unit .unit), .none, .push (.running action saved closed) tail⟩ [] []
  | finishCleanup (action : Action) (saved : Term) (closed : ClosedValue saved.erase)
      (hint : Instantiation.ValueType) (scope : Scope) (tail : Stack) :
      ReturnStep ⟨.unit hint, scope, .push (.running action saved closed) tail⟩
        ⟨saved, action.scope, tail⟩ [] [.cleanup action.identity]
  | leaveClause (ticket : Nat) (answer : Ty) (value : Term) (closed : ClosedValue value.erase)
      (scope callerScope : Scope) (tail : Stack) :
      ReturnStep ⟨value, scope, .spent ticket answer callerScope tail⟩ ⟨value, callerScope, tail⟩ [] []
  | finishClose (identity : Nat) (hint : Instantiation.ValueType) (scope callerScope : Scope) (tail : Stack) :
      ReturnStep ⟨.unit hint, scope, .push (.closing identity callerScope) tail⟩
        ⟨.unit hint, callerScope, tail⟩ [] [.close identity]
  | retire (ticket : Nat) (hint : Instantiation.ValueType) (scope : Scope) (tail : Stack) :
      ReturnStep ⟨.unit hint, scope, .push (.retiring ticket) tail⟩ ⟨.unit hint, scope, tail⟩ [] [.ticket ticket]

/-- Each actual return rule determines the exact metadata movement. The
relation retains the same source and successor configurations as ReturnStep. -/
inductive ReturnBounds {world : List Nat} :
    {before after : Configuration} → {created completed : List Owner} →
    ReturnStep before after created completed →
    SourceBoundSnapshots.Snapshot world → SourceBoundSnapshots.Snapshot world → Prop where
  | plug (moved : SourceBoundSnapshots.Returned plain.context source next) :
      ReturnBounds (.plug plain value closed scope tail) source next
  | leaveHandler (moved : SourceBoundSnapshots.Exited .handler source next) :
      ReturnBounds (.leaveHandler handler value closed scope tail) source next
  | leaveCell (moved : SourceBoundSnapshots.Exited .cell source next) :
      ReturnBounds (.leaveCell identity payload answer savedScope scope value closed tail) source next
  | startCleanup (moved : SourceBoundSnapshots.StartedCleanup source next) :
      ReturnBounds (.startCleanup action saved closed scope tail) source next
  | finishCleanup (moved : SourceBoundSnapshots.Exited .running source next) :
      ReturnBounds (.finishCleanup action saved closed hint scope tail) source next
  | leaveClause (moved : SourceBoundSnapshots.Exited .spent source next) :
      ReturnBounds (.leaveClause ticket answer value closed scope callerScope tail) source next
  | finishClose (moved : SourceBoundSnapshots.Exited .running source next) :
      ReturnBounds (.finishClose identity hint scope callerScope tail) source next
  | retire (moved : SourceBoundSnapshots.Exited .running source next) :
      ReturnBounds (.retire ticket hint scope tail) source next

theorem ReturnStep.erase (step : ReturnStep before after created completed) :
    ScopedExecution.RawStep before.erase after.erase created completed := by
  cases step with
  | plug plain value closed scope tail => exact plug_executes plain value closed scope tail
  | leaveHandler handler value closed scope tail => exact .leaveHandler handler.erase value.erase closed scope tail.erase
  | leaveCell identity payload answer savedScope scope value closed tail =>
      exact .leaveCell identity payload answer savedScope scope value.erase closed tail.erase
  | startCleanup action saved closed scope tail => exact .startCleanup action.erase saved.erase closed scope tail.erase
  | finishCleanup action saved closed hint scope tail => exact .finishCleanup action.erase saved.erase closed scope tail.erase
  | leaveClause ticket answer value closed scope callerScope tail =>
      exact .leaveClause ticket answer value.erase closed scope callerScope tail.erase
  | finishClose identity hint scope callerScope tail => exact .finishClose identity scope callerScope tail.erase
  | retire ticket hint scope tail => exact .retire ticket scope tail.erase

/-- Every raw transition whose current expression is a value lifts to an
annotated return with exactly the same erased successor and owner events. -/
theorem ReturnStep.of_raw
    (step : ScopedExecution.RawStep before.erase rawAfter created completed)
    (isValue : before.expression.erase.IsValue) :
    ∃ after, ReturnStep before after created completed ∧ after.erase = rawAfter := by
  generalize same : before.erase = raw at step
  have rawValue : raw.expression.IsValue := by rw [← same]; exact isValue
  cases step <;> try cases rawValue
  case focus => exact False.elim (ScopedPorts.focus_is_not_value (by assumption) rawValue)
  all_goals cases before
  all_goals
    rename_i value scope stack
    cases stack <;> simp [Configuration.erase, Stack.erase] at same
  all_goals try (rename_i frame rest; cases frame <;> simp [Frame.erase] at same)
  case plug.mk.push.plain =>
    rcases same with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨_, .plug _ _ (by assumption) _ _, by simp [Configuration.erase, SourceAnnotatedCode.Context.erase_plug, Plain.erase]⟩
  case leaveHandler.mk.push.handler =>
    rcases same with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨_, .leaveHandler _ _ (by assumption) _ _, rfl⟩
  case leaveCell.mk.push.cell =>
    rcases same with ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    exact ⟨_, .leaveCell _ _ _ _ _ _ (by assumption) _, rfl⟩
  case startCleanup.mk.push.armed =>
    rcases same with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨_, .startCleanup _ _ (by assumption) _ _, rfl⟩
  case leaveClause.mk.spent =>
    rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨_, .leaveClause _ _ _ (by assumption) _ _ _, rfl⟩
  case finishCleanup.intro.mk.push.running =>
    rcases same with ⟨codeSame, rfl, ⟨rfl, rfl⟩, rfl⟩
    cases value <;> simp only [Term.erase, reduceCtorEq] at codeSame
    exact ⟨_, .finishCleanup _ _ _ _ _ _, rfl⟩
  case finishClose.intro.mk.push.closing =>
    rcases same with ⟨codeSame, rfl, ⟨rfl, rfl⟩, rfl⟩
    cases value <;> simp only [Term.erase, reduceCtorEq] at codeSame
    exact ⟨_, .finishClose _ _ _ _ _, rfl⟩
  case retire.intro.mk.push.retiring =>
    rcases same with ⟨codeSame, rfl, rfl, rfl⟩
    cases value <;> simp only [Term.erase, reduceCtorEq] at codeSame
    exact ⟨_, .retire _ _ _ _, rfl⟩

end Ash.OneShot.SourceAnnotatedRuntime

namespace Ash.OneShot.SourceAnnotatedRuntimeReturns

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
variable [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExecution (ownedTickets)
open RecursiveCompletion (retiredTickets)
open OwnerPhaseTransitions (available Trace)
open SourceAnnotatedRuntimeBoundaries

/-- Derive the successor from the current source state and actual annotated
return transition. Neither successor typing nor future validity is assumed. -/
theorem return_preserves_snapshot (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      before.scope before.expression before.stack snapshot.plan snapshot.forest output demand row evidence)
    (step : SourceAnnotatedRuntime.ReturnStep before next created completed) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack nextSnapshot.plan nextSnapshot.forest output remaining row evidence ∧
      demand = retiredTickets completed ++ remaining ∧ created = [] ∧
      Trace (available (ownedTickets before.stack.erase)) (retiredTickets completed) (available (ownedTickets next.stack.erase)) ∧
      SourceAnnotatedRuntime.ReturnBounds step snapshot nextSnapshot := by
  cases step with
  | plug plain value closed scope tail =>
      obtain ⟨nextSnapshot, _, next, moved⟩ := plug_snapshot snapshot state closed
      exact ⟨_, nextSnapshot, next, rfl, rfl, .nil, .plug (closed := closed) moved⟩
  | leaveHandler handler value closed scope tail =>
      obtain ⟨nextSnapshot, next, moved⟩ := leave_handler_snapshot snapshot state closed.1
      exact ⟨_, nextSnapshot, next, rfl, rfl, .nil, .leaveHandler (closed := closed) moved⟩
  | leaveCell identity payload answer savedScope scope value closed tail =>
      obtain ⟨nextSnapshot, next, moved⟩ := leave_cell_snapshot snapshot state closed.1
      exact ⟨_, nextSnapshot, next, rfl, rfl, .nil, .leaveCell (closed := closed) moved⟩
  | startCleanup action saved closed scope tail =>
      obtain ⟨nextSnapshot, next, moved⟩ := start_cleanup_snapshot snapshot state closed
      exact ⟨_, nextSnapshot, next, rfl, rfl, .nil, .startCleanup (closed := closed) moved⟩
  | finishCleanup action saved closed hint scope tail =>
      obtain ⟨nextSnapshot, next, moved⟩ := finish_cleanup_snapshot snapshot state
      exact ⟨_, nextSnapshot, next, rfl, rfl, .nil, .finishCleanup (closed := closed) moved⟩
  | leaveClause ticket answer value closed scope callerScope tail =>
      obtain ⟨nextSnapshot, next, moved⟩ := leave_clause_snapshot snapshot state closed.1
      exact ⟨_, nextSnapshot, next, rfl, rfl, .nil, .leaveClause (closed := closed) moved⟩
  | finishClose identity hint scope callerScope tail =>
      obtain ⟨nextSnapshot, next, moved⟩ := finish_close_snapshot snapshot state
      exact ⟨_, nextSnapshot, next, rfl, rfl, .nil, .finishClose moved⟩
  | retire ticket hint scope tail =>
      obtain ⟨remaining, nextSnapshot, same, preserved, moved, transition⟩ :=
        SourceAnnotatedRuntimeRetirement.retire_snapshot snapshot state
      exact ⟨remaining, nextSnapshot, preserved, same, rfl, transition, .retire moved⟩

theorem return_preserves
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      before.scope before.expression before.stack forest output demand row evidence)
    (step : SourceAnnotatedRuntime.ReturnStep before next created completed) :
    ∃ remaining, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack nextForest.forest output remaining row evidence ∧
      demand = retiredTickets completed ++ remaining ∧ created = [] ∧
      Trace (available (ownedTickets before.stack.erase)) (retiredTickets completed) (available (ownedTickets next.stack.erase)) := by
  cases state with
  | checked current scope pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot world :=
        ⟨_, rootPlan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
      have indexed : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
          before.scope before.expression before.stack snapshot.plan snapshot.forest output demand row evidence :=
        .checked current scope pending closing templates matched contextual unique evaluated accepted accounting
      obtain ⟨remaining, nextSnapshot, next, consumed, allocated, trace, _⟩ := return_preserves_snapshot snapshot indexed step
      exact ⟨remaining, ⟨_, _, nextSnapshot.forest⟩, next.state, consumed, allocated, trace⟩

/-- Exhaustive preservation for the original machine's returned-value steps.
The annotated successor is constructed and erases to the given raw successor. -/
theorem raw_return_preserves_snapshot {before : SourceAnnotatedRuntime.Configuration}
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      before.scope before.expression before.stack snapshot.plan snapshot.forest output demand row evidence)
    (step : ScopedExecution.RawStep before.erase rawNext created completed)
    (isValue : before.expression.erase.IsValue) :
    ∃ next : SourceAnnotatedRuntime.Configuration, ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
      next.erase = rawNext ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack nextSnapshot.plan nextSnapshot.forest output remaining row evidence ∧
      demand = retiredTickets completed ++ remaining ∧ created = [] ∧
      Trace (available (ownedTickets before.stack.erase)) (retiredTickets completed) (available (ownedTickets next.stack.erase)) ∧
      (∃ lifted : SourceAnnotatedRuntime.ReturnStep before next created completed,
        SourceAnnotatedRuntime.ReturnBounds lifted snapshot nextSnapshot) := by
  obtain ⟨next, lifted, same⟩ := SourceAnnotatedRuntime.ReturnStep.of_raw step isValue
  obtain ⟨remaining, nextSnapshot, preserved, consumed, allocated, trace, moved⟩ := return_preserves_snapshot snapshot state lifted
  exact ⟨next, remaining, nextSnapshot, same, preserved, consumed, allocated, trace, ⟨lifted, moved⟩⟩

theorem raw_return_preserves {before : SourceAnnotatedRuntime.Configuration}
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      before.scope before.expression before.stack forest output demand row evidence)
    (step : ScopedExecution.RawStep before.erase rawNext created completed)
    (isValue : before.expression.erase.IsValue) :
    ∃ next : SourceAnnotatedRuntime.Configuration, ∃ remaining, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      next.erase = rawNext ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        next.scope next.expression next.stack nextForest.forest output remaining row evidence ∧
      demand = retiredTickets completed ++ remaining ∧ created = [] ∧
      Trace (available (ownedTickets before.stack.erase)) (retiredTickets completed) (available (ownedTickets next.stack.erase)) := by
  cases state with
  | checked current scope pending closing templates matched contextual unique evaluated accepted accounting =>
      rename_i rootPlan
      let snapshot : SourceBoundSnapshots.Snapshot world :=
        ⟨_, rootPlan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
      have indexed : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
          before.scope before.expression before.stack snapshot.plan snapshot.forest output demand row evidence :=
        .checked current scope pending closing templates matched contextual unique evaluated accepted accounting
      obtain ⟨next, remaining, nextSnapshot, same, preserved, consumed, allocated, trace, _⟩ :=
        raw_return_preserves_snapshot snapshot indexed step isValue
      exact ⟨next, remaining, ⟨_, _, nextSnapshot.forest⟩, same, preserved.state, consumed, allocated, trace⟩

end Ash.OneShot.SourceAnnotatedRuntimeReturns

#print axioms Ash.OneShot.SourceAnnotatedRuntime.ReturnStep.erase
#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.return_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntime.ReturnStep.of_raw

#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.raw_return_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.return_preserves_snapshot
#print axioms Ash.OneShot.SourceAnnotatedRuntimeReturns.raw_return_preserves_snapshot
