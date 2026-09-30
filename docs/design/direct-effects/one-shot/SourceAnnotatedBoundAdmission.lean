import SourceBoundAdmissionSteps
import SourceAnnotatedExecutionCheckedEntries

/-! Combine structural admission of persistent bound data with the existing
runtime invariant on the same successor. Evaluation, ownership, names, access
and completion reuse the established transition proofs. -/
namespace Ash.OneShot.SourceAnnotatedRuntime
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem ReturnBounds.admitted {source next : SourceBoundSnapshots.Snapshot world}
    (moved : ReturnBounds step source next) (admitted : source.Admitted) : next.Admitted := by
  cases moved with
  | plug moved => exact moved.admitted admitted
  | leaveHandler moved | leaveCell moved | finishCleanup moved | leaveClause moved | finishClose moved | retire moved =>
      exact moved.admitted admitted
  | startCleanup moved => exact moved.admitted admitted

end Ash.OneShot.SourceAnnotatedRuntime

namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open RecursiveExpressions (Ready)
open RecursiveCompletion (retiredTickets)
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

theorem AtPlan.ready_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (admitted : snapshot.Admitted)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound evidence)
    (ready : Ready before.execution.configuration.expression.erase)
    (raw : RawStep before.execution.configuration.erase rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
    ∃ remaining nextRow,
      after.erase = rawAfter ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output remaining nextRow bound evidence ∧
      (∃ reduction : SourceAnnotatedCode.Reduction before.execution.configuration.expression
          before.execution.configuration.scope after.expression after.scope,
        SourceBoundSnapshots.Computed reduction.rule snapshot next) ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ next.Admitted := by
  obtain ⟨after, next, remaining, nextRow, same, step, typed, ⟨reduction, moved⟩, permutation, included⟩ :=
    AtPlan.ready_snapshot snapshot run ready raw
  exact ⟨after, next, remaining, nextRow, same, step, typed, ⟨reduction, moved⟩, permutation, included, moved.admitted admitted⟩

theorem AtPlan.focus_snapshot_admitted {plain : SourceAnnotatedRuntime.Plain}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (position : SourceAnnotatedCode.Focus code child plain.context)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true) :
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨child, plain.scope, .push (.plain plain) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output demand row bound evidence ∧
      SourceBoundSnapshots.Focused snapshot next ∧ next.Admitted := by
  obtain ⟨next, step, typed, moved⟩ := AtPlan.focus_snapshot snapshot run position guard
  exact ⟨next, step, typed, moved, moved.admitted admitted⟩

theorem AtPlan.value_step_preserves_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (admitted : snapshot.Admitted)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations before snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : before.execution.configuration.expression.erase.IsValue)
    (raw : RawStep before.execution.configuration.erase rawAfter created discharged) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
      after.erase = rawAfter ∧
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after created discharged).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after created discharged) nextSnapshot.plan nextSnapshot.forest output remaining row bound evidence ∧
      demand = retiredTickets discharged ++ remaining ∧ created = [] ∧
      (∃ lifted : SourceAnnotatedRuntime.ReturnStep before.execution.configuration after created discharged,
        SourceAnnotatedRuntime.ReturnBounds lifted snapshot nextSnapshot) ∧ nextSnapshot.Admitted := by
  obtain ⟨after, remaining, nextSnapshot, same, step, typed, accounting, noCreated, ⟨lifted, moved⟩⟩ :=
    AtPlan.value_step_preserves_snapshot snapshot run isValue raw
  exact ⟨after, remaining, nextSnapshot, same, step, typed, accounting, noCreated, ⟨lifted, moved⟩, moved.admitted admitted⟩

theorem AtPlan.builtin_step_preserves_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : operand.erase.IsValue)
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, stack.erase⟩ rawAfter [] []) :
    ∃ after : SourceAnnotatedRuntime.Configuration, ∃ nextRow,
      after.erase = rawAfter ∧
      let nextSnapshot := SourceBoundSnapshots.Snapshot.value snapshot.pending
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) nextSnapshot.plan nextSnapshot.forest output demand nextRow bound evidence ∧ nextRow.Sublist row ∧ nextSnapshot.Admitted := by
  obtain ⟨after, nextRow, same, step, typed, included⟩ :=
    AtPlan.builtin_step_preserves_snapshot snapshot run isValue raw
  exact ⟨after, nextRow, same, step, typed, included, SourceBoundSnapshots.Snapshot.value_admitted admitted.2⟩

theorem AtPlan.resource_entry_snapshot_admitted

    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (freshOwners : (issued ++ [Owner.resource identity]).Nodup)
    (ports : checkEntryPort hint answer = true) :
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued ++ [identity]), ∃ nextRow,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.resource identity] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.resource identity] []) nextSnapshot.plan nextSnapshot.forest output demand nextRow bound evidence ∧
      nextRow.Sublist row ∧ SourceBoundSnapshots.EnteredResource identity snapshot nextSnapshot ∧ nextSnapshot.Admitted := by
  obtain ⟨nextSnapshot, nextRow, step, typed, included, moved⟩ :=
    AtPlan.resource_entry_snapshot snapshot run freshOwners ports
  exact ⟨nextSnapshot, nextRow, step, typed, included, moved, moved.admitted admitted⟩

theorem AtPlan.cleanup_entry_snapshot_admitted
    {action : SourceAnnotatedRuntime.Action}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint action.action body, action.scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (freshOwners : (issued ++ [Owner.cleanup action.identity]).Nodup)
    (ports : checkCleanupPorts hint action = true) :
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint action.action body, action.scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, action.scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) nextSnapshot.plan nextSnapshot.forest output demand row bound evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot ∧ nextSnapshot.Admitted := by
  obtain ⟨nextSnapshot, step, typed, moved⟩ := AtPlan.cleanup_entry_snapshot snapshot run freshOwners ports
  exact ⟨nextSnapshot, step, typed, moved, moved.admitted admitted⟩

theorem AtPlan.ready_progress_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued))
    (admitted : snapshot.Admitted)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      before snapshot.plan snapshot.forest output demand row bound evidence)
    (ready : Ready before.execution.configuration.expression.erase) :
    ∃ after : SourceAnnotatedRuntime.Configuration,
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld before.execution.issued),
    ∃ remaining nextRow,
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output remaining nextRow bound evidence ∧
      (∃ reduction : SourceAnnotatedCode.Reduction before.execution.configuration.expression
          before.execution.configuration.scope after.expression after.scope,
        SourceBoundSnapshots.Computed reduction.rule snapshot next) ∧
      demand.Perm remaining ∧ nextRow.Sublist row ∧ next.Admitted := by
  obtain ⟨after, next, remaining, nextRow, step, typed, ⟨reduction, moved⟩, permutation, included⟩ :=
    AtPlan.ready_progress_snapshot snapshot run ready
  exact ⟨after, next, remaining, nextRow, step, typed, ⟨reduction, moved⟩, permutation, included, moved.admitted admitted⟩

theorem AtPlan.resource_progress_snapshot_admitted

    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource hint binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : initializer.erase.IsValue) :
    ∃ identity payload answer,
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued ++ [identity]), ∃ nextRow,
      initializer.erase = .integer payload ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.resource hint binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration :=
        ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.resource identity] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.resource identity] [])
        nextSnapshot.plan nextSnapshot.forest output demand nextRow bound evidence ∧
      nextRow.Sublist row ∧ SourceBoundSnapshots.EnteredResource identity snapshot nextSnapshot ∧ nextSnapshot.Admitted := by
  obtain ⟨identity, payload, answer, nextSnapshot, nextRow, same, step, typed, included, moved⟩ :=
    AtPlan.resource_progress_snapshot snapshot run isValue
  exact ⟨identity, payload, answer, nextSnapshot, nextRow, same, step, typed, included, moved, moved.admitted admitted⟩

theorem AtPlan.cleanup_progress_snapshot_admitted

    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (isValue : callback.erase.IsValue) :
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) nextSnapshot.plan nextSnapshot.forest output demand row bound evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot ∧ nextSnapshot.Admitted := by
  obtain ⟨action, nextSnapshot, step, typed, moved⟩ := AtPlan.cleanup_progress_snapshot snapshot run isValue
  exact ⟨action, nextSnapshot, step, typed, moved, moved.admitted admitted⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedRuntime.ReturnBounds.admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.ready_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.focus_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.value_step_preserves_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.builtin_step_preserves_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.resource_entry_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.cleanup_entry_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.ready_progress_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.resource_progress_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.cleanup_progress_snapshot_admitted
