import SourceAnnotatedStoredExecution
import SourceAnnotatedStoredEntries
import SourceAnnotatedStoredResources
import SourceAnnotatedBoundAdmission

/-! Resource and cleanup entry preserve the exact installed packet stack;
existing freshness, completion and source-hint proofs select entry data. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution

theorem AtPackets.cleanup_annotations_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (isValue : callback.erase.IsValue) :
    ∃ answerPort : ScopedPorts.Port, ∃ requests,
    ∀ identity answerType, (issued ++ [Owner.cleanup identity]).Nodup → ScopedPorts.eraseType answerType = answerPort →
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      action.identity = identity ∧ action.answer = answerType ∧ action.requests = requests ∧
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) nextSnapshot.plan nextSnapshot.forest output demand row bound (.push .armed stored) evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨answerPort, requests, _, _, admitted⟩ := SourceAnnotatedStoredEntries.cleanup_annotations_exact_snapshot snapshot source isValue
  refine ⟨answerPort, requests, ?_⟩
  intro identity answerType freshOwners answerSame
  obtain ⟨action, nextSnapshot, identitySame, typeSame, requestsSame, _, _, raw, next, installed⟩ := admitted identity answerType answerSame
  rw [← identitySame] at raw freshOwners
  let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
  have results := DeclaredExecution.cleanup_step_results raw run.current.results
  have checks : AccessChecks ⟨.cleanup callback.erase body.erase, scope, stack.erase⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.cleanup callback.erase body.erase, scope, stack.erase⟩ after.erase).Nodup := by
    simpa [enteredActivations, SourceAnnotatedRuntime.NamedState.erase] using run.current.names.unique
  have actual : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.cleanup hint callback body, scope, stack⟩)
      after.erase [.cleanup action.identity] [] := raw
  refine ⟨action, nextSnapshot, identitySame, typeSame, requestsSame, ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, installed⟩
  apply assemble_entry_atPackets (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa [after, ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [after, SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

theorem AtPackets.cleanup_progress_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (isValue : callback.erase.IsValue) :
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) nextSnapshot.plan nextSnapshot.forest output demand row bound (.push .armed stored) evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot := by
  obtain ⟨answerPort, requests, admitted⟩ := AtPackets.cleanup_annotations_snapshot snapshot run isValue
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.cleanup (fun _ => rfl) run.current.ledger.2
  obtain ⟨action, nextSnapshot, _, _, _, step, next, installed⟩ := admitted identity (ScopedPorts.embedPort answerPort) fresh (by simp)
  exact ⟨action, nextSnapshot, step, next, installed⟩

theorem AtPackets.resource_entry_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (freshOwners : (issued ++ [Owner.resource identity]).Nodup)
    (ports : checkEntryPort hint answer = true) :
    ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued ++ [identity]), ∃ nextRow,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.resource identity] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.resource identity] []) nextSnapshot.plan nextSnapshot.forest output demand nextRow bound (.push .cell stored) evidence ∧
      nextRow.Sublist row ∧ SourceBoundSnapshots.EnteredResource identity snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  have freshWorld : identity ∉ ScopedTyping.resourceWorld issued := by
    intro member
    exact (List.nodup_append.mp freshOwners).2.2 (.resource identity)
      (ScopedTyping.mem_resource_world.mp member) (.resource identity) (by simp) rfl
  obtain ⟨actualPayload, nextSnapshot, nextRow, same, raw, next, included, installed⟩ :=
    SourceAnnotatedStoredResources.resource_narrowing_snapshot snapshot source (by trivial) freshWorld (checkEntryPort_iff.mp ports)
  cases Code.integer.inj same
  let after : SourceAnnotatedRuntime.Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
    .push (.cell identity payload scope answer) stack⟩
  have previousResults := run.current.results
  simp only [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
    SourceAnnotatedCode.Term.erase] at previousResults
  have results := (CompletionFrames.resource_step previousResults freshWorld (answer := answer)).2
  have checks : AccessChecks ⟨.resource binder (.integer payload) body.erase, scope, stack.erase⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.resource binder (.integer payload) body.erase, scope, stack.erase⟩ after.erase).Nodup := by
    simpa [enteredActivations, SourceAnnotatedRuntime.NamedState.erase] using run.current.names.unique
  have actual : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩)
      after.erase [.resource identity] [] := by
    simpa only [after, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedCode.Term.erase, SourceAnnotatedCode.Term.erase_instantiate] using raw
  refine ⟨nextSnapshot, nextRow, ⟨.event _ _ _ _ actual freshOwners freshHandlers, checks⟩, ?_, included, installed⟩
  apply assemble_entry_atPackets (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa [after, ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [after, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedCode.Term.erase_instantiate,
      ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

theorem AtPackets.resource_progress_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource hint binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound stored evidence)
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
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.resource identity] [])
        nextSnapshot.plan nextSnapshot.forest output demand nextRow bound (.push .cell stored) evidence ∧
      nextRow.Sublist row ∧ SourceBoundSnapshots.EnteredResource identity snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨initialHint, payload, answerPort, rfl, portKnown⟩ :=
    SourceAnnotatedRuntimeResources.resource_input_data source.atPlan.state isValue
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.resource (fun _ => rfl) run.current.ledger.2
  have ports : checkEntryPort hint (ScopedPorts.embedPort answerPort) = true := by
    apply checkEntryPort_iff.mpr
    simpa using portKnown
  obtain ⟨nextSnapshot, nextRow, step, next, included, installed⟩ :=
    AtPackets.resource_entry_snapshot snapshot run fresh ports
  exact ⟨identity, payload, _, nextSnapshot, nextRow, rfl, step, next, included, installed⟩

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem AtPackets.resource_progress_snapshot_admitted

    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource hint binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      snapshot.plan snapshot.forest output demand row bound stored evidence)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
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
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.resource identity] [])
        nextSnapshot.plan nextSnapshot.forest output demand nextRow bound (.push .cell stored) evidence ∧
      nextRow.Sublist row ∧ SourceBoundSnapshots.EnteredResource identity snapshot nextSnapshot ∧ nextSnapshot.Admitted ∧
      (SourceConsumingStoredBounds.StackBounds.push (.cell (identity := identity) (payload := payload) (caller := scope) (answer := answer)) stored).Admitted (ScopedTyping.resourceWorld issued ++ [identity]) required := by
  obtain ⟨identity, payload, answer, nextSnapshot, nextRow, same, step, typed, included, moved⟩ :=
    AtPackets.resource_progress_snapshot snapshot run isValue
  exact ⟨identity, payload, answer, nextSnapshot, nextRow, same, step, typed, included, moved, moved.admitted admitted, .push .cell (storedAdmitted.world_weaken (List.subset_append_left _ _))⟩

theorem AtPackets.cleanup_progress_snapshot_admitted

    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (isValue : callback.erase.IsValue) :
    ∃ action : SourceAnnotatedRuntime.Action, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body, scope, .push (.armed action) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.cleanup action.identity] []) nextSnapshot.plan nextSnapshot.forest output demand row bound (.push .armed stored) evidence ∧
      SourceBoundSnapshots.EnteredCleanup snapshot nextSnapshot ∧ nextSnapshot.Admitted ∧
      (SourceConsumingStoredBounds.StackBounds.push (.armed (action := action)) stored).Admitted (ScopedTyping.resourceWorld issued) required := by
  obtain ⟨action, nextSnapshot, step, typed, moved⟩ := AtPackets.cleanup_progress_snapshot snapshot run isValue
  exact ⟨action, nextSnapshot, step, typed, moved, moved.admitted admitted, .push .armed storedAdmitted⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.cleanup_annotations_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.cleanup_progress_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.resource_entry_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.resource_progress_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.resource_progress_snapshot_admitted
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.cleanup_progress_snapshot_admitted
