import SourceAnnotatedResourceEntry
import SourceAnnotatedExecutionFiniteRuns

/-! Resource entry admits every historically fresh identity through a finite
source-hint guard. Its checked effect row may narrow; no hidden support set or
successor invariant is part of the operational boundary. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceScheduledSavedPlans (Saved)

/-- Match the supplied frame answer against the actual source node's hint. -/
def checkEntryPort (hint : Instantiation.ValueType) (answer : Ty) : Bool :=
  decide (SourceFocusHints.inputPort Instantiation.Environment.empty hint = some (ScopedPorts.eraseType answer))

theorem checkEntryPort_iff : checkEntryPort hint answer = true ↔
    SourceFocusHints.inputPort Instantiation.Environment.empty hint = some (ScopedPorts.eraseType answer) := by
  simp [checkEntryPort]

/-- Every supplied fresh resource owner and passing answer annotation preserves
the shared runtime. All successor source and effect checking is derived. -/
theorem AtPlan.resource_entry_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
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
      nextRow.Sublist row ∧ SourceBoundSnapshots.EnteredResource identity snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  have freshWorld : identity ∉ ScopedTyping.resourceWorld issued := by
    intro member
    exact (List.nodup_append.mp freshOwners).2.2 (.resource identity)
      (ScopedTyping.mem_resource_world.mp member) (.resource identity) (by simp) rfl
  obtain ⟨actualPayload, nextSnapshot, nextRow, same, raw, next, included, installed⟩ :=
    SourceAnnotatedRuntimeResources.resource_narrowing_snapshot snapshot source (by trivial) freshWorld (checkEntryPort_iff.mp ports)
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
  apply assemble_entry_atPlan (after := after) run.coherent run.current actual freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa [after, ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [after, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedCode.Term.erase_instantiate,
      ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

theorem Run.resource_entry
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩,
        issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (freshOwners : (issued ++ [Owner.resource identity]).Nodup)
    (ports : checkEntryPort hint answer = true) :
    ∃ saved : Saved, ∃ nextRow,
      let before : SourceAnnotatedRuntime.NamedState :=
        ⟨⟨⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [.resource identity] []).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [.resource identity] []) saved.forest output demand nextRow bound evidence ∧
      nextRow.Sublist row := by
  obtain ⟨dependencies, plan, indexed⟩ := run.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨_, plan, .absent, _, _, forest, .absent forest⟩
  obtain ⟨nextSnapshot, nextRow, step, next, included, _⟩ :=
    AtPlan.resource_entry_snapshot snapshot indexed freshOwners ports
  exact ⟨⟨_, _, nextSnapshot.forest⟩, nextRow, step, next.run, included⟩

/-- Every ready resource source can allocate and retain the same bound evidence.
The existing freshness theorem and source hints supply all entry inputs. -/
theorem AtPlan.resource_progress_snapshot
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
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
      nextRow.Sublist row ∧ SourceBoundSnapshots.EnteredResource identity snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨initialHint, payload, answerPort, rfl, portKnown⟩ :=
    SourceAnnotatedRuntimeResources.resource_input_data source.state isValue
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.resource (fun _ => rfl) run.current.ledger.2
  have ports : checkEntryPort hint (ScopedPorts.embedPort answerPort) = true := by
    apply checkEntryPort_iff.mpr
    simpa using portKnown
  obtain ⟨nextSnapshot, nextRow, step, next, included, installed⟩ :=
    AtPlan.resource_entry_snapshot snapshot run fresh ports
  exact ⟨identity, payload, _, nextSnapshot, nextRow, rfl, step, next, included, installed⟩

namespace EntryPortExamples

theorem matching_and_wrong_answer :
    checkEntryPort .unit .unit = true ∧ checkEntryPort .unit .integer = false := by decide

theorem unresolved_resource_rejected :
    checkEntryPort (.reference (.bound 7)) (.reference 7) = false := by decide

end EntryPortExamples
end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.checkEntryPort_iff
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.resource_entry
#print axioms Ash.OneShot.SourceAnnotatedExecution.EntryPortExamples.matching_and_wrong_answer
#print axioms Ash.OneShot.SourceAnnotatedExecution.EntryPortExamples.unresolved_resource_rejected

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.resource_entry_snapshot

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.resource_progress_snapshot
