import SourceAnnotatedStoredExecution
import SourceAnnotatedStoredFocus
import SourceAnnotatedExecutionFocus

/-! All ten annotated focus positions share one finite port guard and the same
runtime ownership, name, access, usage and completion invariants. -/
namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution
open SourceScheduledSavedPlans (Saved)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Every supplied annotated focus frame passing the finite guard preserves
the shared runtime. No transition premise assumes successor source typing. -/
theorem AtPackets.focus_preserves_bounds {plain : SourceAnnotatedRuntime.Plain}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (position : SourceAnnotatedCode.Focus code child plain.context)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true) :
    ∃ childDependencies restDependencies,
    ∃ childPlan : SourceDeclarationPlans.Plan childDependencies,
    ∃ restPlan : SourceDeclarationPlans.Plan restDependencies,
    ∃ childBounds : SourcePlanBounds.Annotation (ScopedTyping.resourceWorld issued) childPlan,
    ∃ restBounds : SourcePlanBounds.Annotation (ScopedTyping.resourceWorld issued) restPlan,
      let next := snapshot.focus childPlan restPlan childBounds restBounds
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨child, plain.scope, .push (.plain plain) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output demand row bound (.push .plain stored) evidence ∧
      SourcePlanBounds.Focused (ScopedTyping.resourceWorld issued) snapshot.current childBounds restBounds := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨childDependencies, restDependencies, childPlan, restPlan, childBounds, restBounds, raw, next, selected⟩ :=
    SourceAnnotatedStoredFocus.focus_snapshot snapshot source position guard
  have previousResults := run.current.results
  simp only [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase] at previousResults
  have results := (CompletionFrames.focus_step (plain := plain.erase) position.erase previousResults).2
  have checks := ScopedPortJoint.focus_access_checks (scope := plain.scope) (tail := stack.erase) (ambient := []) position.erase
  have freshOwners : (issued ++ []).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, RunState.erase] using run.current.ledger.2
  have freshHandlers : (activations ++ enteredActivations
      (SourceAnnotatedRuntime.Configuration.erase ⟨code, plain.scope, stack⟩)
      (SourceAnnotatedRuntime.Configuration.erase ⟨child, plain.scope, .push (.plain plain) stack⟩)).Nodup := by
    simpa [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
      SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase,
      focus_enters_no_activation position.erase] using run.current.names.unique
  refine ⟨_, _, childPlan, restPlan, childBounds, restBounds,
    ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_, selected⟩
  apply assemble_entry_atPackets run.coherent run.current raw freshOwners freshHandlers checks usage history run.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, SourceAnnotatedRuntime.Plain.erase] using results
  · rfl
  · simp

theorem AtPackets.focus_snapshot {plain : SourceAnnotatedRuntime.Plain}
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (position : SourceAnnotatedCode.Focus code child plain.context)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true) :
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨child, plain.scope, .push (.plain plain) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output demand row bound (.push .plain stored) evidence ∧
      SourceBoundSnapshots.Focused snapshot next := by
  obtain ⟨_, _, childPlan, restPlan, childBounds, restBounds, step, next, selected⟩ :=
    AtPackets.focus_preserves_bounds snapshot run position guard
  exact ⟨snapshot.focus childPlan restPlan childBounds restBounds, step, next,
    .step snapshot childBounds restBounds selected⟩

/-- Source hints derive the focus guard for every annotated focus form. The
snapshot adds no new readiness premise. -/
theorem AtPackets.focus_progress_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (position : SourceAnnotatedCode.Focus code child context) :
    ∃ plain : SourceAnnotatedRuntime.Plain,
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      plain.context = context ∧ plain.scope = scope ∧
      SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true ∧
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨child, scope, .push (.plain plain) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output demand row bound (.push .plain stored) evidence ∧
      SourceBoundSnapshots.Focused snapshot next := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨plain, _, _, contextSame, scopeSame, guard, _, _⟩ :=
    SourceAnnotatedRuntimeFocus.focus_progress source.atPlan.state position
  dsimp only at scopeSame
  subst scope
  obtain ⟨next, step, successor, selected⟩ := AtPackets.focus_snapshot (plain := plain) snapshot
    run (contextSame.symm ▸ position) guard
  exact ⟨plain, next, contextSame, rfl, guard, step, successor, selected⟩

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem AtPackets.focus_progress_snapshot_admitted
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (admitted : snapshot.Admitted)
    (run : AtPackets operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound stored evidence)
    (storedAdmitted : stored.Admitted (ScopedTyping.resourceWorld issued) required)
    (position : SourceAnnotatedCode.Focus code child context) :
    ∃ plain : SourceAnnotatedRuntime.Plain,
    ∃ next : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      plain.context = context ∧ plain.scope = scope ∧
      SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true ∧
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
      let after : SourceAnnotatedRuntime.Configuration := ⟨child, scope, .push (.plain plain) stack⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] []).erase ∧
      AtPackets operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] []) next.plan next.forest output demand row bound (.push .plain stored) evidence ∧
      SourceBoundSnapshots.Focused snapshot next ∧ next.Admitted ∧
      (SourceConsumingStoredBounds.StackBounds.push (.plain (data := plain)) stored).Admitted (ScopedTyping.resourceWorld issued) required := by
  obtain ⟨plain, next, contextSame, scopeSame, guard, step, successor, selected⟩ :=
    AtPackets.focus_progress_snapshot snapshot run position
  exact ⟨plain, next, contextSame, scopeSame, guard, step, successor, selected,
    selected.admitted admitted, .push .plain storedAdmitted⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.focus_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.focus_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.focus_progress_snapshot

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPackets.focus_progress_snapshot_admitted
