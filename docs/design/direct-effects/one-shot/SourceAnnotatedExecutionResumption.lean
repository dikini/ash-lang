import SourceAnnotatedExecutionStable

/-! One-shot resumption restores the actual annotated capture under every
caller prefix. Existing runtime proofs supply completion and access checks. -/
namespace Ash.OneShot.SourceAnnotatedExecution

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution
open SourceScheduledSavedPlans (Saved)
variable {front capture tail : SourceAnnotatedRuntime.Stack}

/-- Resumption preserves the common runtime at every actual annotated live
cut and consumes the selected continuation owner exactly once. -/
theorem AtPlan.resume_preserves_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued))
    (run : AtPlan operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ snapshot.plan snapshot.forest output demand row bound evidence)
    (resolved : scope.resolve binder = some owner) (isValue : value.erase.IsValue) :
    ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued),
      let after : SourceAnnotatedRuntime.Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨.resume hint binder value, scope,
        front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]).erase ∧
      AtPlan operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]) nextSnapshot.plan nextSnapshot.forest output remaining row bound evidence ∧
      demand = owner :: remaining ∧
      SourceBoundSnapshots.Resumed owner snapshot nextSnapshot := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  have previous := run.current
  simp only [SourceAnnotatedRuntime.NamedState.erase, SourceAnnotatedRuntime.Configuration.erase,
    SourceAnnotatedCode.Term.erase, SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] at previous
  have closed := (ContinuationBounds.resume_operand_bound (environment := fun _ => .unknown)
    resolved (DeclaredReturnAdmission.ports previous.source) isValue).1
  obtain ⟨remaining, nextSnapshot, next, accounting, trace, moved⟩ := SourceAnnotatedRuntimeResumption.resume_cut_preserves_snapshot snapshot source resolved closed
  obtain ⟨runtimeRemaining, step, current, runtimeAccounting⟩ := DeclaredExecution.resume_preserves previous resolved isValue
  have raw : RawStep
      (SourceAnnotatedRuntime.Configuration.erase ⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩)
      (SourceAnnotatedRuntime.Configuration.erase ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩)
      [] [.ticket owner] := by
    simpa only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using
      RawStep.resume binder owner scope caller inputType answerType front.erase capture.erase tail.erase value.erase closed resolved
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using previous.ledger.2
  have joined := assemble_entry_atPlan run.coherent run.current raw freshOwners
    (by simpa only [ScopedPortJoint.advanceState, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using current.names.unique)
    (by simpa only [SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using step.checks)
    usage history run.annotationHistory retained
    (by simpa only [ScopedActionUsage.advance, List.append_nil] using next)
    (by simpa only [ScopedPortJoint.advanceState, SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
      SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using current.results)
    rfl (by simp)
  refine ⟨remaining, nextSnapshot, ?_, joined, accounting, moved⟩
  simpa only [SourceAnnotatedRuntime.advanceState, ScopedPortJoint.advanceState, SourceAnnotatedRuntime.NamedState.erase,
    SourceAnnotatedRuntime.Configuration.erase, SourceAnnotatedCode.Term.erase,
    SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using step

theorem Run.resume_preserves
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (resolved : scope.resolve binder = some owner) (isValue : value.erase.IsValue) :
    ∃ remaining, ∃ saved : Saved,
      let after : SourceAnnotatedRuntime.Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
      let before : SourceAnnotatedRuntime.NamedState := ⟨⟨⟨.resume hint binder value, scope,
        front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] before.erase (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]).erase ∧
      Run operations declarations policy contracts registry tables families required annotations
        (SourceAnnotatedRuntime.advanceState before after [] [.ticket owner]) saved.forest output remaining row bound evidence ∧
      demand = owner :: remaining := by
  obtain ⟨dependencies, plan, indexed⟩ := run.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot (ScopedTyping.resourceWorld issued) :=
    ⟨dependencies, plan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
  obtain ⟨remaining, nextSnapshot, step, next, accounting, _⟩ :=
    AtPlan.resume_preserves_snapshot snapshot indexed resolved isValue
  exact ⟨remaining, ⟨_, _, nextSnapshot.forest⟩, step, next.run, accounting⟩

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- Usage and accessibility locate the live cut; lifting that physical cut
retains the actual annotations and requires no extra source admission. -/
theorem Run.resume_location
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound evidence) :
    ∃ owner, ∃ front capture tail : SourceAnnotatedRuntime.Stack, ∃ input answer caller,
      scope.resolve binder = some owner ∧ stack = front.append (.live owner input answer capture caller tail) := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := usage
  obtain ⟨owner, resolved, same⟩ := DeclaredClosingInvariant.resume_owner code
  have present : owner ∈ activeTickets stack.erase := accessible (same ▸ List.mem_cons_self)
  obtain ⟨rawFront, input, answer, rawCapture, caller, rawTail, shape⟩ := ScopedPortJoint.active_ticket_has_boundary present
  obtain ⟨front, capture, tail, stackSame, _, _, _⟩ := SourceAnnotatedRuntime.Stack.lift_live shape
  exact ⟨owner, front, capture, tail, input, answer, caller, resolved, stackSame⟩

theorem Run.resume_progress
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound evidence)
    (isValue : value.erase.IsValue) :
    ∃ after : SourceAnnotatedRuntime.NamedState, ∃ owner remaining, ∃ saved : Saved,
      NamedAccessStep []
        (SourceAnnotatedRuntime.NamedState.erase ⟨⟨⟨.resume hint binder value, scope, stack⟩, issued, completed⟩, activations⟩) after.erase ∧
      Run operations declarations policy contracts registry tables families required annotations after saved.forest output remaining row bound evidence ∧
      demand = owner :: remaining := by
  obtain ⟨owner, front, capture, tail, input, answer, caller, resolved, stackSame⟩ := run.resume_location
  subst stack
  obtain ⟨remaining, saved, step, next, accounting⟩ := run.resume_preserves resolved isValue
  exact ⟨_, owner, remaining, saved, step, next, accounting⟩

end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.resume_preserves
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.resume_progress

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.resume_preserves_snapshot
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.resume_location
