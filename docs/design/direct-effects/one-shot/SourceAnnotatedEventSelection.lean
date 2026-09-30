import SourceAnnotatedExecutionEvents

/-! Existing source progress and annotation selection produce witnesses of the
common operational relation. Successor invariants are not selection premises. -/
namespace Ash.OneShot.SourceAnnotatedExecutionEvents
open ScopedExpressions ScopedExecution
open SourceAnnotatedRuntime (NamedState advanceState)
open SourceAnnotatedExecution (Run checkEntryPort checkEntryPort_iff checkCleanupPorts checkCleanupPorts_iff)

/-- The current source hint agrees with the port required by the actual stack. -/
theorem current_hint
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope code stack forest output demand row evidence) :
    SourceFocusHints.inputPort Instantiation.Environment.empty code.hint =
      some (SourceScheduledExecution.stackInputPort stack.erase output.erase.erase.port) := by
  cases state with
  | checked current scope pending closing templates matched contextual unique evaluated accepted accounting =>
      rw [pending.input_port]
      exact SourceFocusHints.check_source_iff.mp current.hint_checked

theorem ready_event
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound)
    (ready : RecursiveExpressions.Ready before.execution.configuration.expression.erase) :
    ∃ after, Step operations.erase.erase.ports output.erase.erase.port before after := by
  obtain ⟨rawAfter, _, _, raw, _⟩ := DeclaredSourceStates.ready_preserves run.current.source ready
  obtain ⟨code, scope, event, _, _, _⟩ := SourceAnnotatedCode.Reduction.of_raw raw ready
  exact ⟨_, .ordinary event⟩

theorem value_event
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound)
    (isValue : before.execution.configuration.expression.erase.IsValue) :
    before.execution.configuration.stack = .nil ∨
    ∃ after, Step operations.erase.erase.ports output.erase.erase.port before after := by
  rcases DeclaredSourceStates.value_progress run.current.source isValue with terminal | ⟨rawAfter, discharged, raw⟩
  · left
    change before.execution.configuration.stack.erase = .nil at terminal
    cases same : before.execution.configuration.stack <;>
      simp_all only [SourceAnnotatedRuntime.Stack.erase, reduceCtorEq]
  · obtain ⟨after, event, _⟩ := SourceAnnotatedRuntime.ReturnStep.of_raw raw isValue
    exact Or.inr ⟨_, .returned event⟩

theorem resume_event
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume hint binder value, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound)
    (isValue : value.erase.IsValue) :
    ∃ after, Step operations.erase.erase.ports output.erase.erase.port
      ⟨⟨⟨.resume hint binder value, scope, stack⟩, issued, completed⟩, activations⟩ after := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := usage
  obtain ⟨owner, resolved, same⟩ := DeclaredClosingInvariant.resume_owner code
  have present : owner ∈ activeTickets stack.erase := accessible (same ▸ List.mem_cons_self)
  obtain ⟨rawFront, input, answer, rawCapture, caller, rawTail, shape⟩ := ScopedPortJoint.active_ticket_has_boundary present
  obtain ⟨front, capture, tail, stackSame, _, _, _⟩ := SourceAnnotatedRuntime.Stack.lift_live shape
  subst stack
  exact ⟨_, .resume resolved isValue⟩

theorem discard_event
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.discard hint binder, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound) :
    ∃ after, Step operations.erase.erase.ports output.erase.erase.port
      ⟨⟨⟨.discard hint binder, scope, stack⟩, issued, completed⟩, activations⟩ after := by
  obtain ⟨after, _, _, step, _, _⟩ := DeclaredClosingInvariant.discard_progress run.erase.erase.shared.prepared
  cases step with
  | mk execution access => cases execution with
    | event after created discharged raw freshOwners freshHandlers =>
      obtain ⟨owner, identity, caller, input, answer, front, capture, tail, plan,
        stackSame, resolved, built, afterSame, createdSame, dischargedSame⟩ :=
        SourceAnnotatedRuntime.raw_discard_shape raw
      change stack = front.append (.live owner input answer capture caller tail) at stackSame
      subst stack
      subst created
      obtain ⟨annotatedPlan, actualBuilt, _⟩ := SourceAnnotatedRuntime.makePlan_of_raw capture built
      exact ⟨_, .discard resolved actualBuilt freshOwners⟩

theorem resource_event
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resource hint binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound)
    (isValue : initializer.erase.IsValue) :
    ∃ after, Step operations.erase.erase.ports output.erase.erase.port
      ⟨⟨⟨.resource hint binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩ after := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  have ports := current_hint source
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.resource (fun _ => rfl) run.current.ledger.2
  obtain ⟨_, _, _, _, initialSame, _, _⟩ := run.resource_progress isValue
  cases initializer <;> simp only [SourceAnnotatedCode.Term.erase, reduceCtorEq] at initialSame
  cases initialSame
  refine ⟨_, .resource fresh (answer := ScopedPorts.embedPort (SourceScheduledExecution.stackInputPort stack.erase output.erase.erase.port)) ?_⟩
  apply checkEntryPort_iff.mpr
  simpa only [SourceAnnotatedCode.Term.hint, ScopedPorts.erase_embed_port] using ports

theorem handler_event
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound) :
    ∃ after, Step operations.erase.erase.ports output.erase.erase.port
      ⟨⟨⟨.handle hint requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ after := by
  have retainedActivations : stack.erase.erase.activations ⊆ activations := by
    intro activation member
    exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member)
      (run.current.names.handlers activation))
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, portKnown, admitted⟩ :=
    SourceAnnotatedRuntimeHandlers.handler_annotations_exact source retainedActivations
  obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name activations
  obtain ⟨handler, saved, activationSame, typeSame, clausesSame, scopeSame, effectSame, _, _⟩ :=
    admitted activation (ScopedPorts.embedPort answerPort) fresh (by simp)
  have ports : checkEntryPort hint handler.answer = true := by
    apply checkEntryPort_iff.mpr
    simpa only [typeSame, ScopedPorts.erase_embed_port] using portKnown
  have event := Step.handler (signature := operations.erase.erase.ports) (result := output.erase.erase.port)
    (body := body) (stack := stack) (issued := issued) (completed := completed) (handler := handler)
    (activationSame ▸ fresh) ports
  exact ⟨_, by simpa only [clausesSame, scopeSame, effectSame] using event⟩

theorem cleanup_event
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound)
    (isValue : callback.erase.IsValue) :
    ∃ after, Step operations.erase.erase.ports output.erase.erase.port
      ⟨⟨⟨.cleanup hint callback body, scope, stack⟩, issued, completed⟩, activations⟩ after := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨answerPort, requests, portKnown, requestsKnown, admitted⟩ :=
    SourceAnnotatedRuntimeEntries.cleanup_annotations_exact source isValue
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.cleanup (fun _ => rfl) run.current.ledger.2
  obtain ⟨action, saved, identitySame, typeSame, declaredRequests, callbackSame, scopeSame, _, _⟩ :=
    admitted identity (ScopedPorts.embedPort answerPort) (by simp)
  have ports : checkCleanupPorts hint action = true := by
    apply checkCleanupPorts_iff.mpr
    constructor
    · simpa only [typeSame, ScopedPorts.erase_embed_port] using portKnown
    · simpa only [callbackSame, declaredRequests] using requestsKnown
  have event := Step.cleanup (signature := operations.erase.erase.ports) (result := output.erase.erase.port)
    (body := body) (stack := stack) (issued := issued) (completed := completed) (activations := activations)
    (action := action) (identitySame ▸ fresh) ports
  exact ⟨_, by simpa only [callbackSame, scopeSame] using event⟩

end Ash.OneShot.SourceAnnotatedExecutionEvents

#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.current_hint
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.ready_event
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.value_event
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.resume_event
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.discard_event
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.resource_event
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.handler_event
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.cleanup_event
