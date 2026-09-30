import SourceScheduledExecution

/-! Focus, returned values and resumption preserve the joined scheduled runtime.
Each proof combines the established source successor with runtime and completion
preservation for the same actual transition. No new control semantics are used. -/
namespace Ash.OneShot.SourceScheduledExecution
open ScopedExpressions ScopedExecution
open SourceScheduledSavedPlans (Saved)
open RecursiveCompletion (retiredTickets)
variable {front capture tail : Stack}

/-- The annotated stack supplies its incoming port; only an empty stack uses
the fixed result port of the whole execution. No code typing is run here. -/
def stackInputPort (stack : Stack) (result : ScopedPorts.Port) : ScopedPorts.Port :=
  match stack with
  | .nil => result
  | .push frame _ => ScopedPorts.eraseType frame.erase.input
  | .live _ _ answer _ _ _ | .spent _ answer _ _ => ScopedPorts.eraseType answer

theorem stack_input_port
    (typed : ScopedPorts.StackTyped signature tickets world stack input result) :
    stackInputPort stack result = input := by
  cases typed <;> rfl

/-- Four context forms determine the operand port from the result port.
Other forms need separate signature, continuation or source annotations. -/
def contextInputPort (context : Context) (output : ScopedPorts.Port) : Option ScopedPorts.Port :=
  match context, output with
  | .pairLeft _, .product left _ => some left
  | .pairRight _, .product _ right => some right
  | .branch _ _, _ => some .boolean
  | .resource _ _, _ => some .integer
  | _, _ => none

theorem context_input_port
    (typed : ScopedPorts.ContextTyped signature world environment ticket allowed context input output)
    (known : contextInputPort context output = some supplied) : supplied = input := by
  cases typed <;> simp_all [contextInputPort]

theorem focus_annotations
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound)
    (position : Focus code child context) :
    ∃ plain : PlainData,
      plain.context = context ∧ plain.scope = scope ∧
      ∀ supplied : PlainData, supplied.context = context → supplied.scope = scope →
        ScopedPorts.eraseType supplied.input = ScopedPorts.eraseType plain.input →
        ScopedPorts.eraseType supplied.output = ScopedPorts.eraseType plain.output →
      ∃ nextForest : Saved,
      let state : NamedState := ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨child, scope, .push (.plain supplied) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] []) nextForest.forest output demand row bound := by
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  obtain ⟨plain, restDependencies, restPlan, contextSame, scopeSame, admitted⟩ := SourceScheduledFocus.focus_annotations source position
  refine ⟨plain, contextSame, scopeSame, ?_⟩
  intro supplied suppliedContext suppliedScope suppliedInput suppliedOutput
  obtain ⟨raw, next⟩ := admitted supplied suppliedContext suppliedScope suppliedInput suppliedOutput
  have results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results
      (ScopedTyping.resourceWorld issued) ⟨child, scope, .push (.plain supplied) stack⟩ bound := by
    have positioned : Focus code child supplied.context := suppliedContext.symm ▸ position
    simpa only [suppliedScope] using (CompletionFrames.focus_step positioned
      (by simpa only [suppliedScope] using before.current.results)).2
  have checks := ScopedPortJoint.focus_access_checks (scope := scope) (tail := stack) (ambient := []) position
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  have freshHandlers : (activations ++ enteredActivations ⟨code, scope, stack⟩
      ⟨child, scope, .push (.plain supplied) stack⟩).Nodup := by
    simpa [focus_enters_no_activation position] using before.current.names.unique
  refine ⟨⟨_, _, .plain restPlan forest⟩, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_entry before.coherent before.current raw freshOwners freshHandlers checks usage history before.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil] using results
  · rfl
  · simp

theorem focus_progress
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound)
    (position : Focus code child context) :
    ∃ plain : PlainData, ∃ nextForest : Saved,
      plain.context = context ∧ plain.scope = scope ∧
      let state : NamedState := ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨child, scope, .push (.plain plain) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] []) nextForest.forest output demand row bound := by
  obtain ⟨plain, contextSame, scopeSame, admitted⟩ := focus_annotations before position
  obtain ⟨saved, step, next⟩ := admitted plain contextSame scopeSame rfl rfl
  exact ⟨plain, saved, contextSame, scopeSame, step, next⟩

/-- Port erasure of the retained source already authenticates the actual
plain frame and its tail. This reuses the established source-to-port theorem. -/
theorem Run.context_frame_ports
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, .push (.plain plain) stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound)
    (known : contextInputPort plain.context (stackInputPort stack output.erase.erase.port) = some input) :
    ScopedPorts.eraseType plain.input = input ∧
    ScopedPorts.eraseType plain.output = stackInputPort stack output.erase.erase.port := by
  obtain ⟨current, expression, pending⟩ := DeclaredReturnAdmission.ports run.current.source
  cases pending with
  | push frame tail =>
    have answer : stackInputPort stack output.erase.erase.port = ScopedPorts.eraseType plain.output := by
      simpa only [ExecFrame.erase, PlainData.erase] using stack_input_port tail
    cases frame with
    | plain scopeTyped contextTyped =>
      exact ⟨(context_input_port contextTyped (by simpa only [answer] using known)).symm, answer.symm⟩

/-- Matching context and stack ports suffice for these focus forms. The
generic focus proof constructs source and completion evidence internally. -/
theorem context_focus_preserves
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound)
    (position : Focus code child plain.context)
    (inputPort : contextInputPort plain.context (stackInputPort stack output.erase.erase.port) =
      some (ScopedPorts.eraseType plain.input))
    (outputPort : ScopedPorts.eraseType plain.output = stackInputPort stack output.erase.erase.port) :
    ∃ saved : Saved,
      let state : NamedState := ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨child, plain.scope, .push (.plain plain) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] []) saved.forest output demand row bound := by
  obtain ⟨reference, referenceContext, referenceScope, admitted⟩ := focus_annotations before position
  obtain ⟨referenceSaved, referenceStep, referenceRun⟩ :=
    admitted reference referenceContext referenceScope rfl rfl
  obtain ⟨referenceInput, referenceOutput⟩ := referenceRun.context_frame_ports
    (by simpa only [referenceContext] using inputPort)
  exact admitted plain rfl rfl referenceInput.symm (outputPort.trans referenceOutput.symm)

/-- A retained request context authenticates its frame ports against the fixed
operation signature. No choice of an unrelated source derivation is required. -/
theorem Run.request_frame_ports
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, .push (.plain plain) stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound)
    (context : plain.context = .perform (Instantiation.freezeEffect requested) operation)
    (known : operations.erase.erase.ports requested operation = some (input, answer)) :
    ScopedPorts.eraseType plain.input = input ∧
    ScopedPorts.eraseType plain.output = answer := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  cases source with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    cases pending with
    | push head tail effects => cases head with
      | plain sourceContext frameScope inputAnnotation outputAnnotation restChecked =>
        rw [context] at sourceContext
        generalize encoded : Instantiation.freezeEffect requested = effect at sourceContext
        generalize checkingEq : SourcePlanSignatures.signature _ = checking at sourceContext
        cases sourceContext with
        | perform actual admitted formed =>
          cases freeze_effect_injective encoded
          have declared := SourcePlannedSources.operation_erase actual
          have ports := SourceDependencyAnnotations.operation_erase declared
          have same := CoherentSourceTypes.port_lookup ports
          obtain ⟨inputSame, outputSame⟩ := Prod.mk.inj (Option.some.inj (same.symm.trans known))
          exact ⟨inputAnnotation.symm.trans inputSame, outputAnnotation.symm.trans outputSame⟩

/-- Every request-operand focus with ports supplied by the operation signature
preserves the retained invariant. The event carries no source-state proof. -/
theorem request_focus_preserves
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, plain.scope, stack⟩,
        issued, completed⟩, activations⟩ forest output demand row bound)
    (notValue : ¬ operand.IsValue)
    (context : plain.context = .perform (Instantiation.freezeEffect requested) operation)
    (known : operations.erase.erase.ports requested operation = some (input, answer))
    (inputPort : ScopedPorts.eraseType plain.input = input)
    (outputPort : ScopedPorts.eraseType plain.output = answer) :
    ∃ saved : Saved,
      let state : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand,
        plain.scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨operand, plain.scope, .push (.plain plain) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] []) saved.forest output demand row bound := by
  obtain ⟨reference, referenceContext, referenceScope, admitted⟩ := focus_annotations before (.perform notValue)
  obtain ⟨referenceSaved, referenceStep, referenceRun⟩ :=
    admitted reference referenceContext referenceScope rfl rfl
  obtain ⟨referenceInput, referenceOutput⟩ := referenceRun.request_frame_ports referenceContext known
  exact admitted plain context rfl (inputPort.trans referenceInput.symm) (outputPort.trans referenceOutput.symm)

/-- The lexical continuation reference selects the same retained contract as
the actual typed resume context. Port checking grants no action permission. -/
theorem Run.resume_frame_ports
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨code, scope, .push (.plain plain) stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound)
    (context : plain.context = .resume binder)
    (resolved : plain.scope.resolve binder = some owner)
    (known : contracts owner = some contract) :
    ScopedPorts.eraseType plain.input = contract.input.erase.erase.port ∧
    ScopedPorts.eraseType plain.output = contract.answer.erase.erase.port := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  cases source with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    cases pending with
    | push head tail effects => cases head with
      | plain sourceContext frameScope inputAnnotation outputAnnotation restChecked =>
        rw [context] at sourceContext
        generalize checkingEq : SourcePlanSignatures.signature _ = checking at sourceContext
        cases sourceContext with
        | resume actual actualResolved permission admitted formed =>
          cases Option.some.inj (actualResolved.symm.trans resolved)
          cases Option.some.inj (actual.symm.trans known)
          exact ⟨inputAnnotation.symm, outputAnnotation.symm⟩

/-- Focusing an operand retains the original one-shot state. Permission and
consumption are still established by the separate invocation checks. -/
theorem resume_focus_preserves
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume binder operand, plain.scope, stack⟩, issued, completed⟩, activations⟩
      forest output demand row bound)
    (notValue : ¬ operand.IsValue)
    (context : plain.context = .resume binder)
    (resolved : plain.scope.resolve binder = some owner)
    (known : contracts owner = some contract)
    (inputPort : ScopedPorts.eraseType plain.input = contract.input.erase.erase.port)
    (outputPort : ScopedPorts.eraseType plain.output = contract.answer.erase.erase.port) :
    ∃ saved : Saved,
      let state : NamedState := ⟨⟨⟨.resume binder operand, plain.scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨operand, plain.scope, .push (.plain plain) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] []) saved.forest output demand row bound := by
  obtain ⟨reference, referenceContext, referenceScope, admitted⟩ := focus_annotations before (.resume notValue)
  obtain ⟨referenceSaved, referenceStep, referenceRun⟩ :=
    admitted reference referenceContext referenceScope rfl rfl
  have referenceResolved : reference.scope.resolve binder = some owner := by simpa only [referenceScope] using resolved
  obtain ⟨referenceInput, referenceOutput⟩ := referenceRun.resume_frame_ports referenceContext referenceResolved known
  exact admitted plain context rfl (inputPort.trans referenceInput.symm) (outputPort.trans referenceOutput.symm)

theorem value_step_preserves
    (before : Run operations declarations policy contracts registry tables families required annotations state forest output demand row bound)
    (isValue : state.execution.configuration.expression.IsValue)
    (raw : RawStep state.execution.configuration after created discharged) :
    ∃ remaining, ∃ nextForest : Saved,
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after created discharged) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after created discharged) nextForest.forest output remaining row bound ∧
      demand = retiredTickets discharged ++ remaining ∧ created = [] := by
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  obtain ⟨remaining, nextForest, next, accounting, noCreated, trace⟩ := SourceScheduledValues.value_step_preserves source isValue raw
  subst created
  obtain ⟨oldRemaining, step, current, oldAccounting, empty⟩ :=
    DeclaredExecution.value_step_preserves before.current isValue raw
  have freshOwners : (state.execution.issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  refine ⟨remaining, nextForest, step, ?_, accounting, rfl⟩
  apply assemble_entry before.coherent before.current raw freshOwners current.names.unique step.checks usage history before.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

theorem value_progress
    (before : Run operations declarations policy contracts registry tables families required annotations state forest output demand row bound)
    (isValue : state.execution.configuration.expression.IsValue) :
    state.execution.configuration.stack = .nil ∨
    ∃ after discharged remaining, ∃ nextForest : Saved,
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] discharged) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] discharged) nextForest.forest output remaining row bound ∧
      demand = retiredTickets discharged ++ remaining := by
  rcases DeclaredSourceStates.value_progress before.current.source isValue with terminal | ⟨after, discharged, raw⟩
  · exact Or.inl terminal
  · obtain ⟨remaining, nextForest, step, next, accounting, empty⟩ := value_step_preserves before isValue raw
    exact Or.inr ⟨after, discharged, remaining, nextForest, step, next, accounting⟩

theorem resume_preserves
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ forest output demand row bound)
    (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) :
    ∃ remaining, ∃ nextForest : Saved,
      let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩
      let state : NamedState := ⟨⟨⟨.resume binder value, scope,
        front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] [.ticket owner]) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] [.ticket owner]) nextForest.forest output remaining row bound ∧
      demand = owner :: remaining := by
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  have closed := (ContinuationBounds.resume_operand_bound (environment := fun _ => .unknown)
    resolved (DeclaredReturnAdmission.ports before.current.source) isValue).1
  obtain ⟨remaining, nextForest, next, accounting, trace⟩ := SourceScheduledResumption.resume_cut_preserves source resolved closed
  obtain ⟨runtimeRemaining, step, current, runtimeAccounting⟩ := DeclaredExecution.resume_preserves before.current resolved isValue
  have raw := RawStep.resume binder owner scope caller inputType answerType front capture tail value closed resolved
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  refine ⟨remaining, nextForest, step, ?_, accounting⟩
  apply assemble_entry before.coherent before.current raw freshOwners current.names.unique step.checks
    usage history before.annotationHistory retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · exact current.results
  · rfl
  · simp

/-- Current usage determines the owner and live boundary; neither is an
additional progress premise. -/
theorem resume_progress
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound)
    (isValue : value.IsValue) :
    ∃ after owner remaining, ∃ nextForest : Saved,
      NamedAccessStep [] ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Run operations declarations policy contracts registry tables families required annotations after nextForest.forest output remaining row bound ∧
      demand = owner :: remaining := by
  obtain ⟨actions, usage, history, source, retained⟩ := before.actions
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := usage
  obtain ⟨owner, resolved, same⟩ := DeclaredClosingInvariant.resume_owner code
  have present : owner ∈ activeTickets stack := accessible (same ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := ScopedPortJoint.active_ticket_has_boundary present
  subst stack
  obtain ⟨remaining, nextForest, step, next, accounting⟩ := resume_preserves before resolved isValue
  exact ⟨_, owner, remaining, nextForest, step, next, accounting⟩


end Ash.OneShot.SourceScheduledExecution

#print axioms Ash.OneShot.SourceScheduledExecution.focus_annotations
#print axioms Ash.OneShot.SourceScheduledExecution.focus_progress
#print axioms Ash.OneShot.SourceScheduledExecution.value_step_preserves
#print axioms Ash.OneShot.SourceScheduledExecution.value_progress
#print axioms Ash.OneShot.SourceScheduledExecution.resume_preserves
#print axioms Ash.OneShot.SourceScheduledExecution.resume_progress

#print axioms Ash.OneShot.SourceScheduledExecution.Run.request_frame_ports
#print axioms Ash.OneShot.SourceScheduledExecution.request_focus_preserves

#print axioms Ash.OneShot.SourceScheduledExecution.Run.resume_frame_ports
#print axioms Ash.OneShot.SourceScheduledExecution.resume_focus_preserves

#print axioms Ash.OneShot.SourceScheduledExecution.stack_input_port
#print axioms Ash.OneShot.SourceScheduledExecution.context_input_port
#print axioms Ash.OneShot.SourceScheduledExecution.Run.context_frame_ports
#print axioms Ash.OneShot.SourceScheduledExecution.context_focus_preserves
