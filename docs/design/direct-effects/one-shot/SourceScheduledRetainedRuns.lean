import SourceScheduledFiniteRuns
import CallableRuns

/-! Stable events, checked disposal and six authenticated focus forms preserve
the scheduled invariant. Events never contain a successor invariant. Application,
binding and cleanup focusing, installation and capture still need integration. -/
namespace Ash.OneShot.SourceScheduledExecution
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Saved)

/-- Reuse the established value, ordinary computation, builtin and resumption
proofs for an arbitrary event supplied independently of the invariant. -/
theorem stable_preserves
    (before : Run operations declarations policy contracts registry tables families required annotations
      state forest output demand row bound)
    (event : CallableRuns.StableEvent state.execution.configuration after discharged) :
    ∃ nextForest : Saved, ∃ remaining nextRow,
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] discharged) ∧
      Run operations declarations policy contracts registry tables families required annotations
        (ScopedPortJoint.advanceState state after [] discharged) nextForest.forest output remaining nextRow bound ∧
      nextRow.Sublist row := by
  obtain ⟨⟨configuration, issued, completed⟩, activations⟩ := state
  cases event with
  | value raw isValue =>
      obtain ⟨remaining, saved, step, next, _⟩ := value_step_preserves before isValue raw
      exact ⟨saved, remaining, _, step, next, .refl _⟩
  | ordinary ordinary =>
      have raw := ScopedPortJoint.ordinary_step_executes ordinary
      cases ordinary with
      | bind closed environment =>
          obtain ⟨remaining, nextRow, step, next, _, included⟩ := ready_preserves before (.bind closed.1) raw
          exact ⟨⟨_, _, forest⟩, remaining, nextRow, step, next, included⟩
      | beta closed closure =>
          obtain ⟨remaining, nextRow, step, next, _, included⟩ := ready_preserves before (.app closed.1) raw
          exact ⟨⟨_, _, forest⟩, remaining, nextRow, step, next, included⟩
      | ifTrue | ifFalse =>
          obtain ⟨remaining, nextRow, step, next, _, included⟩ := ready_preserves before .branch raw
          exact ⟨⟨_, _, forest⟩, remaining, nextRow, step, next, included⟩
      | read selected =>
          obtain ⟨nextRow, step, next, included⟩ := builtin_step_preserves before trivial raw
          exact ⟨⟨_, _, forest⟩, demand, nextRow, step, next, included⟩
      | write selected =>
          obtain ⟨nextRow, step, next, included⟩ := builtin_step_preserves before ⟨trivial, trivial⟩ raw
          exact ⟨⟨_, _, forest⟩, demand, nextRow, step, next, included⟩
  | resume closed resolved =>
      obtain ⟨remaining, saved, step, next, _⟩ := resume_preserves before resolved closed.1
      exact ⟨saved, remaining, _, step, next, .refl _⟩

/-- The signature supplies both ports. Comparing their erased finite data
requires no typing derivation or future-state certificate in an event. -/
def checkRequestPorts (operations : SourcePlannedTyping.Operations) (requested : Instance)
    (operation : Nat) (plain : PlainData) : Bool :=
  decide (operations.erase.erase.ports requested operation =
    some (ScopedPorts.eraseType plain.input, ScopedPorts.eraseType plain.output))

theorem checkRequestPorts_iff : checkRequestPorts operations requested operation plain = true ↔
    operations.erase.erase.ports requested operation =
      some (ScopedPorts.eraseType plain.input, ScopedPorts.eraseType plain.output) := by
  simp [checkRequestPorts]

/-- Resolve the lexical continuation before reading its contract. These port
checks do not grant resume rights or make a consumed owner available. -/
def checkResumePorts (contracts : SourcePlannedTyping.Contracts) (binder : Nat) (plain : PlainData) : Bool :=
  match plain.scope.resolve binder with
  | none => false
  | some owner => match contracts owner with
    | none => false
    | some contract => decide (ScopedPorts.eraseType plain.input = contract.input.erase.erase.port ∧
        ScopedPorts.eraseType plain.output = contract.answer.erase.erase.port)

theorem checkResumePorts_iff : checkResumePorts contracts binder plain = true ↔
    ∃ owner contract, plain.scope.resolve binder = some owner ∧ contracts owner = some contract ∧
      ScopedPorts.eraseType plain.input = contract.input.erase.erase.port ∧
      ScopedPorts.eraseType plain.output = contract.answer.erase.erase.port := by
  cases resolved : plain.scope.resolve binder with
  | none => simp [checkResumePorts, resolved]
  | some owner => cases known : contracts owner with
    | none => simp [checkResumePorts, resolved, known]
    | some contract => simp [checkResumePorts, resolved, known]

/-- The execution result port and actual stack fix the context's result.
The four supported context forms then determine the operand port. -/
def checkContextPorts (result : ScopedPorts.Port) (stack : Stack) (plain : PlainData) : Bool :=
  decide (contextInputPort plain.context (stackInputPort stack result) = some (ScopedPorts.eraseType plain.input) ∧
    ScopedPorts.eraseType plain.output = stackInputPort stack result)

theorem checkContextPorts_iff : checkContextPorts result stack plain = true ↔
    contextInputPort plain.context (stackInputPort stack result) = some (ScopedPorts.eraseType plain.input) ∧
    ScopedPorts.eraseType plain.output = stackInputPort stack result := by
  simp [checkContextPorts]

/-- These events retain the source metadata registries. Stable events reuse the
existing grammar. Disposal supplies an actual named/access-checked transition.
Focus ports come from signatures, continuation contracts, or context and stack
shape. The fixed result port is the erased initial result type. Successor source
and closing-plan typing are derived from the invariant. -/
inductive RetainedStep (operations : SourcePlannedTyping.Operations) (contracts : SourcePlannedTyping.Contracts) (result : ScopedPorts.Port) : NamedState → NamedState → Prop where
  | stable (event : CallableRuns.StableEvent before.execution.configuration configuration discharged) :
      RetainedStep operations contracts result before (ScopedPortJoint.advanceState before configuration [] discharged)
  | discard (event : NamedAccessStep []
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after) :
      RetainedStep operations contracts result ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after

  | focusRequest (notValue : ¬ operand.IsValue)
      (context : plain.context = .perform (Instantiation.freezeEffect requested) operation)
      (ports : checkRequestPorts operations requested operation plain = true) :
      RetainedStep operations contracts result
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, plain.scope, stack⟩,
          issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, plain.scope, stack⟩,
            issued, completed⟩, activations⟩
          ⟨operand, plain.scope, .push (.plain plain) stack⟩ [] [])

  | focusResume (notValue : ¬ operand.IsValue)
      (context : plain.context = .resume binder)
      (ports : checkResumePorts contracts binder plain = true) :
      RetainedStep operations contracts result
        ⟨⟨⟨.resume binder operand, plain.scope, stack⟩, issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨.resume binder operand, plain.scope, stack⟩, issued, completed⟩, activations⟩
          ⟨operand, plain.scope, .push (.plain plain) stack⟩ [] [])

  | focusContext (position : Focus code child plain.context)
      (ports : checkContextPorts result stack plain = true) :
      RetainedStep operations contracts result
        ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩
        (ScopedPortJoint.advanceState
          ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩
          ⟨child, plain.scope, .push (.plain plain) stack⟩ [] [])

theorem retained_step_preserves {output : SourcePlannedTyping.Value}
    (step : RetainedStep operations contracts output.erase.erase.port state after)
    (before : Run operations declarations policy contracts registry tables families required annotations
      state forest output demand row bound) :
    NamedAccessStep [] state after ∧
    ∃ saved : Saved, ∃ remaining nextRow,
      Run operations declarations policy contracts registry tables families required annotations
        after saved.forest output remaining nextRow bound ∧ nextRow.Sublist row := by
  cases step with
  | stable event =>
      obtain ⟨saved, remaining, nextRow, executed, next, included⟩ := stable_preserves before event
      exact ⟨executed, saved, remaining, nextRow, next, included⟩
  | discard event =>
      obtain ⟨owner, remaining, saved, next, accounting⟩ := before.discard_preserves event
      exact ⟨event, saved, remaining, row, next, .refl _⟩
  | focusRequest notValue context ports =>
      obtain ⟨saved, executed, next⟩ := request_focus_preserves before notValue context
        (checkRequestPorts_iff.mp ports) rfl rfl
      exact ⟨executed, saved, _, _, next, .refl _⟩
  | focusResume notValue context ports =>
      obtain ⟨owner, contract, resolved, known, inputPort, outputPort⟩ := checkResumePorts_iff.mp ports
      obtain ⟨saved, executed, next⟩ := resume_focus_preserves before notValue context resolved known inputPort outputPort
      exact ⟨executed, saved, _, _, next, .refl _⟩
  | focusContext position ports =>
      obtain ⟨inputPort, outputPort⟩ := checkContextPorts_iff.mp ports
      obtain ⟨saved, executed, next⟩ := context_focus_preserves before position inputPort outputPort
      exact ⟨executed, saved, _, _, next, .refl _⟩

/-- Ordinary transitive-closure induction preserves the complete retained
invariant along every nonempty finite execution of these events. The trace carries no
intermediate validity evidence. -/
theorem retained_run_preserves {output : SourcePlannedTyping.Value}
    (steps : Relation.TransGen (RetainedStep operations contracts output.erase.erase.port) state after)
    {hints : Hints receiving} {forest : Forest hints}
    (before : Run operations declarations policy contracts registry tables families required annotations
      state forest output demand row bound) :
    Relation.TransGen (NamedAccessStep []) state after ∧
    ∃ saved : Saved, ∃ remaining nextRow,
      Run operations declarations policy contracts registry tables families required annotations
        after saved.forest output remaining nextRow bound ∧ nextRow.Sublist row := by
  induction steps with
  | single step =>
      obtain ⟨executed, saved, remaining, nextRow, next, included⟩ := retained_step_preserves step before
      exact ⟨.single executed, saved, remaining, nextRow, next, included⟩
  | tail steps step ih =>
      obtain ⟨executed, saved, remaining, nextRow, next, included⟩ := ih
      obtain ⟨last, finalSaved, finalDemand, finalRow, final, finalIncluded⟩ := retained_step_preserves step next
      exact ⟨.tail executed last, finalSaved, finalDemand, finalRow, final, finalIncluded.trans included⟩

namespace RequestFocusExamples

def readContext : PlainData :=
  ⟨.perform (Instantiation.freezeEffect (.cell 7)) 0, .none, .reference 7, .integer, [], rfl⟩
def operand : Code := .bind 0 .unit (.resourceRef (.activation 7))
def request (value : Code) : Code := .perform (Instantiation.freezeEffect (.cell 7)) 0 value

theorem correct_ports : checkRequestPorts InitialAdmissionExamples.operations (.cell 7) 0 readContext = true := by decide

theorem wrong_input_rejected :
    checkRequestPorts InitialAdmissionExamples.operations (.cell 7) 0 { readContext with input := .unit } = false := by decide

theorem wrong_output_rejected :
    checkRequestPorts InitialAdmissionExamples.operations (.cell 7) 0 { readContext with output := .unit } = false := by decide

/-- Request focusing interleaves with ordinary binding and return-to-context
without attaching an invariant to any intermediate trace node. -/
theorem focus_bind_plug : Relation.TransGen (RetainedStep InitialAdmissionExamples.operations contracts result)
    ⟨⟨⟨request operand, .none, stack⟩, issued, completed⟩, activations⟩
    ⟨⟨⟨request (.resourceRef (.activation 7)), .none, stack⟩, issued, completed⟩, activations⟩ := by
  let focused : NamedState := ⟨⟨⟨operand, .none, .push (.plain readContext) stack⟩, issued, completed⟩, activations⟩
  let returned : NamedState := ⟨⟨⟨.resourceRef (.activation 7), .none, .push (.plain readContext) stack⟩,
    issued, completed⟩, activations⟩
  have first : RetainedStep InitialAdmissionExamples.operations contracts result
      ⟨⟨⟨request operand, .none, stack⟩, issued, completed⟩, activations⟩ focused := by
    simpa [ScopedPortJoint.advanceState, enteredActivations, focused, request, readContext] using
      (RetainedStep.focusRequest (result := result) (contracts := contracts) (stack := stack) (issued := issued) (completed := completed) (activations := activations)
        (plain := readContext) (operand := operand) (by simp [operand, Code.IsValue]) rfl correct_ports)
  have middle : RetainedStep InitialAdmissionExamples.operations contracts result focused returned := by
    have raw : ScopedPortJoint.OrdinaryStep focused.execution.configuration returned.execution.configuration :=
      .bind ⟨trivial, rfl, by intro dependency member; cases member⟩ (by intro name member; cases List.mem_singleton.mp member)
    simpa [ScopedPortJoint.advanceState, enteredActivations, focused, returned, operand] using
      (RetainedStep.stable (result := result) (operations := InitialAdmissionExamples.operations) (contracts := contracts) (before := focused) (.ordinary raw))
  have last : RetainedStep InitialAdmissionExamples.operations contracts result returned
      ⟨⟨⟨request (.resourceRef (.activation 7)), .none, stack⟩, issued, completed⟩, activations⟩ := by
    have closed : ClosedValue (.resourceRef (.activation 7)) :=
      ⟨trivial, rfl, by intro dependency member; cases List.mem_singleton.mp member; trivial⟩
    simpa [ScopedPortJoint.advanceState, enteredActivations, returned, readContext, request, Context.plug] using
      (RetainedStep.stable (result := result) (operations := InitialAdmissionExamples.operations) (contracts := contracts) (before := returned)
        (.value (RawStep.plug readContext _ closed .none stack) trivial))
  exact .tail (.tail (.single first) middle) last

/-- The same common finite-execution theorem now covers the mixed trace. -/
theorem focused_trace_preserves
    (before : Run InitialAdmissionExamples.operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨request operand, .none, stack⟩, issued, completed⟩, activations⟩ forest output demand row bound) :
    ∃ saved : Saved, ∃ remaining nextRow,
      Run InitialAdmissionExamples.operations declarations policy contracts registry tables families required annotations
        ⟨⟨⟨request (.resourceRef (.activation 7)), .none, stack⟩, issued, completed⟩, activations⟩
        saved.forest output remaining nextRow bound ∧ nextRow.Sublist row :=
  (retained_run_preserves focus_bind_plug before).2

end RequestFocusExamples

namespace ResumeFocusExamples

def contract : SourcePlannedTyping.Contract := ⟨.unit, .unit, false, [], [], [], some [], [], []⟩
def contracts : SourcePlannedTyping.Contracts := fun owner => if owner = 19 then some contract else none
def resumeContext : PlainData := ⟨.resume 9, .ticket 9 19, .unit, .unit, [19], rfl⟩
def operand : Code := .bind 0 .unit .unit

theorem correct_ports : checkResumePorts contracts 9 resumeContext = true := by decide

theorem unresolved_binder_rejected : checkResumePorts contracts 8 resumeContext = false := by decide

theorem missing_contract_rejected : checkResumePorts (fun _ => none) 9 resumeContext = false := by decide

theorem wrong_ports_rejected :
    checkResumePorts contracts 9 { resumeContext with input := .integer } = false ∧
    checkResumePorts contracts 9 { resumeContext with output := .integer } = false := by decide

/-- Matching a continuation's port contract does not restore its one-shot
permission after consumption. Reuse the established phase rejection theorem. -/
theorem ports_do_not_revive_owner : checkResumePorts contracts 9 resumeContext = true ∧
    ¬ SourceDependencySchemes.Checked outward actions (OwnerPhaseTransitions.spend phases 19) world
      (.invoke ⟨19, .resume⟩) receiving :=
  ⟨correct_ports, SourceDependencySchemes.Examples.consumed_resume_rejected⟩

/-- The pending resume keeps its lexical owner reference while the operand
uses ordinary binding. No invariant is a field of the three-event trace. -/
theorem focus_bind_plug : Relation.TransGen (RetainedStep operations contracts result)
    ⟨⟨⟨.resume 9 operand, .ticket 9 19, stack⟩, issued, completed⟩, activations⟩
    ⟨⟨⟨.resume 9 .unit, .ticket 9 19, stack⟩, issued, completed⟩, activations⟩ := by
  let focused : NamedState := ⟨⟨⟨operand, .ticket 9 19, .push (.plain resumeContext) stack⟩,
    issued, completed⟩, activations⟩
  let returned : NamedState := ⟨⟨⟨.unit, .ticket 9 19, .push (.plain resumeContext) stack⟩,
    issued, completed⟩, activations⟩
  have first : RetainedStep operations contracts result
      ⟨⟨⟨.resume 9 operand, .ticket 9 19, stack⟩, issued, completed⟩, activations⟩ focused := by
    simpa [ScopedPortJoint.advanceState, enteredActivations, focused, resumeContext] using
      (RetainedStep.focusResume (result := result) (operations := operations) (stack := stack) (issued := issued)
        (completed := completed) (activations := activations) (plain := resumeContext) (operand := operand)
        (by simp [operand, Code.IsValue]) rfl correct_ports)
  have middle : RetainedStep operations contracts result focused returned := by
    have raw : ScopedPortJoint.OrdinaryStep focused.execution.configuration returned.execution.configuration :=
      .bind ⟨trivial, rfl, by intro dependency member; cases member⟩ (by intro name member; cases member)
    simpa [ScopedPortJoint.advanceState, enteredActivations, focused, returned, operand] using
      (RetainedStep.stable (result := result) (operations := operations) (contracts := contracts) (before := focused) (.ordinary raw))
  have last : RetainedStep operations contracts result returned
      ⟨⟨⟨.resume 9 .unit, .ticket 9 19, stack⟩, issued, completed⟩, activations⟩ := by
    have closed : ClosedValue .unit := ⟨trivial, rfl, by intro dependency member; cases member⟩
    simpa [ScopedPortJoint.advanceState, enteredActivations, returned, resumeContext, Context.plug] using
      (RetainedStep.stable (result := result) (operations := operations) (contracts := contracts) (before := returned)
        (.value (RawStep.plug resumeContext _ closed (.ticket 9 19) stack) trivial))
  exact .tail (.tail (.single first) middle) last

/-- Add the actual one-shot consumption after operand evaluation. Both the
caller prefix and saved continuation are arbitrary finite stacks. -/
theorem focus_bind_resume {front captured tail : Stack} : Relation.TransGen (RetainedStep operations contracts result)
    ⟨⟨⟨.resume 9 operand, .ticket 9 19, front.append (.live 19 .unit .unit captured caller tail)⟩,
      issued, completed⟩, activations⟩
    ⟨⟨⟨.unit, .ticket 9 19, captured.append (front.append (.spent 19 .unit caller tail))⟩,
      issued, .ticket 19 :: completed⟩, activations⟩ := by
  apply Relation.TransGen.tail focus_bind_plug
  have closed : ClosedValue .unit := ⟨trivial, rfl, by intro dependency member; cases member⟩
  simpa [ScopedPortJoint.advanceState, enteredActivations] using
    (RetainedStep.stable (result := result) (operations := operations) (contracts := contracts)
      (before := ⟨⟨⟨.resume 9 .unit, .ticket 9 19, front.append (.live 19 .unit .unit captured caller tail)⟩,
        issued, completed⟩, activations⟩)
      (.resume (front := front) (capture := captured) (tail := tail) closed rfl))

/-- The common theorem derives every intermediate invariant, including the
transition from operand evaluation to actual continuation consumption. -/
theorem focused_resume_preserves {front captured tail : Stack}
    (before : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.resume 9 operand, .ticket 9 19, front.append (.live 19 .unit .unit captured caller tail)⟩,
        issued, completed⟩, activations⟩ forest output demand row bound) :
    ∃ saved : Saved, ∃ remaining nextRow,
      Run operations declarations policy contracts registry tables families required annotations
        ⟨⟨⟨.unit, .ticket 9 19, captured.append (front.append (.spent 19 .unit caller tail))⟩,
          issued, .ticket 19 :: completed⟩, activations⟩ saved.forest output remaining nextRow bound ∧
      nextRow.Sublist row :=
  (retained_run_preserves focus_bind_resume before).2

end ResumeFocusExamples


namespace ContextFocusExamples

def leftContext : PlainData :=
  ⟨.pairLeft (.boolean true), .none, .integer, .product .integer .boolean, [], rfl⟩
def rightContext : PlainData :=
  ⟨.pairRight (.integer 7), .none, .boolean, .product .integer .boolean, [], rfl⟩
def branchContext (scope : Scope) : PlainData :=
  ⟨.branch .unit .unit, scope, .boolean, .unit, [], by cases scope <;> rfl⟩
def resourceContext : PlainData :=
  ⟨.resource 7 .unit, .none, .integer, .unit, [], rfl⟩
def condition : Code := .bind 0 .unit (.boolean true)
def branch : Code := .branch condition .unit .unit

theorem four_context_forms :
    checkContextPorts (.product .integer .boolean) .nil leftContext = true ∧
    checkContextPorts (.product .integer .boolean) .nil rightContext = true ∧
    checkContextPorts .unit .nil (branchContext .none) = true ∧
    checkContextPorts .unit .nil resourceContext = true := by decide

theorem reversed_pair_ports_rejected :
    checkContextPorts (.product .integer .boolean) .nil { leftContext with input := .boolean } = false ∧
    checkContextPorts (.product .integer .boolean) .nil { rightContext with input := .integer } = false := by decide

theorem wrong_stack_result_rejected :
    checkContextPorts .integer .nil (branchContext .none) = false ∧
    checkContextPorts .integer .nil resourceContext = false := by decide

/-- Unresolved annotation choices are not silently treated as accepted. -/
theorem unsupported_contexts_rejected :
    contextInputPort (.appFunction .unit) .unit = none ∧
    contextInputPort (.appArgument .unit) .unit = none ∧
    contextInputPort (.bind 0 .unit) .unit = none ∧
    contextInputPort (.cleanup .unit) .unit = none := by decide

/-- The local guard reads the annotated stack head, including another operand
frame and live/spent boundaries. This does not assert whole-stack validity. -/
theorem nested_stack_ports :
    checkContextPorts .integer (.push (.plain ResumeFocusExamples.resumeContext) .nil)
      (branchContext (.ticket 9 19)) = true ∧
    checkContextPorts .integer (.live 19 .unit .unit .nil .none .nil)
      (branchContext (.ticket 9 19)) = true ∧
    checkContextPorts .integer (.spent 19 .unit .none .nil)
      (branchContext (.ticket 9 19)) = true := by decide

/-- Evaluate a condition, plug its frame, then choose the branch. Stack and
lexical continuation scope are arbitrary; only the finite port check is used. -/
theorem focus_bind_branch (stackPort : stackInputPort stack result = .unit) :
    Relation.TransGen (RetainedStep operations contracts result)
      ⟨⟨⟨branch, scope, stack⟩, issued, completed⟩, activations⟩
      ⟨⟨⟨.unit, scope, stack⟩, issued, completed⟩, activations⟩ := by
  let focused : NamedState := ⟨⟨⟨condition, scope, .push (.plain (branchContext scope)) stack⟩,
    issued, completed⟩, activations⟩
  let returned : NamedState := ⟨⟨⟨.boolean true, scope, .push (.plain (branchContext scope)) stack⟩,
    issued, completed⟩, activations⟩
  let ready : NamedState := ⟨⟨⟨.branch (.boolean true) .unit .unit, scope, stack⟩,
    issued, completed⟩, activations⟩
  have checked : checkContextPorts result stack (branchContext scope) = true := by
    simp [checkContextPorts, stackPort, branchContext, contextInputPort, ScopedPorts.eraseType]
  have first : RetainedStep operations contracts result
      ⟨⟨⟨branch, scope, stack⟩, issued, completed⟩, activations⟩ focused := by
    simpa [ScopedPortJoint.advanceState, enteredActivations, focused, branch, branchContext] using
      (RetainedStep.focusContext (operations := operations) (contracts := contracts) (result := result)
        (stack := stack) (issued := issued) (completed := completed) (activations := activations)
        (plain := branchContext scope) (.branch (by simp [condition, Code.IsValue])) checked)
  have middle : RetainedStep operations contracts result focused returned := by
    have raw : ScopedPortJoint.OrdinaryStep focused.execution.configuration returned.execution.configuration :=
      .bind ⟨trivial, rfl, by intro dependency member; cases member⟩ (by intro name member; cases member)
    simpa [ScopedPortJoint.advanceState, enteredActivations, focused, returned, condition] using
      (RetainedStep.stable (operations := operations) (contracts := contracts) (result := result)
        (before := focused) (.ordinary raw))
  have plug : RetainedStep operations contracts result returned ready := by
    have closed : ClosedValue (.boolean true) := ⟨trivial, rfl, by intro dependency member; cases member⟩
    simpa [ScopedPortJoint.advanceState, enteredActivations, returned, ready, branchContext, Context.plug] using
      (RetainedStep.stable (operations := operations) (contracts := contracts) (result := result)
        (before := returned) (.value (RawStep.plug (branchContext scope) _ closed scope stack) trivial))
  have last : RetainedStep operations contracts result ready
      ⟨⟨⟨.unit, scope, stack⟩, issued, completed⟩, activations⟩ := by
    simpa [ScopedPortJoint.advanceState, enteredActivations, ready] using
      (RetainedStep.stable (operations := operations) (contracts := contracts) (result := result)
        (before := ready) (.ordinary .ifTrue))
  exact .tail (.tail (.tail (.single first) middle) plug) last

/-- Nest context-based focusing inside contract-based resume focusing. The
ordinary condition steps occur before consuming the one-shot continuation. -/
theorem nested_resume_branch {front captured tail : Stack} :
    Relation.TransGen (RetainedStep operations ResumeFocusExamples.contracts result)
      ⟨⟨⟨.resume 9 branch, .ticket 9 19, front.append (.live 19 .unit .unit captured caller tail)⟩,
        issued, completed⟩, activations⟩
      ⟨⟨⟨.unit, .ticket 9 19, captured.append (front.append (.spent 19 .unit caller tail))⟩,
        issued, .ticket 19 :: completed⟩, activations⟩ := by
  let stack := front.append (.live 19 .unit .unit captured caller tail)
  let focused : NamedState := ⟨⟨⟨branch, .ticket 9 19, .push (.plain ResumeFocusExamples.resumeContext) stack⟩,
    issued, completed⟩, activations⟩
  let returned : NamedState := ⟨⟨⟨.unit, .ticket 9 19, .push (.plain ResumeFocusExamples.resumeContext) stack⟩,
    issued, completed⟩, activations⟩
  let ready : NamedState := ⟨⟨⟨.resume 9 .unit, .ticket 9 19, stack⟩, issued, completed⟩, activations⟩
  have first : RetainedStep operations ResumeFocusExamples.contracts result
      ⟨⟨⟨.resume 9 branch, .ticket 9 19, stack⟩, issued, completed⟩, activations⟩ focused := by
    simpa [ScopedPortJoint.advanceState, enteredActivations, focused, ResumeFocusExamples.resumeContext] using
      (RetainedStep.focusResume (operations := operations) (result := result) (stack := stack)
        (issued := issued) (completed := completed) (activations := activations)
        (plain := ResumeFocusExamples.resumeContext) (operand := branch)
        (by simp [branch, Code.IsValue]) rfl ResumeFocusExamples.correct_ports)
  have middle : Relation.TransGen (RetainedStep operations ResumeFocusExamples.contracts result) focused returned :=
    focus_bind_branch rfl
  have plug : RetainedStep operations ResumeFocusExamples.contracts result returned ready := by
    have closed : ClosedValue .unit := ⟨trivial, rfl, by intro dependency member; cases member⟩
    simpa [ScopedPortJoint.advanceState, enteredActivations, returned, ready,
      ResumeFocusExamples.resumeContext, Context.plug] using
      (RetainedStep.stable (operations := operations) (contracts := ResumeFocusExamples.contracts) (result := result)
        (before := returned) (.value (RawStep.plug ResumeFocusExamples.resumeContext _ closed (.ticket 9 19) stack) trivial))
  have last : RetainedStep operations ResumeFocusExamples.contracts result ready
      ⟨⟨⟨.unit, .ticket 9 19, captured.append (front.append (.spent 19 .unit caller tail))⟩,
        issued, .ticket 19 :: completed⟩, activations⟩ := by
    have closed : ClosedValue .unit := ⟨trivial, rfl, by intro dependency member; cases member⟩
    simpa [ScopedPortJoint.advanceState, enteredActivations, ready, stack] using
      (RetainedStep.stable (operations := operations) (contracts := ResumeFocusExamples.contracts) (result := result)
        (before := ready) (.resume (front := front) (capture := captured) (tail := tail) closed rfl))
  exact .tail (.tail ((Relation.TransGen.single first).trans middle) plug) last

theorem nested_resume_preserves {front captured tail : Stack}
    (before : Run operations declarations policy ResumeFocusExamples.contracts registry tables families required annotations
      ⟨⟨⟨.resume 9 branch, .ticket 9 19, front.append (.live 19 .unit .unit captured caller tail)⟩,
        issued, completed⟩, activations⟩ forest output demand row bound) :
    ∃ saved : Saved, ∃ remaining nextRow,
      Run operations declarations policy ResumeFocusExamples.contracts registry tables families required annotations
        ⟨⟨⟨.unit, .ticket 9 19, captured.append (front.append (.spent 19 .unit caller tail))⟩,
          issued, .ticket 19 :: completed⟩, activations⟩ saved.forest output remaining nextRow bound ∧
      nextRow.Sublist row :=
  (retained_run_preserves nested_resume_branch before).2

end ContextFocusExamples

end Ash.OneShot.SourceScheduledExecution

#print axioms Ash.OneShot.SourceScheduledExecution.stable_preserves
#print axioms Ash.OneShot.SourceScheduledExecution.retained_step_preserves
#print axioms Ash.OneShot.SourceScheduledExecution.retained_run_preserves

#print axioms Ash.OneShot.SourceScheduledExecution.checkRequestPorts_iff
#print axioms Ash.OneShot.SourceScheduledExecution.RequestFocusExamples.correct_ports
#print axioms Ash.OneShot.SourceScheduledExecution.RequestFocusExamples.wrong_input_rejected
#print axioms Ash.OneShot.SourceScheduledExecution.RequestFocusExamples.wrong_output_rejected
#print axioms Ash.OneShot.SourceScheduledExecution.RequestFocusExamples.focus_bind_plug
#print axioms Ash.OneShot.SourceScheduledExecution.RequestFocusExamples.focused_trace_preserves

#print axioms Ash.OneShot.SourceScheduledExecution.checkResumePorts_iff
#print axioms Ash.OneShot.SourceScheduledExecution.checkContextPorts_iff

#print axioms Ash.OneShot.SourceScheduledExecution.ResumeFocusExamples.correct_ports
#print axioms Ash.OneShot.SourceScheduledExecution.ResumeFocusExamples.unresolved_binder_rejected
#print axioms Ash.OneShot.SourceScheduledExecution.ResumeFocusExamples.missing_contract_rejected
#print axioms Ash.OneShot.SourceScheduledExecution.ResumeFocusExamples.wrong_ports_rejected
#print axioms Ash.OneShot.SourceScheduledExecution.ResumeFocusExamples.ports_do_not_revive_owner
#print axioms Ash.OneShot.SourceScheduledExecution.ResumeFocusExamples.focus_bind_plug
#print axioms Ash.OneShot.SourceScheduledExecution.ResumeFocusExamples.focus_bind_resume
#print axioms Ash.OneShot.SourceScheduledExecution.ResumeFocusExamples.focused_resume_preserves

#print axioms Ash.OneShot.SourceScheduledExecution.ContextFocusExamples.four_context_forms
#print axioms Ash.OneShot.SourceScheduledExecution.ContextFocusExamples.reversed_pair_ports_rejected
#print axioms Ash.OneShot.SourceScheduledExecution.ContextFocusExamples.wrong_stack_result_rejected
#print axioms Ash.OneShot.SourceScheduledExecution.ContextFocusExamples.unsupported_contexts_rejected
#print axioms Ash.OneShot.SourceScheduledExecution.ContextFocusExamples.nested_stack_ports
#print axioms Ash.OneShot.SourceScheduledExecution.ContextFocusExamples.focus_bind_branch
#print axioms Ash.OneShot.SourceScheduledExecution.ContextFocusExamples.nested_resume_branch
#print axioms Ash.OneShot.SourceScheduledExecution.ContextFocusExamples.nested_resume_preserves
