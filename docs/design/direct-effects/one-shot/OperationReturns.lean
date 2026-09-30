import OperationResults

/-!
Signature-aware normal-return obligations on the actual execution stack.
Capture annotations are checked against the operation signature independently
of raw execution. New allocation certificates remain local obligations.
-/

namespace Ash.OneShot.OperationReturns
open Instantiation Syntax ScopedExpressions ScopedExecution ScopedPorts
open ResultSummaries (Summary)
open ReturnSupport (Below)
open OperationResults
open ContinuationBounds (portBound)
open ReturnBoundaries (FrameChecked CellBound)

def frameResult (signature : Signature) (environment : ResultSummaries.Environment) : ExecFrame → Summary → Summary
  | .plain plain, result => contextResult signature environment plain.context result
  | .handler _, _ | .cell _ _ _ _, _ | .armed _, _ | .running _ _ _, _ | .unwinding _, _ |
    .closing _ _, _ | .retiring _, _ => .unknown

def stackResult (signature : Signature) (environment : ResultSummaries.Environment) : Stack → Summary → Summary
  | .nil, result => result
  | .push frame tail, result => stackResult signature environment tail (frameResult signature environment frame result)
  | .live _ _ _ _ _ tail, _ | .spent _ _ _ tail, _ => stackResult signature environment tail .unknown

theorem frame_result_monotone (frame : ExecFrame) (below : Below actual upper) :
    Below (frameResult signature environment frame actual) (frameResult signature environment frame upper) := by
  cases frame with
  | plain plain => exact context_result_monotone plain.context below
  | handler | cell | armed | running | unwinding | closing | retiring => exact Below.refl _

theorem cut_result (cut : HandlerCut requested whole cap tail handler) (summary : Summary) :
    stackResult signature environment whole summary = stackResult signature environment tail .unknown := by
  induction cut generalizing summary with
  | hit => rfl
  | push frame rest cap tail handler miss next ih => exact ih _
  | live ticket q a saved scope rest cap tail handler next ih => exact ih _
  | spent ticket a scope rest cap tail handler next ih => exact ih _

def Checked (signature : Signature) (environment : ResultSummaries.Environment) : Stack → Summary → Prop
  | .nil, _ => True
  | .push frame tail, summary => FrameChecked frame summary ∧
      Checked signature environment tail (frameResult signature environment frame summary)
  | .live _ input _ saved _ tail, _ =>
      Checked signature environment saved (portBound (eraseType input)) ∧ Checked signature environment tail .unknown
  | .spent _ _ _ tail, _ => Checked signature environment tail .unknown

def ConfigurationChecked (signature : Signature) (environment : ResultSummaries.Environment) (configuration : Configuration) : Prop :=
  Checked signature environment configuration.stack (analyze signature environment configuration.expression)

theorem checked_monotone (stack : Stack) (below : Below actual upper)
    (checked : Checked signature environment stack upper) : Checked signature environment stack actual := by
  induction stack generalizing actual upper with
  | nil => trivial
  | push frame tail ih => exact ⟨ReturnBoundaries.frame_checked_monotone below checked.1,
      ih (frame_result_monotone frame below) checked.2⟩
  | live | spent => exact checked

theorem checked_append (front tail : Stack) (summary : Summary) :
    Checked signature environment (front.append tail) summary ↔
      Checked signature environment front summary ∧ Checked signature environment tail (stackResult signature environment front summary) := by
  induction front generalizing summary with
  | nil => simp [Stack.append, Checked, stackResult]
  | push frame rest ih => simp only [Stack.append, Checked, stackResult, ih, and_assoc]
  | live owner input answer saved caller rest ihSaved ihRest =>
      simp only [Stack.append, Checked, stackResult, ihRest, and_assoc]
  | spent owner answer caller rest ih => exact ih _

theorem cut_cap_result (cut : HandlerCut requested whole cap tail handler) :
    stackResult signature environment cap summary = .unknown := by
    have selected : HandlerCut requested cap cap .nil handler := by
      induction cut with
      | hit handler tail same => exact .hit handler .nil same
      | push frame rest cap tail handler miss next ih => exact .push frame cap cap .nil handler miss ih
      | live ticket q a saved scope rest cap tail handler next ih => exact .live ticket q a saved scope cap cap .nil handler ih
      | spent ticket a scope rest cap tail handler next ih => exact .spent ticket a scope cap cap .nil handler ih
    exact cut_result selected summary

theorem checked_cut (cut : HandlerCut requested whole cap tail handler)
    (checked : Checked signature environment whole summary) :
    Checked signature environment cap summary ∧ Checked signature environment tail .unknown := by
  rw [handler_cut_reconstructs cut] at checked
  obtain ⟨inside, outside⟩ := (checked_append cap tail summary).mp checked
  rw [cut_cap_result cut] at outside
  exact ⟨inside, outside⟩

/-- Capture retains exactly the bound at which its saved continuation was
    checked. Establishing this bound at a pending request is separate from
    inferring its result in an enclosing initial calculus term. -/
theorem checked_capture (cut : HandlerCut requested whole cap tail handler)
    (checked : Checked signature environment whole (portBound (eraseType input))) :
    Checked signature environment (.live owner input handler.answer cap handler.scope tail) summary :=
  checked_cut cut checked

theorem capture_constructs_typed_checked
    (cut : HandlerCut requested whole cap tail handler)
    (known : signature requested operation = some (argument, output))
    (typed : ConfigurationTyped signature tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result)
    (isValue : operand.IsValue) (fresh : tickets owner = none)
    (checked : Checked signature environment whole (portBound output)) :
    ∃ (parameter binder : Nat) (body : Code),
      let extended := tickets.insert owner output (eraseType handler.answer)
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer cap handler.scope tail⟩
      RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      TicketExtension tickets extended ∧ ConfigurationTyped signature extended world after result ∧
      ConfigurationChecked signature environment after := by
  obtain ⟨resultPort, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, operationType, _, operandTyped⟩ := typed_perform_inversion expression
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans operationType))
      have closed := typed_value_closed operandTyped isValue
      obtain ⟨saved, outside, handlerTyped⟩ := handler_cut_retains_typing cut stack
      cases handlerTyped with
      | handler caller clauses coverage unique =>
          have handlerKnown := operationType
          rw [← ScopedTyping.handler_cut_instance cut] at handlerKnown
          obtain ⟨parameter, binder, body, selected⟩ := ScopedTyping.clause_at_of_key (coverage _ _ _ handlerKnown)
          obtain ⟨clauseInput, clauseOutput, clauseKnown, bodyTyped⟩ := selected_clause_typed selected clauses
          have ready := typed_suffix_ready bodyTyped
          have extension := fresh_ticket_signature_extension (input := output) (answer := eraseType handler.answer) fresh
          have newTicket : (tickets.insert owner output (eraseType handler.answer)) owner =
              some (output, eraseType handler.answer) := by simp [TicketSignatures.insert]
          refine ⟨parameter, binder, body,
            .capture requested operation parameter binder owner operand body scope whole cap tail handler
              (embedPort output) cut selected closed ready, extension, ?_, ?_⟩
          · exact ⟨eraseType handler.answer,
              .checked (.bound newTicket) (selected_clause_substitution_typed selected clauses handlerKnown operandTyped closed),
              .live (by simpa using newTicket) (scope_known_extension caller extension)
                (by simpa using stack_typed_extension saved extension) (stack_typed_extension outside extension)⟩
          · change Checked signature environment cap (portBound (eraseType (embedPort output))) ∧ Checked signature environment tail .unknown
            rw [erase_embed_port]
            exact checked_cut cut checked

theorem checked_resume {front cap tail : Stack}
    (checked : Checked signature environment (front.append (.live owner input answer cap callerScope tail)) .unknown)
    (bound : Below summary (portBound (eraseType input))) :
    Checked signature environment (cap.append (front.append (.spent owner answer callerScope tail))) summary := by
  obtain ⟨inside, saved, outside⟩ := (checked_append front _ _).mp checked
  apply (checked_append cap _ _).mpr
  refine ⟨checked_monotone cap bound saved, ?_⟩
  apply (checked_append front _ _).mpr
  exact ⟨checked_monotone front (Below.unknown _) inside, outside⟩

theorem close_control_checked (scope : Scope) (plan : List CloseEntry) (summary : Summary) :
    Checked signature environment (closeControl scope plan) summary := by
  induction plan generalizing summary with
  | nil => trivial
  | cons entry rest ih =>
      cases entry with
      | release identity payload => exact ⟨ReturnBoundaries.unit_cell_bound, ih _⟩
      | invoke action | retire ticket => exact ⟨trivial, ih _⟩

theorem checked_discard {front cap tail : Stack}
    (checked : Checked signature environment (front.append (.live owner input answer cap callerScope tail)) .unknown) :
    Checked signature environment ((closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer callerScope tail)))) summary := by
  obtain ⟨inside, _, outside⟩ := (checked_append front _ _).mp checked
  apply (checked_append (closeControl scope plan) _ _).mpr
  refine ⟨close_control_checked _ _ _, trivial, ?_⟩
  exact (checked_append front _ _).mpr ⟨inside, outside⟩

theorem cell_update_checked (update : CellUpdate identity old new before after)
    (checked : Checked signature environment before summary) : Checked signature environment after summary := by
  induction update generalizing summary with
  | hit => exact checked
  | push miss next ih => exact ⟨checked.1, ih checked.2⟩
  | live next ih => exact ⟨checked.1, ih checked.2⟩
  | spent next ih => exact ih checked

inductive AllocationReturn (signature : Signature) (environment : ResultSummaries.Environment) : List Owner → Configuration → Prop where
  | none (absent : ∀ identity, Owner.resource identity ∉ created) : AllocationReturn signature environment created configuration
  | cell (bound : CellBound identity answer (analyze signature environment body)) :
      AllocationReturn signature environment [.resource identity] ⟨body, scope, .push (.cell identity payload savedScope answer) tail⟩

/-- Only a newly captured ticket has an input annotation to check. The
    condition inspects this event's request, signature and saved input port;
    it makes no assertion about future execution or successor return checks. -/
def CaptureInput (signature : Signature) (before : Configuration)
    (created : List Owner) (after : Configuration) : Prop :=
  match created with
  | [.ticket owner] => match before.expression, after.stack with
      | .perform effect operation _, .live actual input _ _ _ _ =>
          owner = actual ∧ ∃ requested argument output,
            decodeEffect effect = some requested ∧
            signature requested operation = some (argument, output) ∧ eraseType input = output
      | _, _ => False
  | _ => True

theorem capture_input_known
    (known : signature requested operation = some (argument, output))
    (annotation : eraseType input = output) :
    CaptureInput signature ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩
      [.ticket owner] ⟨body, clauseScope, .live owner input answer cap caller tail⟩ :=
  ⟨rfl, requested, argument, output, decode_frozen_effect requested, known, annotation⟩

theorem raw_step_preserves_checked
    (step : RawStep before after created discharged)
    (typed : ConfigurationTyped (withCellSignatures users) tickets world before result)
    (checked : ConfigurationChecked (withCellSignatures users) environment before)
    (capture : CaptureInput (withCellSignatures users) before created after)
    (allocation : AllocationReturn (withCellSignatures users) environment created after) :
    ConfigurationChecked (withCellSignatures users) environment after := by
  cases step with
  | @focus whole child plain focus tail =>
      have same := context_result_plug (signature := withCellSignatures users) (environment := environment) plain.context child
      rw [focus_reconstructs focus] at same
      refine ⟨trivial, ?_⟩
      change Checked (withCellSignatures users) environment tail (contextResult (withCellSignatures users) environment plain.context (analyze (withCellSignatures users) environment child))
      rw [same]
      exact checked
  | plug plain value closed scope tail =>
      simpa only [ConfigurationChecked, Checked, frameResult, context_result_plug] using checked.2
  | bind parameter value suffix scope tail closed ready =>
      exact checked_monotone tail (Below.of_support_eq
        (analyze_substitution_support suffix parameter closed)) checked
  | beta parameter body value scope tail closed ready =>
      exact checked_monotone tail (upper := analyze (withCellSignatures users) environment (.app (.lambda parameter body) value))
        (Below.unknown _) checked
  | ifTrue yes no scope tail => exact checked_monotone tail (Below.join_left _ _) checked
  | ifFalse yes no scope tail => exact checked_monotone tail (Below.join_right _ _) checked
  | enterHandler | enterCleanup => exact ⟨trivial, checked⟩
  | enterCell binder identity payload body scope answer tail ready =>
      cases allocation with
      | none absent => exact False.elim (absent identity List.mem_cons_self)
      | cell bound => exact ⟨bound, checked⟩
  | leaveHandler handler value closed scope tail => exact checked_monotone tail (Below.unknown _) checked.2
  | leaveCell identity payload answer savedScope scope value closed tail => exact checked_monotone tail (Below.unknown _) checked.2
  | startCleanup => exact ⟨trivial, checked.2⟩
  | finishCleanup action saved closed scope tail => exact checked_monotone tail (Below.unknown _) checked.2
  | capture requested operation parameter binder owner operand body scope whole cap tail handler
      input selection clause closed ready =>
      obtain ⟨_, key, argument, output, decoded, known, annotation⟩ := capture
      rw [decode_frozen_effect] at decoded
      cases decoded
      have same := operation_bound_known known
      change Checked (withCellSignatures users) environment whole
        (operationBound (withCellSignatures users) (freezeEffect requested) operation) at checked
      rw [same, ← annotation] at checked
      exact checked_cut selection checked
  | resume binder owner scope callerScope input answer front cap tail value closed resolved =>
      exact checked_resume checked (resumed_value_below_input resolved typed closed.1)
  | discard binder owner closeId scope callerScope input answer front cap tail plan resolved build => exact checked_discard checked
  | leaveClause owner answer value closed scope callerScope tail => exact checked_monotone tail (Below.unknown _) checked
  | finishClose identity scope callerScope tail => exact checked_monotone tail (Below.unknown _) checked.2
  | retire owner scope tail => exact checked_monotone tail (Below.unknown _) checked.2
  | readCell identity payload scope before after selected =>
      exact cell_update_checked selected checked
  | writeCell identity old new scope before after selected =>
      exact cell_update_checked selected checked

theorem typed_resume_constructs_checked {front cap tail : Stack}
    (resolved : scope.resolve binder = some owner)
    (typed : ConfigurationTyped signature tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩ result)
    (isValue : value.IsValue)
    (checked : ConfigurationChecked signature environment
      ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩) :
    RawStep ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩
      ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩ [] [.ticket owner] ∧
    ConfigurationTyped signature tickets world
      ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩ result ∧
    ConfigurationChecked signature environment
      ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩ := by
  have operand := ContinuationBounds.resume_operand_bound resolved typed isValue (environment := environment)
  exact ⟨.resume binder owner scope callerScope input answer front cap tail value operand.1 resolved,
    resume_preserves_configuration_typing resolved typed, checked_resume checked (resumed_value_below_input resolved typed isValue)⟩


/-- Current request checking supplies the saved bound. The constructor also
    exposes the signature agreement of the same actual capture event. -/
theorem typed_capture_constructs_checked
    (cut : HandlerCut requested whole cap tail handler)
    (known : signature requested operation = some (argument, output))
    (typed : ConfigurationTyped signature tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result)
    (isValue : operand.IsValue) (fresh : tickets owner = none)
    (checked : ConfigurationChecked signature environment
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩) :
    ∃ (parameter binder : Nat) (body : Code),
      let extended := tickets.insert owner output (eraseType handler.answer)
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer cap handler.scope tail⟩
      RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CaptureInput signature ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ [.ticket owner] after ∧
      TicketExtension tickets extended ∧ ConfigurationTyped signature extended world after result ∧
      ConfigurationChecked signature environment after := by
  change Checked signature environment whole (analyze signature environment (.perform (freezeEffect requested) operation operand)) at checked
  rw [analyze_perform_known known] at checked
  obtain ⟨parameter, binder, body, step, extension, typedAfter, checkedAfter⟩ :=
    capture_constructs_typed_checked cut known typed isValue fresh checked
  exact ⟨parameter, binder, body, step, capture_input_known known (erase_embed_port output),
    extension, typedAfter, checkedAfter⟩

theorem typed_cell_return_excludes
    (typed : ConfigurationTyped signature tickets world
      ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ result)
    (closed : ClosedValue value)
    (checked : ConfigurationChecked signature environment
      ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩) :
    identity ∉ resourceDependencies value.dependencies := by
  rcases checked.1 with inferred | ⟨shape, _⟩
  · obtain ⟨resources, known, absent⟩ := inferred
    rw [closed_value_storage_sound closed] at known
    cases known
    exact absent
  · exact typed_first_order_cell_return_excludes_identity typed closed.1 shape

theorem value_access_checks
    (typed : ConfigurationTyped signature tickets world configuration result)
    (value : configuration.expression.IsValue)
    (checked : ConfigurationChecked signature environment configuration) : AccessChecks configuration ambient := by
  constructor
  · intro identity payload answer savedScope scope returned tail same closed
    rw [same] at typed checked
    exact typed_cell_return_excludes typed closed checked
  · intro requested operation operand scope whole cap tail handler same cut closed
    rw [same] at value
    cases value
  · intro binder owner scope caller input answer front cap tail plan same resolve built
    rw [same] at value
    cases value

theorem value_allocation_return (step : RawStep before after created discharged)
    (value : before.expression.IsValue) : AllocationReturn signature environment created after := by
  cases step <;> exact .none (by simp_all [Code.IsValue])

theorem value_capture_input (step : RawStep before after created discharged)
    (value : before.expression.IsValue) : CaptureInput signature before created after := by
  cases step <;> simp_all [CaptureInput, Code.IsValue]

theorem run_value_preserves_checked (step : RunStep before after)
    (typed : ConfigurationTyped (withCellSignatures users) tickets world before.configuration result)
    (value : before.configuration.expression.IsValue)
    (checked : ConfigurationChecked (withCellSignatures users) environment before.configuration) :
    ConfigurationChecked (withCellSignatures users) environment after.configuration := by
  cases step with
  | event after created discharged raw fresh =>
      exact raw_step_preserves_checked raw typed checked (value_capture_input raw value) (value_allocation_return raw value)

theorem named_value_preserves_checked (step : NamedAccessStep ambient before after)
    (typed : ConfigurationTyped (withCellSignatures users) tickets world before.execution.configuration result)
    (value : before.execution.configuration.expression.IsValue)
    (checked : ConfigurationChecked (withCellSignatures users) environment before.execution.configuration) :
    ConfigurationChecked (withCellSignatures users) environment after.execution.configuration :=
  run_value_preserves_checked (named_step_executes step.execution) typed value checked

theorem checked_value_progress
    (valid : ScopedPortJoint.Valid (withCellSignatures users) policy registry ambient before result outgoing)
    (value : before.execution.configuration.expression.IsValue)
    (checked : ConfigurationChecked (withCellSignatures users) environment before.execution.configuration) :
    before.execution.configuration.stack = .nil ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortJoint.Valid (withCellSignatures users) policy registry ambient after result outgoing ∧
      ConfigurationChecked (withCellSignatures users) environment after.execution.configuration := by
  have typed := effect_configuration_has_types valid.effects
  rcases ScopedPortJoint.checked_value_progress valid value (value_access_checks typed value checked)
      with terminal | ⟨after, step, next⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨after, step, next, named_value_preserves_checked step typed value checked⟩

theorem checked_ready_value_progress
    (ready : ScopedPortPrepared.Ready (withCellSignatures users) policy registry ambient before result outgoing)
    (value : before.execution.configuration.expression.IsValue)
    (checked : ConfigurationChecked (withCellSignatures users) environment before.execution.configuration) :
    ScopedPortProgress.Terminal before.execution.configuration ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortPrepared.Ready (withCellSignatures users) policy registry ambient after result outgoing ∧
      ConfigurationChecked (withCellSignatures users) environment after.execution.configuration := by
  have typed := effect_configuration_has_types ready.joint.effects
  rcases ScopedPortPrepared.checked_ready_value_progress ready value (value_access_checks typed value checked)
      with terminal | ⟨after, step, next⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨after, step, next, named_value_preserves_checked step typed value checked⟩

namespace Examples
open ContinuationBounds.Examples (environment answer family handler saved requesting captured resumed tickets)

theorem requesting_checked : ConfigurationChecked ContinuationBounds.Examples.signature environment requesting :=
  ⟨trivial, Or.inl ⟨[], rfl, by simp⟩, trivial, trivial⟩

theorem capture_agreement : CaptureInput ContinuationBounds.Examples.signature requesting [.ticket 5] captured :=
  capture_input_known rfl rfl

theorem capture_and_resume_checked :
    RawStep requesting captured [.ticket 5] [] ∧ RawStep captured resumed [] [.ticket 5] ∧
    CaptureInput ContinuationBounds.Examples.signature requesting [.ticket 5] captured ∧
    ConfigurationChecked ContinuationBounds.Examples.signature environment requesting ∧
    ConfigurationChecked ContinuationBounds.Examples.signature environment captured ∧
    ConfigurationChecked ContinuationBounds.Examples.signature environment resumed := by
  have checked : ConfigurationChecked ContinuationBounds.Examples.signature environment captured :=
    checked_capture ContinuationBounds.Examples.saved_cut
      (show Checked ContinuationBounds.Examples.signature environment saved (portBound .integer) from
        ⟨trivial, Or.inl ⟨[], rfl, by simp⟩, trivial, trivial⟩)
  obtain ⟨resume, _, afterChecked⟩ := typed_resume_constructs_checked (front := .nil) rfl
    ContinuationBounds.Examples.captured_typed trivial checked
  exact ⟨ContinuationBounds.Examples.typed_capture_and_resume.1, resume, capture_agreement,
    requesting_checked, checked, afterChecked⟩

theorem wrong_capture_input_rejected :
    ¬ CaptureInput ContinuationBounds.Examples.signature requesting [.ticket 5]
      ⟨.resume 9 (.integer 42), .ticket 9 5, .live 5 (.reference 7) answer saved .none .nil⟩ := by
  intro agreement
  obtain ⟨_, key, argument, output, decoded, known, annotation⟩ := agreement
  have same : key = family := Option.some.inj (decoded.symm.trans (decode_frozen_effect family))
  subst key
  have ports : (Port.unit, Port.integer) = (argument, output) := Option.some.inj known
  cases ports
  cases annotation

/-- Unit and Int have identical storage bounds, but capture checks the actual
    declared port. Storage equality alone is too weak an annotation check. -/
theorem scalar_mismatch_rejected :
    portBound Port.unit = portBound Port.integer ∧
    ¬ CaptureInput ContinuationBounds.Examples.signature requesting [.ticket 5]
      ⟨.resume 9 (.integer 42), .ticket 9 5, .live 5 .unit answer saved .none .nil⟩ := by
  refine ⟨rfl, ?_⟩
  intro agreement
  obtain ⟨_, key, argument, output, decoded, known, annotation⟩ := agreement
  have same : key = family := Option.some.inj (decoded.symm.trans (decode_frozen_effect family))
  subst key
  have ports : (Port.unit, Port.integer) = (argument, output) := Option.some.inj known
  cases ports
  cases annotation

def readStack : Stack := .push (.plain ContinuationBounds.Examples.copiedFrame)
  (.push (.cell 7 41 .none answer) .nil)
def reading : Configuration :=
  ⟨.perform (freezeEffect (.cell 7)) 0 (.resourceRef (.activation 7)), .none, readStack⟩
def readResult : Configuration := ⟨.integer 41, .none, readStack⟩

theorem builtin_read_preserves_whole_stack :
    RawStep reading readResult [] [] ∧
    ConfigurationChecked (withCellSignatures users) environment reading ∧
    ConfigurationChecked (withCellSignatures users) environment readResult := by
  have selected : CellUpdate 7 41 41 readStack readStack :=
    .push (by decide) .hit
  have checked : ConfigurationChecked (withCellSignatures users) environment reading :=
    ⟨trivial, Or.inl ⟨[], rfl, by simp⟩, trivial⟩
  exact ⟨.readCell 7 41 .none readStack readStack selected, checked, cell_update_checked selected checked⟩

end Examples

end Ash.OneShot.OperationReturns

#print axioms Ash.OneShot.OperationReturns.frame_result_monotone
#print axioms Ash.OneShot.OperationReturns.cut_result
#print axioms Ash.OneShot.OperationReturns.checked_monotone
#print axioms Ash.OneShot.OperationReturns.checked_append
#print axioms Ash.OneShot.OperationReturns.cut_cap_result
#print axioms Ash.OneShot.OperationReturns.checked_cut
#print axioms Ash.OneShot.OperationReturns.checked_capture
#print axioms Ash.OneShot.OperationReturns.capture_constructs_typed_checked
#print axioms Ash.OneShot.OperationReturns.checked_resume
#print axioms Ash.OneShot.OperationReturns.close_control_checked
#print axioms Ash.OneShot.OperationReturns.checked_discard
#print axioms Ash.OneShot.OperationReturns.cell_update_checked
#print axioms Ash.OneShot.OperationReturns.capture_input_known
#print axioms Ash.OneShot.OperationReturns.raw_step_preserves_checked
#print axioms Ash.OneShot.OperationReturns.typed_resume_constructs_checked
#print axioms Ash.OneShot.OperationReturns.typed_capture_constructs_checked
#print axioms Ash.OneShot.OperationReturns.typed_cell_return_excludes
#print axioms Ash.OneShot.OperationReturns.value_access_checks
#print axioms Ash.OneShot.OperationReturns.value_allocation_return
#print axioms Ash.OneShot.OperationReturns.value_capture_input
#print axioms Ash.OneShot.OperationReturns.run_value_preserves_checked
#print axioms Ash.OneShot.OperationReturns.named_value_preserves_checked
#print axioms Ash.OneShot.OperationReturns.checked_value_progress
#print axioms Ash.OneShot.OperationReturns.checked_ready_value_progress
#print axioms Ash.OneShot.OperationReturns.Examples.requesting_checked
#print axioms Ash.OneShot.OperationReturns.Examples.capture_agreement
#print axioms Ash.OneShot.OperationReturns.Examples.capture_and_resume_checked
#print axioms Ash.OneShot.OperationReturns.Examples.wrong_capture_input_rejected
#print axioms Ash.OneShot.OperationReturns.Examples.scalar_mismatch_rejected
#print axioms Ash.OneShot.OperationReturns.Examples.builtin_read_preserves_whole_stack
