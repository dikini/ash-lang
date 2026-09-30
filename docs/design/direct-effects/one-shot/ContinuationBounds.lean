import TemplateSubstitution

/-!
Declared input ports bound actual resumed values. Saved resource-return
checks retain those bounds rather than forgetting every input. Callable
ports remain unknown because their declaration does not bound stored captures.
-/

namespace Ash.OneShot.ContinuationBounds
open Instantiation Syntax ScopedExpressions ScopedExecution ScopedPorts
open ResultSummaries ReturnSupport
open ReturnBoundaries (FrameChecked AllocationReturn)

def portBound : Port → Summary
  | .unit | .boolean | .integer => .scalar
  | .reference identity => .resource identity
  | .product left right => .product (portBound left) (portBound right)
  | .function _ _ _ => .unknown

theorem port_bound_finite (type : Port) (known : (portBound type).support = some resources) :
    type.FirstOrder ∧ resources = type.resources := by
  induction type generalizing resources with
  | unit => exact ⟨.unit, (Option.some.inj known).symm⟩
  | boolean => exact ⟨.boolean, (Option.some.inj known).symm⟩
  | integer => exact ⟨.integer, (Option.some.inj known).symm⟩
  | reference identity => exact ⟨.reference, (Option.some.inj known).symm⟩
  | function => cases known
  | product left right ihLeft ihRight =>
      cases leftKnown : (portBound left).support with
      | none => simp [portBound, Summary.support, leftKnown] at known
      | some xs => cases rightKnown : (portBound right).support with
          | none => simp [portBound, Summary.support, leftKnown, rightKnown] at known
          | some ys =>
              obtain ⟨leftShape, rfl⟩ := ihLeft leftKnown
              obtain ⟨rightShape, rfl⟩ := ihRight rightKnown
              have same : left.resources ++ right.resources = resources := by
                simpa [portBound, Summary.support, leftKnown, rightKnown] using known
              exact ⟨.product leftShape rightShape, same.symm⟩

theorem first_order_port_bound (shape : type.FirstOrder) :
    (portBound type).support = some type.resources := by
  induction shape with
  | unit | boolean | integer | reference => rfl
  | product left right ihLeft ihRight => simp [portBound, Summary.support, ihLeft, ihRight, Port.resources]

theorem typed_value_below_port
    (typed : Typed signature world TypeEnv.empty ticket allowed value type)
    (isValue : value.IsValue) : Below (analyze environment value) (portBound type) := by
  intro resources known
  obtain ⟨shape, rfl⟩ := port_bound_finite type known
  refine ⟨type.resources, ?_, List.Subset.refl _⟩
  rw [closed_value_storage_sound (typed_value_closed typed isValue),
    typed_first_order_value_support typed isValue shape]

/-- The historical ticket signature connects the operand's static input
    port to the actual saved stack's input annotation. -/
theorem resume_operand_bound {front cap tail : Stack}
    (resolved : scope.resolve binder = some owner)
    (typed : ConfigurationTyped signature tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩ result)
    (isValue : value.IsValue) :
    ClosedValue value ∧ Below (analyze environment value) (portBound (eraseType input)) := by
  obtain ⟨expressionType, expression, stack⟩ := typed
  cases expression with
  | checked scopeType expression => cases expression with
      | resume operand effects formed => cases scopeType with
          | bound known =>
              simp [Execution.Scope.resolve] at resolved
              subst owner
              obtain ⟨middle, _, outside⟩ := stack_typed_decompose front stack
              cases outside with
              | live actual caller saved rest =>
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans actual))
                  exact ⟨typed_value_closed operand isValue, typed_value_below_port operand isValue⟩

def Checked (environment : ResultSummaries.Environment) : Stack → Summary → Prop
  | .nil, _ => True
  | .push frame tail, summary => FrameChecked frame summary ∧
      Checked environment tail (frameResult environment frame summary)
  | .live _ input _ saved _ tail, _ =>
      Checked environment saved (portBound (eraseType input)) ∧ Checked environment tail .unknown
  | .spent _ _ _ tail, _ => Checked environment tail .unknown

def ConfigurationChecked (environment : ResultSummaries.Environment) (configuration : Configuration) : Prop :=
  Checked environment configuration.stack (analyze environment configuration.expression)

theorem checked_monotone (stack : Stack) (below : Below actual upper)
    (checked : Checked environment stack upper) : Checked environment stack actual := by
  induction stack generalizing actual upper with
  | nil => trivial
  | push frame tail ih => exact ⟨ReturnBoundaries.frame_checked_monotone below checked.1,
      ih (frame_result_monotone frame below) checked.2⟩
  | live | spent => exact checked

theorem old_checked_suffices (stack : Stack) (checked : ReturnBoundaries.Checked environment stack summary) :
    Checked environment stack summary := by
  induction stack generalizing summary with
  | nil => trivial
  | push frame tail ih => exact ⟨checked.1, ih checked.2⟩
  | live owner input answer saved caller tail ihSaved ihTail =>
      exact ⟨ihSaved (ReturnBoundaries.checked_monotone saved (Below.unknown _) checked.1), ihTail checked.2⟩
  | spent owner answer caller tail ih => exact ih checked

theorem checked_append (front tail : Stack) (summary : Summary) :
    Checked environment (front.append tail) summary ↔
      Checked environment front summary ∧ Checked environment tail (stackResult environment front summary) := by
  induction front generalizing summary with
  | nil => simp [Stack.append, Checked, stackResult]
  | push frame rest ih => simp only [Stack.append, Checked, stackResult, ih, and_assoc]
  | live owner input answer saved caller rest ihSaved ihRest =>
      simp only [Stack.append, Checked, stackResult, ihRest, and_assoc]
  | spent owner answer caller rest ih => exact ih _

theorem checked_cut (cut : HandlerCut requested whole cap tail handler)
    (checked : Checked environment whole summary) :
    Checked environment cap summary ∧ Checked environment tail .unknown := by
  rw [handler_cut_reconstructs cut] at checked
  obtain ⟨inside, outside⟩ := (checked_append cap tail summary).mp checked
  rw [ReturnBoundaries.cut_cap_result cut] at outside
  exact ⟨inside, outside⟩

/-- Capture retains exactly the bound at which its saved continuation was
    checked. Establishing this bound at a pending request is separate from
    inferring its result in an enclosing initial calculus term. -/
theorem checked_capture (cut : HandlerCut requested whole cap tail handler)
    (checked : Checked environment whole (portBound (eraseType input))) :
    Checked environment (.live owner input handler.answer cap handler.scope tail) summary :=
  checked_cut cut checked

/-- The captured input annotation is derived from the actual operation's
    declared result port. Freshness here concerns the historical type table;
    ownership, access and closing admission remain independent. -/
theorem capture_constructs_typed_checked
    (cut : HandlerCut requested whole cap tail handler)
    (known : signature requested operation = some (argument, output))
    (typed : ConfigurationTyped signature tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result)
    (isValue : operand.IsValue) (fresh : tickets owner = none)
    (checked : Checked environment whole (portBound output)) :
    ∃ (parameter binder : Nat) (body : Code),
      let extended := tickets.insert owner output (eraseType handler.answer)
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer cap handler.scope tail⟩
      RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      TicketExtension tickets extended ∧ ConfigurationTyped signature extended world after result ∧
      ConfigurationChecked environment after := by
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
          · change Checked environment cap (portBound (eraseType (embedPort output))) ∧ Checked environment tail .unknown
            rw [erase_embed_port]
            exact checked_cut cut checked

theorem checked_resume {front cap tail : Stack}
    (checked : Checked environment (front.append (.live owner input answer cap callerScope tail)) .unknown)
    (bound : Below summary (portBound (eraseType input))) :
    Checked environment (cap.append (front.append (.spent owner answer callerScope tail))) summary := by
  obtain ⟨inside, saved, outside⟩ := (checked_append front _ _).mp checked
  apply (checked_append cap _ _).mpr
  refine ⟨checked_monotone cap bound saved, ?_⟩
  apply (checked_append front _ _).mpr
  exact ⟨checked_monotone front (Below.unknown _) inside, outside⟩

theorem close_control_checked (scope : Scope) (plan : List CloseEntry) (summary : Summary) :
    Checked environment (closeControl scope plan) summary :=
  old_checked_suffices _ (ReturnBoundaries.close_control_checked scope plan summary)

theorem checked_discard {front cap tail : Stack}
    (checked : Checked environment (front.append (.live owner input answer cap callerScope tail)) .unknown) :
    Checked environment ((closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer callerScope tail)))) summary := by
  obtain ⟨inside, _, outside⟩ := (checked_append front _ _).mp checked
  apply (checked_append (closeControl scope plan) _ _).mpr
  refine ⟨close_control_checked _ _ _, trivial, ?_⟩
  exact (checked_append front _ _).mpr ⟨inside, outside⟩

theorem cell_update_checked (update : CellUpdate identity old new before after)
    (checked : Checked environment before summary) : Checked environment after summary := by
  induction update generalizing summary with
  | hit => exact checked
  | push miss next ih => exact ⟨checked.1, ih checked.2⟩
  | live next ih => exact ⟨checked.1, ih checked.2⟩
  | spent next ih => exact ih checked

theorem raw_step_preserves_checked
    (step : RawStep before after created discharged)
    (typed : ConfigurationTyped signature tickets world before result)
    (checked : ConfigurationChecked environment before)
    (allocation : AllocationReturn environment created after) :
    ConfigurationChecked environment after := by
  cases step with
  | @focus whole child plain focus tail =>
      have same := context_result_plug (environment := environment) plain.context child
      rw [focus_reconstructs focus] at same
      refine ⟨trivial, ?_⟩
      change Checked environment tail (contextResult environment plain.context (analyze environment child))
      rw [same]
      exact checked
  | plug plain value closed scope tail =>
      simpa only [ConfigurationChecked, Checked, frameResult, context_result_plug] using checked.2
  | bind parameter value suffix scope tail closed ready =>
      exact checked_monotone tail (Below.of_support_eq
        (bind_summary_correspondence parameter suffix closed).storage.support.symm) checked
  | beta parameter body value scope tail closed ready =>
      exact checked_monotone tail (upper := analyze environment (.app (.lambda parameter body) value))
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
      exact checked_capture selection (checked_monotone whole (Below.unknown _) checked)
  | resume binder owner scope callerScope input answer front cap tail value closed resolved =>
      exact checked_resume checked (resume_operand_bound resolved typed closed.1).2
  | discard binder owner closeId scope callerScope input answer front cap tail plan resolved build => exact checked_discard checked
  | leaveClause owner answer value closed scope callerScope tail => exact checked_monotone tail (Below.unknown _) checked
  | finishClose identity scope callerScope tail => exact checked_monotone tail (Below.unknown _) checked.2
  | retire owner scope tail => exact checked_monotone tail (Below.unknown _) checked.2
  | readCell identity payload scope before after selected =>
      exact checked_monotone after (Below.unknown _) (cell_update_checked selected checked)
  | writeCell identity old new scope before after selected =>
      exact checked_monotone after (Below.unknown _) (cell_update_checked selected checked)

theorem typed_resume_constructs_checked {front cap tail : Stack}
    (resolved : scope.resolve binder = some owner)
    (typed : ConfigurationTyped signature tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩ result)
    (isValue : value.IsValue)
    (checked : ConfigurationChecked environment
      ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩) :
    RawStep ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩
      ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩ [] [.ticket owner] ∧
    ConfigurationTyped signature tickets world
      ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩ result ∧
    ConfigurationChecked environment
      ⟨value, scope, cap.append (front.append (.spent owner answer callerScope tail))⟩ := by
  have operand := resume_operand_bound resolved typed isValue (environment := environment)
  exact ⟨.resume binder owner scope callerScope input answer front cap tail value operand.1 resolved,
    resume_preserves_configuration_typing resolved typed, checked_resume checked operand.2⟩

theorem typed_cell_return_excludes
    (typed : ConfigurationTyped signature tickets world
      ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ result)
    (closed : ClosedValue value)
    (checked : ConfigurationChecked environment
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
    (checked : ConfigurationChecked environment configuration) : AccessChecks configuration ambient := by
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

theorem run_value_preserves_checked (step : RunStep before after)
    (typed : ConfigurationTyped signature tickets world before.configuration result)
    (value : before.configuration.expression.IsValue)
    (checked : ConfigurationChecked environment before.configuration) :
    ConfigurationChecked environment after.configuration := by
  cases step with
  | event after created discharged raw fresh =>
      exact raw_step_preserves_checked raw typed checked (ReturnBoundaries.value_allocation_return raw value)

theorem named_value_preserves_checked (step : NamedAccessStep ambient before after)
    (typed : ConfigurationTyped signature tickets world before.execution.configuration result)
    (value : before.execution.configuration.expression.IsValue)
    (checked : ConfigurationChecked environment before.execution.configuration) :
    ConfigurationChecked environment after.execution.configuration :=
  run_value_preserves_checked (named_step_executes step.execution) typed value checked

theorem checked_value_progress
    (valid : ScopedPortJoint.Valid signature policy registry ambient before result outgoing)
    (value : before.execution.configuration.expression.IsValue)
    (checked : ConfigurationChecked environment before.execution.configuration) :
    before.execution.configuration.stack = .nil ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortJoint.Valid signature policy registry ambient after result outgoing ∧
      ConfigurationChecked environment after.execution.configuration := by
  have typed := effect_configuration_has_types valid.effects
  rcases ScopedPortJoint.checked_value_progress valid value (value_access_checks typed value checked)
      with terminal | ⟨after, step, next⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨after, step, next, named_value_preserves_checked step typed value checked⟩

theorem checked_ready_value_progress
    (ready : ScopedPortPrepared.Ready (withCellSignatures users) policy registry ambient before result outgoing)
    (value : before.execution.configuration.expression.IsValue)
    (checked : ConfigurationChecked environment before.execution.configuration) :
    ScopedPortProgress.Terminal before.execution.configuration ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortPrepared.Ready (withCellSignatures users) policy registry ambient after result outgoing ∧
      ConfigurationChecked environment after.execution.configuration := by
  have typed := effect_configuration_has_types ready.joint.effects
  rcases ScopedPortPrepared.checked_ready_value_progress ready value (value_access_checks typed value checked)
      with terminal | ⟨after, step, next⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨after, step, next, named_value_preserves_checked step typed value checked⟩

namespace Examples

def environment : ResultSummaries.Environment := fun _ => .unknown
def answer : Ty := ReturnBoundaries.Examples.callbackAnswer
def family : Instance := .user 83 []
def signature : Signature := fun _ operation => if operation = 0 then some (.unit, .integer) else none

def handler : HandlerData :=
  ⟨12, family, .cons 0 5 9 (.resume 9 (.integer 42)) .nil, .none, answer, rfl⟩

def copiedFrame : PlainData :=
  ⟨.bind 3 (.lambda 0 (.variable 3)), .none, .integer, answer, [], rfl⟩

def saved : Stack := .push (.plain copiedFrame)
  (.push (.cell 7 41 .none answer) (.push (.handler handler) .nil))

def requesting : Configuration := ⟨.perform (freezeEffect family) 0 .unit, .none, saved⟩
def captured : Configuration := ⟨.resume 9 (.integer 42), .ticket 9 5, .live 5 .integer answer saved .none .nil⟩
def resumed : Configuration := ⟨.integer 42, .ticket 9 5, saved.append (.spent 5 answer .none .nil)⟩
def tickets : TicketSignatures := fun owner => if owner = 5 then some (.integer, eraseType answer) else none

theorem saved_cut : HandlerCut family saved saved .nil handler := by
  apply HandlerCut.push (.plain copiedFrame) _ _ .nil handler (by decide)
  apply HandlerCut.push (.cell 7 41 .none answer) _ _ .nil handler (by decide)
  exact .hit handler .nil rfl

theorem saved_integer_bound : Checked environment saved (portBound .integer) :=
  ⟨trivial, Or.inl ⟨[], rfl, by simp⟩, trivial, trivial⟩

theorem captured_checked : ConfigurationChecked environment captured := checked_capture saved_cut saved_integer_bound

theorem old_unknown_capture_rejected : ¬ ReturnBoundaries.ConfigurationChecked environment captured := by
  intro checked
  rcases checked.1.2.1 with ⟨resources, known, _⟩ | ⟨shape, _⟩
  · cases known
  · cases shape

theorem saved_typed (records : TicketSignatures) :
    StackTyped signature records [7] saved .integer (eraseType answer) := by
  have suffix : Typed signature [7] (TypeEnv.empty.extend 3 .integer) .none []
      (.lambda 0 (.variable 3)) (eraseType answer) :=
    .lambda (.variable rfl (List.nil_subset _)) (List.nil_subset _)
  have clauses : ClausesTyped signature [7] TypeEnv.empty family (eraseType answer) [] handler.clauses :=
    .cons rfl (.resume .integer (List.Subset.refl []) (List.nil_subset _)) .nil
  have coverage : Covers signature family handler.clauses := by
    intro operation input output known
    by_cases zero : operation = 0
    · subst operation
      exact List.mem_cons_self
    · simp [signature, zero] at known
  exact .push (.plain ScopeTyped.none (.bind suffix))
    (.push (.cell ⟨_, ScopeTyped.none⟩ (by simp [answer, ReturnBoundaries.Examples.callbackAnswer, eraseType, Port.resources]))
      (.push (.handler ⟨_, ScopeTyped.none⟩ clauses coverage (by decide)) .nil))

theorem requesting_typed : ConfigurationTyped signature (fun _ => none) [7] requesting (eraseType answer) := by
  refine ⟨.integer, AtType.checked (allowed := [family]) ScopeTyped.none ?_, saved_typed _⟩
  exact Typed.perform rfl List.mem_cons_self Typed.unit (by simp [InWorld, Port.resources])

theorem captured_typed : ConfigurationTyped signature tickets [7] captured (eraseType answer) := by
  refine ⟨eraseType answer, AtType.checked (allowed := []) (ScopeTyped.bound (residual := []) (closing := []) (by rfl)) ?_,
    StackTyped.live (by rfl) ⟨_, ScopeTyped.none⟩ (saved_typed _) StackTyped.nil⟩
  apply Typed.resume Typed.integer (List.Subset.refl [])
  simp [InWorld, answer, ReturnBoundaries.Examples.callbackAnswer, eraseType, Port.resources]

/-- A parameterless integer-producing request crosses a resource whose result
    is a closure retaining the copied integer. These are actual raw events,
    value-type checks and return bounds; full joined admission is separate. -/
theorem typed_capture_and_resume :
    RawStep requesting captured [.ticket 5] [] ∧
    RawStep captured resumed [] [.ticket 5] ∧
    ConfigurationTyped signature (fun _ => none) [7] requesting (eraseType answer) ∧
    ConfigurationTyped signature tickets [7] captured (eraseType answer) ∧
    ConfigurationTyped signature tickets [7] resumed (eraseType answer) ∧
    ConfigurationChecked environment captured ∧ ConfigurationChecked environment resumed := by
  have capture : RawStep requesting captured [.ticket 5] [] :=
    .capture family 0 5 9 5 .unit (.resume 9 (.integer 42)) .none saved saved .nil handler .integer
      saved_cut .hit ScopedExecution.Examples.unit_closed
      (by intro name member; simp [Code.dependencies] at member)
  obtain ⟨resume, typed, checked⟩ := typed_resume_constructs_checked (front := .nil) rfl captured_typed trivial captured_checked
  exact ⟨capture, resume, requesting_typed, captured_typed, typed, captured_checked, checked⟩

theorem callable_input_stays_unknown :
    portBound (.function .unit .integer []) = .unknown := rfl

/-- Raw resumption alone does not enforce the ticket's input port. Dropping
    the typing premise would allow a handle where the saved check expects
    an integer, making the returned closure retain its closing resource. -/
theorem raw_resume_without_input_typing_can_break_the_bound :
    let before : Configuration := ⟨.resume 9 (.resourceRef (.activation 7)), .ticket 9 5,
      .live 5 .integer answer saved .none .nil⟩
    let after : Configuration := ⟨.resourceRef (.activation 7), .ticket 9 5,
      saved.append (.spent 5 answer .none .nil)⟩
    RawStep before after [] [.ticket 5] ∧ ConfigurationChecked environment before ∧
      ¬ ConfigurationChecked environment after := by
  have closed : ClosedValue (.resourceRef (.activation 7)) := by
    refine ⟨trivial, rfl, ?_⟩
    intro dependency member
    simp only [Code.dependencies, List.mem_singleton] at member
    subst dependency
    trivial
  refine ⟨.resume 9 5 (.ticket 9 5) .none .integer answer .nil saved .nil _ closed rfl,
    captured_checked, ?_⟩
  intro checked
  rcases checked.2.1 with ⟨resources, known, absent⟩ | ⟨shape, _⟩
  · have same : [7] = resources := Option.some.inj known
    subst resources
    exact absent List.mem_cons_self
  · cases shape

end Examples
end Ash.OneShot.ContinuationBounds

#print axioms Ash.OneShot.ContinuationBounds.port_bound_finite
#print axioms Ash.OneShot.ContinuationBounds.first_order_port_bound
#print axioms Ash.OneShot.ContinuationBounds.typed_value_below_port
#print axioms Ash.OneShot.ContinuationBounds.resume_operand_bound
#print axioms Ash.OneShot.ContinuationBounds.checked_monotone
#print axioms Ash.OneShot.ContinuationBounds.old_checked_suffices
#print axioms Ash.OneShot.ContinuationBounds.checked_append
#print axioms Ash.OneShot.ContinuationBounds.checked_cut
#print axioms Ash.OneShot.ContinuationBounds.checked_capture
#print axioms Ash.OneShot.ContinuationBounds.capture_constructs_typed_checked
#print axioms Ash.OneShot.ContinuationBounds.checked_resume
#print axioms Ash.OneShot.ContinuationBounds.close_control_checked
#print axioms Ash.OneShot.ContinuationBounds.checked_discard
#print axioms Ash.OneShot.ContinuationBounds.cell_update_checked
#print axioms Ash.OneShot.ContinuationBounds.raw_step_preserves_checked
#print axioms Ash.OneShot.ContinuationBounds.typed_resume_constructs_checked
#print axioms Ash.OneShot.ContinuationBounds.typed_cell_return_excludes
#print axioms Ash.OneShot.ContinuationBounds.value_access_checks
#print axioms Ash.OneShot.ContinuationBounds.run_value_preserves_checked
#print axioms Ash.OneShot.ContinuationBounds.named_value_preserves_checked
#print axioms Ash.OneShot.ContinuationBounds.checked_value_progress
#print axioms Ash.OneShot.ContinuationBounds.checked_ready_value_progress
#print axioms Ash.OneShot.ContinuationBounds.Examples.saved_cut
#print axioms Ash.OneShot.ContinuationBounds.Examples.saved_integer_bound
#print axioms Ash.OneShot.ContinuationBounds.Examples.captured_checked
#print axioms Ash.OneShot.ContinuationBounds.Examples.old_unknown_capture_rejected
#print axioms Ash.OneShot.ContinuationBounds.Examples.saved_typed
#print axioms Ash.OneShot.ContinuationBounds.Examples.requesting_typed
#print axioms Ash.OneShot.ContinuationBounds.Examples.captured_typed
#print axioms Ash.OneShot.ContinuationBounds.Examples.typed_capture_and_resume
#print axioms Ash.OneShot.ContinuationBounds.Examples.callable_input_stays_unknown
#print axioms Ash.OneShot.ContinuationBounds.Examples.raw_resume_without_input_typing_can_break_the_bound
