import CallableJoint

/-!
Current-state progress and non-capture contract preservation for the callable
fragment of the one-shot calculus. These results retain the joined invariant;
checked-run construction and disposal/cleanup remain separate obligations.
-/

namespace Ash.OneShot.CallableProgress
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ScopedTyping (resourceWorld resource_world_append)
open DeclarationResults (signature)
open CallableFrames (ConfigurationReturns StackReturns)
open GenerativeProgress (NoSourceRequest)

theorem cell_update_preserves_results
    (update : CellUpdate identity old new before after)
    (checked : StackReturns declarations registry world before input output) :
    StackReturns declarations registry world after input output := by
  induction update generalizing input output with
  | hit => cases checked with
      | cell scope absent rest => exact .cell scope absent rest
  | push miss next ih => cases checked with
      | plain scope context rest => exact .plain scope context (ih rest)
      | cell scope absent rest => exact .cell scope absent (ih rest)
      | handler scope clauses rest => exact .handler scope clauses (ih rest)
  | live next ih => cases checked with
      | live known scope saved rest => exact .live known scope saved (ih rest)
  | spent next ih => cases checked with
      | spent known scope rest => exact .spent known scope (ih rest)

theorem request_storage_contract
    (checked : CallableContracts.Derives declarations environment world ticket (.perform effect operation operand) contract) :
    ∃ bound, contract = .storage bound := by
  cases checked with
  | leaf isValue => cases isValue
  | perform => exact ⟨_, rfl⟩

theorem builtin_request_preserves_results
    (raw : RawStep before after [] [])
    (same : before.expression = .perform effect operation operand)
    (isValue : operand.IsValue)
    (checked : ConfigurationReturns declarations registry world before output) :
    ConfigurationReturns declarations registry world after output := by
  have ordinary := ScopedPortProgress.nonallocating_request_is_ordinary raw same isValue
  cases ordinary with
  | bind | beta | ifTrue | ifFalse => cases same
  | read selected =>
      obtain ⟨environment, ticket, contract, scope, code, stack⟩ := checked
      obtain ⟨bound, rfl⟩ := request_storage_contract code
      exact ⟨environment, ticket, .storage bound, scope, .leaf trivial rfl .nil,
        cell_update_preserves_results selected stack⟩
  | write selected =>
      obtain ⟨environment, ticket, contract, scope, code, stack⟩ := checked
      obtain ⟨bound, rfl⟩ := request_storage_contract code
      exact ⟨environment, ticket, .storage bound, scope, .leaf trivial rfl .nil,
        cell_update_preserves_results selected stack⟩

theorem request_progress
    (valid : CallableJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (isValue : operand.IsValue) :
    (requested ∈ outgoing ∧ stack.erase.resolve requested = none) ∨
      ∃ next after, NamedAccessStep ambient
        ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
        CallableJoint.Valid declarations policy next ambient after result outgoing bound ∧
        CallableJoint.RegistryExtends registry next := by
  cases resolved : stack.erase.resolve requested with
  | none =>
      rcases current_request_is_interpreted_or_exported valid.joint.effects with ⟨target, found⟩ | exported
      · simp [resolved] at found
      · exact Or.inl ⟨exported, rfl⟩
  | some target => cases target with
      | builtin identity =>
          obtain rfl := ScopedTyping.builtin_resolution_instance stack resolved
          obtain ⟨after, raw, effects⟩ := builtin_effect_progress valid.joint.effects isValue resolved
          obtain ⟨step, joint⟩ := ScopedPortJoint.ordinary_step_preserves_joint_configuration
            (ScopedPortProgress.nonallocating_request_is_ordinary raw rfl isValue) valid.joint
          have results := builtin_request_preserves_results raw rfl isValue valid.results
          exact Or.inr ⟨registry, _, step, ⟨joint, by simpa [ScopedPortJoint.advanceState] using results⟩,
            CallableJoint.registry_extends_refl _⟩
      | source activation =>
          obtain ⟨cap, tail, handler, cut, active⟩ := ScopedTyping.handler_selection_of_resolution stack resolved
          obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) valid.joint.ledger.2
          obtain ⟨parameter, binder, body, output, residual, record, contract, selected, known, extension, step, afterValid⟩ :=
            CallableJoint.capture_without_payload_premise cut valid isValue fresh
          exact Or.inr ⟨_, _, step, afterValid, extension⟩

theorem interpreted_request_progress
    (valid : CallableJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (isValue : operand.IsValue) (resolved : stack.erase.resolve requested = some target) :
    ∃ next after, NamedAccessStep ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      CallableJoint.Valid declarations policy next ambient after result outgoing bound ∧
      CallableJoint.RegistryExtends registry next := by
  rcases request_progress valid isValue with ⟨exported, missing⟩ | next
  · simp [resolved] at missing
  · exact next

theorem closed_request_progress
    (valid : CallableJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      result [] bound)
    (isValue : operand.IsValue) :
    ∃ next after, NamedAccessStep ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      CallableJoint.Valid declarations policy next ambient after result [] bound ∧
      CallableJoint.RegistryExtends registry next := by
  rcases request_progress valid isValue with ⟨exported, missing⟩ | next
  · cases exported
  · exact next

theorem resume_progress
    (valid : CallableJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (isValue : value.IsValue) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      CallableJoint.Valid declarations policy registry ambient after result outgoing bound := by
  obtain ⟨current, demand, code, control, accessible, balance, unique⟩ := valid.joint.usage
  obtain ⟨owner, resolved, same⟩ := ScopedPortJoint.resume_demand_supplies_owner code
  have present : owner ∈ ScopedExecution.activeTickets stack := accessible (same ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := ScopedPortJoint.active_ticket_has_boundary present
  subst stack
  exact ⟨_, CallableJoint.resume_preserves valid resolved isValue⟩

def SupportedHead : Code → Prop
  | .discard _ | .cleanup _ _ => False
  | _ => True

theorem supported_head
    (checked : CallableContracts.Derives declarations environment world ticket code contract) : SupportedHead code := by
  cases checked with
  | leaf isValue => cases code <;> simp_all [SupportedHead, Code.IsValue]
  | «variable» | pair | lambda | app | bind | branch | perform | resource | resume | handle => trivial

theorem focus_boundary (focus : Focus whole child context) :
    NoSourceRequest ⟨whole, scope, stack⟩ := by
  intro requested operation operand capture tail handler same isValue cut
  exact False.elim (ScopedPortProgress.focused_request_has_nonvalue_operand focus same isValue)

theorem return_access_checks
    (checked : ConfigurationReturns declarations registry world configuration output)
    (boundary : NoSourceRequest configuration) : AccessChecks configuration ambient := by
  obtain ⟨environment, ticket, bound, scope, code, stack⟩ := checked
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    rw [same] at code stack
    cases stack with
    | cell saved absent rest => exact fun member => absent (CallableContracts.value_support code closed.1 member)
  · intro requested operation operand scope whole cap tail handler same cut closed
    exact False.elim (boundary requested operation operand cap tail handler
      (congrArg Configuration.expression same) closed.1 (same.symm ▸ cut))
  · intro binder owner scope caller input answer front cap tail plan same resolved built
    rw [same] at code
    exact False.elim (supported_head code)

theorem branch_results
    (checked : ConfigurationReturns declarations registry world
      ⟨.branch (.boolean condition) yes no, scope, stack⟩ output) :
    ConfigurationReturns declarations registry world ⟨if condition then yes else no, scope, stack⟩ output := by
  obtain ⟨environment, ticket, contract, scopeChecked, code, rest⟩ := checked
  refine ⟨environment, ticket, contract, scopeChecked, ?_, rest⟩
  cases code with
  | leaf isValue => cases isValue
  | branch conditionChecked yesChecked noChecked =>
      cases condition
      · exact noChecked
      · exact yesChecked

/-- Only the capture case needs a changed result registry. At all other
    current boundaries the same records survive the actual raw event. -/
theorem raw_preserves_results
    (step : RawStep before after created discharged)
    (fresh : (issued ++ created).Nodup)
    (checked : ConfigurationReturns declarations registry (resourceWorld issued) before output)
    (boundary : NoSourceRequest before) :
    ConfigurationReturns declarations registry (resourceWorld (issued ++ created)) after output := by
  cases step with
  | focus plain focus tail => simpa using (CallableFrames.focus_step focus checked).2
  | plug plain value closed scope tail => simpa using (CallableFrames.plug_step checked closed).2
  | bind name value body scope tail closed suffix => simpa using (CallableFrames.bind_step checked closed suffix).2
  | beta parameter body argument scope tail closed closure => simpa using (CallableFrames.beta_step checked closed closure).2
  | enterCleanup | discard =>
      obtain ⟨environment, ticket, bound, scope, code, stack⟩ := checked
      exact False.elim (supported_head code)
  | ifTrue => simpa using branch_results (condition := true) checked
  | ifFalse => simpa using branch_results (condition := false) checked
  | enterHandler handler body tail => simpa using (CallableFrames.handler_entry_step checked).2
  | leaveHandler handler value closed scope tail => simpa using (CallableFrames.handler_return_step checked closed).2
  | enterCell binder identity payload body scope answer tail closed =>
      have unused : identity ∉ resourceWorld issued := by
        intro member
        exact (List.nodup_append.mp fresh).2.2 (.resource identity)
          (ScopedTyping.mem_resource_world.mp member) (.resource identity) (by simp) rfl
      simpa [resource_world_append, resourceWorld] using (CallableFrames.resource_step checked unused).2
  | leaveCell identity payload answer savedScope scope value closed tail =>
      simpa using (CallableFrames.cell_return_step checked closed).2.2
  | startCleanup | finishCleanup | finishClose | retire =>
      obtain ⟨environment, ticket, bound, scope, code, stack⟩ := checked
      cases stack
  | capture requested operation parameter binder owner operand body scope whole cap tail handler answer cut clause closed ready =>
      exact False.elim (boundary requested operation operand cap tail handler rfl closed.1 cut)
  | resume binder owner scope caller input answer front capture tail value closed resolved =>
      simpa using (CallableFrames.resume_step resolved checked closed).2
  | leaveClause owner answer value closed scope caller tail =>
      simpa using (CallableFrames.clause_return_step checked closed).2
  | readCell identity payload scope before after selected =>
      simpa using builtin_request_preserves_results (.readCell identity payload scope before after selected) rfl trivial checked
  | writeCell identity old new scope before after selected =>
      simpa using builtin_request_preserves_results (.writeCell identity old new scope before after selected) rfl ⟨trivial, trivial⟩ checked

theorem named_preserves_results
    (step : NamedAccessStep ambient before after)
    (checked : ConfigurationReturns declarations registry (resourceWorld before.execution.issued)
      before.execution.configuration output)
    (boundary : NoSourceRequest before.execution.configuration) :
    ConfigurationReturns declarations registry (resourceWorld after.execution.issued)
      after.execution.configuration output := by
  cases step.execution with
  | event after created discharged raw fresh freshHandlers => exact raw_preserves_results raw fresh checked boundary

theorem join_non_capture
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound)
    (boundary : NoSourceRequest before.execution.configuration)
    (step : NamedAccessStep ambient before after)
    (joint : ScopedPortJoint.Valid (signature declarations) policy registry.joint ambient after result outgoing) :
    CallableJoint.Valid declarations policy registry ambient after result outgoing bound :=
  ⟨joint, named_preserves_results step valid.results boundary⟩

theorem current_progress
    (valid : CallableJoint.Valid declarations policy registry ambient before result outgoing bound) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ScopedPortProgress.OutwardRequest before.execution.configuration outgoing ∨
      ∃ next after, NamedAccessStep ambient before after ∧
        CallableJoint.Valid declarations policy next ambient after result outgoing bound ∧
        CallableJoint.RegistryExtends registry next := by
  obtain ⟨⟨⟨expression, scope, stack⟩, issued, completed⟩, activations⟩ := before
  obtain ⟨input, current, ports⟩ := effect_configuration_has_types valid.joint.effects
  have admitted : SupportedHead expression := by
    obtain ⟨environment, ticket, bound, scope, code, rest⟩ := valid.results
    exact supported_head code
  have form : ScopedPortProgress.CurrentForm expression := by
    cases current with
    | checked scopeTyped typed => exact ScopedPortProgress.typed_current_form typed
  cases form with
  | value isValue =>
      have boundary := GenerativeProgress.value_boundary (configuration := ⟨expression, scope, stack⟩) isValue
      rcases ScopedPortJoint.checked_value_progress valid.joint isValue
        (return_access_checks valid.results boundary) with terminal | next
      · exact Or.inl ⟨isValue, terminal⟩
      · obtain ⟨after, step, joint⟩ := next
        exact Or.inr (Or.inr ⟨registry, after, step, join_non_capture valid boundary step joint,
          CallableJoint.registry_extends_refl _⟩)
  | focus position =>
      obtain ⟨plain, step, joint⟩ := ScopedPortJoint.focus_constructs_joint_configuration valid.joint position
      exact Or.inr (Or.inr ⟨registry, _, step, join_non_capture valid (focus_boundary position) step joint,
        CallableJoint.registry_extends_refl _⟩)
  | bind isValue =>
      obtain ⟨after, step, joint⟩ := ScopedPortProgress.bind_value_progress valid.joint isValue
      exact Or.inr (Or.inr ⟨registry, after, step, join_non_capture valid
        (GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)) step joint,
        CallableJoint.registry_extends_refl _⟩)
  | branch isValue =>
      obtain ⟨after, step, joint⟩ := ScopedPortProgress.branch_value_progress valid.joint isValue
      exact Or.inr (Or.inr ⟨registry, after, step, join_non_capture valid
        (GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)) step joint,
        CallableJoint.registry_extends_refl _⟩)
  | request isValue =>
      rcases request_progress valid isValue with outward | next
      · exact Or.inr (Or.inl ⟨_, _, _, rfl, isValue, outward⟩)
      · exact Or.inr (Or.inr next)
  | handler =>
      obtain ⟨activation, fresh⟩ := ScopedPortProgress.fresh_activation_exists valid.joint.names.unique
      obtain ⟨handler, active, step, joint⟩ := ScopedPortJoint.handler_entry_constructs_joint_configuration valid.joint fresh
      exact Or.inr (Or.inr ⟨registry, _, step, join_non_capture valid
        (GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)) step joint,
        CallableJoint.registry_extends_refl _⟩)
  | resume isValue =>
      obtain ⟨after, step, afterValid⟩ := resume_progress valid isValue
      exact Or.inr (Or.inr ⟨registry, after, step, afterValid, CallableJoint.registry_extends_refl _⟩)
  | resource isValue =>
      obtain ⟨after, step, joint⟩ := ScopedPortJoint.resource_entry_constructs_joint_configuration valid.joint isValue
      exact Or.inr (Or.inr ⟨registry, after, step, join_non_capture valid
        (GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)) step joint,
        CallableJoint.registry_extends_refl _⟩)
  | app functionValue argumentValue =>
      obtain ⟨after, step, joint⟩ := ScopedPortProgress.application_value_progress valid.joint functionValue argumentValue
      exact Or.inr (Or.inr ⟨registry, after, step, join_non_capture valid
        (GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)) step joint,
        CallableJoint.registry_extends_refl _⟩)
  | discard | cleanup => exact False.elim admitted

theorem closed_progress
    (valid : CallableJoint.Valid declarations policy registry ambient before result [] bound) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ∃ next after, NamedAccessStep ambient before after ∧
        CallableJoint.Valid declarations policy next ambient after result [] bound ∧
        CallableJoint.RegistryExtends registry next := by
  rcases current_progress valid with terminal | outward | next
  · exact Or.inl terminal
  · obtain ⟨requested, operation, operand, same, value, exported, missing⟩ := outward
    cases exported
  · exact Or.inr next

theorem initial_progress
    (typed : Typed (signature declarations) [] TypeEnv.empty .none [] expression result)
    (used : Uses policy .none .available expression .available)
    (support : Syntax.resourceDependencies expression.dependencies = [])
    (checked : CallableContracts.Derives declarations environment [] .none expression bound) :
    let initial : NamedState := ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩
    ScopedPortProgress.Terminal initial.execution.configuration ∨
      ∃ registry after, NamedAccessStep [] initial after ∧
        CallableJoint.Valid declarations policy registry [] after result [] bound ∧
        CallableJoint.RegistryExtends (fun _ => none) registry :=
  closed_progress (CallableJoint.initial_configuration_valid typed used support checked)


theorem terminal_accounting
    (valid : CallableJoint.Valid declarations policy registry ambient state result outgoing bound)
    (terminal : ScopedPortProgress.Terminal state.execution.configuration) :
    state.execution.issued.Perm state.execution.completed ∧ state.execution.completed.Nodup := by
  have ledger := valid.joint.ledger
  have completed := ledger_no_double_completion ledger
  obtain ⟨⟨⟨value, scope, stack⟩, issued, done⟩, activations⟩ := state
  obtain ⟨isValue, rfl⟩ := terminal
  exact ⟨by simpa [RunState.erase, Stack.erase, Control.owners] using ledger.1, completed⟩

theorem terminal_result_support
    (valid : CallableJoint.Valid declarations policy registry ambient state result outgoing bound)
    (terminal : ScopedPortProgress.Terminal state.execution.configuration) :
    Syntax.resourceDependencies state.execution.configuration.expression.dependencies ⊆ bound.storageOf := by
  obtain ⟨environment, ticket, input, scope, code, stack⟩ := valid.results
  rw [terminal.2] at stack
  cases stack with
  | nil => exact CallableContracts.value_support code terminal.1

end Ash.OneShot.CallableProgress

#print axioms Ash.OneShot.CallableProgress.cell_update_preserves_results
#print axioms Ash.OneShot.CallableProgress.request_storage_contract
#print axioms Ash.OneShot.CallableProgress.builtin_request_preserves_results
#print axioms Ash.OneShot.CallableProgress.request_progress
#print axioms Ash.OneShot.CallableProgress.interpreted_request_progress
#print axioms Ash.OneShot.CallableProgress.closed_request_progress
#print axioms Ash.OneShot.CallableProgress.resume_progress
#print axioms Ash.OneShot.CallableProgress.supported_head
#print axioms Ash.OneShot.CallableProgress.focus_boundary
#print axioms Ash.OneShot.CallableProgress.return_access_checks
#print axioms Ash.OneShot.CallableProgress.branch_results
#print axioms Ash.OneShot.CallableProgress.raw_preserves_results
#print axioms Ash.OneShot.CallableProgress.named_preserves_results
#print axioms Ash.OneShot.CallableProgress.join_non_capture
#print axioms Ash.OneShot.CallableProgress.current_progress
#print axioms Ash.OneShot.CallableProgress.closed_progress
#print axioms Ash.OneShot.CallableProgress.initial_progress
#print axioms Ash.OneShot.CallableProgress.terminal_accounting
#print axioms Ash.OneShot.CallableProgress.terminal_result_support
