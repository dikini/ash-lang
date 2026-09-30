import PayloadBoundary

/-!
Evaluated requests and resumes progress from the combined structural invariant.
Selection follows the actual ordered stack. This is a current-state theorem;
it does not establish complete initial admission or cleanup/callable support.
-/

namespace Ash.OneShot.ClauseProgress
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedPorts
open DeclarationResults (signature)
open ClauseFrames (ConfigurationReturns StackReturns)

theorem cell_update_preserves_results
    (update : CellUpdate identity old new before after)
    (checked : StackReturns declarations registry world before input output) :
    StackReturns declarations registry world after input output := by
  induction update generalizing input output with
  | hit => cases checked with
      | cell scope absent rest => exact .cell scope absent rest
  | push miss next ih => cases checked with
      | plain scope context included rest => exact .plain scope context included (ih rest)
      | cell scope absent rest => exact .cell scope absent (ih rest)
      | handler scope clauses included rest => exact .handler scope clauses included (ih rest)
  | live next ih => cases checked with
      | live known scope saved included rest => exact .live known scope saved included (ih rest)
  | spent next ih => cases checked with
      | spent known scope included rest => exact .spent known scope included (ih rest)

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
      rename_i identity payload before after caller
      obtain ⟨environment, ticket, bound, scope, code, stack⟩ := checked
      have closed : ScopedExpressions.ClosedValue (.integer payload) := ⟨trivial, rfl, by intro dependency member; cases member⟩
      exact ⟨environment, ticket, bound, scope, .existing (.leaf (Or.inl trivial) rfl
        (GenerativeFrames.closed_value_check closed (List.nil_subset _))),
        cell_update_preserves_results selected stack⟩
  | write selected =>
      obtain ⟨environment, ticket, bound, scope, code, stack⟩ := checked
      have closed : ScopedExpressions.ClosedValue .unit := ⟨trivial, rfl, by intro dependency member; cases member⟩
      exact ⟨environment, ticket, bound, scope, .existing (.leaf (Or.inl trivial) rfl
        (GenerativeFrames.closed_value_check closed (List.nil_subset _))),
        cell_update_preserves_results selected stack⟩

theorem request_progress
    (valid : ClauseJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (isValue : operand.IsValue) :
    (requested ∈ outgoing ∧ stack.erase.resolve requested = none) ∨
      ∃ next after, NamedAccessStep ambient
        ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
        ClauseJoint.Valid declarations policy next ambient after result outgoing bound ∧
        ClauseJoint.RegistryExtends registry next := by
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
            ClauseJoint.registry_extends_refl _⟩
      | source activation =>
          obtain ⟨cap, tail, handler, cut, active⟩ := ScopedTyping.handler_selection_of_resolution stack resolved
          obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) valid.joint.ledger.2
          obtain ⟨parameter, binder, body, output, residual, record, contract, selected, known, extension, step, afterValid⟩ :=
            PayloadBoundary.capture_without_payload_premise cut valid isValue fresh
          exact Or.inr ⟨_, _, step, afterValid, extension⟩

theorem interpreted_request_progress
    (valid : ClauseJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (isValue : operand.IsValue) (resolved : stack.erase.resolve requested = some target) :
    ∃ next after, NamedAccessStep ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      ClauseJoint.Valid declarations policy next ambient after result outgoing bound ∧
      ClauseJoint.RegistryExtends registry next := by
  rcases request_progress valid isValue with ⟨exported, missing⟩ | next
  · simp [resolved] at missing
  · exact next

theorem closed_request_progress
    (valid : ClauseJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      result [] bound)
    (isValue : operand.IsValue) :
    ∃ next after, NamedAccessStep ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      ClauseJoint.Valid declarations policy next ambient after result [] bound ∧
      ClauseJoint.RegistryExtends registry next := by
  rcases request_progress valid isValue with ⟨exported, missing⟩ | next
  · cases exported
  · exact next

theorem resume_progress
    (valid : ClauseJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (isValue : value.IsValue) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      ClauseJoint.Valid declarations policy registry ambient after result outgoing bound := by
  obtain ⟨current, demand, code, control, accessible, balance, unique⟩ := valid.joint.usage
  obtain ⟨owner, resolved, same⟩ := ScopedPortJoint.resume_demand_supplies_owner code
  have present : owner ∈ ScopedExecution.activeTickets stack := accessible (same ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := ScopedPortJoint.active_ticket_has_boundary present
  subst stack
  exact ⟨_, ClauseJoint.resume_preserves valid resolved isValue⟩

end Ash.OneShot.ClauseProgress

#print axioms Ash.OneShot.ClauseProgress.cell_update_preserves_results
#print axioms Ash.OneShot.ClauseProgress.builtin_request_preserves_results
#print axioms Ash.OneShot.ClauseProgress.request_progress
#print axioms Ash.OneShot.ClauseProgress.interpreted_request_progress
#print axioms Ash.OneShot.ClauseProgress.closed_request_progress
#print axioms Ash.OneShot.ClauseProgress.resume_progress
