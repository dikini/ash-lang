import ClauseExecution

/-!
Preservation for a supplied capture event, not just an existentially selected
one. Its continuation-input annotation is checked against the declared port.
The current finite-port fragment makes that annotation canonical.
-/

namespace Ash.OneShot.CaptureAnnotations
open Instantiation ScopedExpressions ScopedExecution ScopedPorts
open DeclarationResults (signature)

theorem clause_selection_unique
    (first : ClauseAt operation clauses parameter binder body)
    (second : ClauseAt operation clauses otherParameter otherBinder otherBody) :
    parameter = otherParameter ∧ binder = otherBinder ∧ body = otherBody := by
  induction first with
  | hit => cases second with
      | hit => exact ⟨rfl, rfl, rfl⟩
      | pass different next => exact False.elim (different rfl)
  | pass different next ih => cases second with
      | hit => exact False.elim (different rfl)
      | pass otherDifferent otherNext => exact ih otherNext

theorem first_order_annotation (shape : (eraseType annotation).FirstOrder) :
    embedPort (eraseType annotation) = annotation := by
  induction annotation with
  | unit | boolean | integer | reference => rfl
  | product left right ihLeft ihRight =>
      cases shape with
      | product leftShape rightShape =>
          simp only [eraseType, embedPort, ihLeft leftShape, ihRight rightShape]
  | function => cases shape

theorem finite_annotation
    (finite : ClauseResults.PortBound port bound) (same : eraseType annotation = port) :
    annotation = embedPort port := by
  have shape := (ContinuationBounds.port_bound_finite port finite).1
  rw [← same] at shape
  simpa [same] using (first_order_annotation shape).symm

theorem selected_output_bound
    (valid : ClauseJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (known : signature declarations requested operation = some (input, output)) :
    ∃ resources, ClauseResults.PortBound output resources := by
  obtain ⟨environment, ticket, inputBound, scopeChecked, code, stack⟩ := valid.results
  obtain ⟨savedEnvironment, savedTicket, answer, handlerScope, clauses, saved, outside⟩ :=
    ClauseFrames.handler_cut_certificate cut stack
  obtain ⟨actualInput, actualOutput, argumentBound, resumeBound, actual, inputFinite, outputFinite, bodyChecked⟩ :=
    ClauseResults.selected_clause selected clauses
  rw [ScopedTyping.handler_cut_instance cut] at actual
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans actual))
  exact ⟨resumeBound, outputFinite⟩

/-- The supplied clause, ticket and raw input annotation determine the exact
    successor. No successor validity or access premise is supplied. -/
theorem selected_capture_preserves
    (valid : ClauseJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (known : signature declarations requested operation = some (input, eraseType annotation))
    (isValue : operand.IsValue)
    (fresh : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ record, ClauseJoint.RegistryExtends registry (registry.insert owner record) ∧
      let before : NamedState := ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner annotation handler.answer capture handler.scope tail⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) ∧
      ClauseJoint.Valid declarations policy (registry.insert owner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket owner] []) result outgoing bound := by
  obtain ⟨resources, finite⟩ := selected_output_bound valid cut selected known
  have canonical := finite_annotation finite rfl
  obtain ⟨chosenParameter, chosenBinder, chosenBody, output, residual, record, contract, chosen,
    ⟨actualInput, actualKnown⟩, extended, step, afterValid⟩ :=
      PayloadBoundary.capture_without_payload_premise cut valid isValue fresh
  obtain ⟨rfl, rfl, rfl⟩ := clause_selection_unique selected chosen
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans actualKnown))
  exact ⟨record, extended, by simpa [← canonical] using step, by simpa [← canonical] using afterValid⟩

/-- Local annotation checking on the existing capture constructor. All
    premises inspect the event's syntax, selection and declaration lookup. -/
inductive DeclaredCapture (declarations : DeclarationRegistry) :
    Configuration → Configuration → Nat → Prop where
  | capture
      (cut : HandlerCut requested whole capture tail handler)
      (selected : ClauseAt operation handler.clauses parameter binder body)
      (known : signature declarations requested operation = some (input, eraseType annotation))
      (closed : ClosedValue operand) (ready : ClosedExcept parameter body) :
      DeclaredCapture declarations
        ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner annotation handler.answer capture handler.scope tail⟩ owner

theorem declared_capture_executes (event : DeclaredCapture declarations before after owner) :
    RawStep before after [.ticket owner] [] := by
  cases event with
  | capture cut selected known closed ready => exact .capture _ _ _ _ _ _ _ _ _ _ _ _ _ cut selected closed ready

theorem declared_capture_preserves
    (event : DeclaredCapture declarations before.execution.configuration after owner)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound)
    (fresh : (before.execution.issued ++ [Owner.ticket owner]).Nodup) :
    ∃ record, ClauseJoint.RegistryExtends registry (registry.insert owner record) ∧
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) ∧
      ClauseJoint.Valid declarations policy (registry.insert owner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket owner] []) result outgoing bound := by
  obtain ⟨⟨configuration, issued, completed⟩, activations⟩ := before
  cases event with
  | capture cut selected known closed ready =>
      exact selected_capture_preserves valid cut selected known closed.1 fresh

namespace Examples
open PayloadBoundary.Examples

def badAfter : Configuration :=
  ⟨.resume 9 (.integer 17), .ticket 9 5, .live 5 .unit .integer saved .none outside⟩

def badState : NamedState := ScopedPortJoint.advanceState initial badAfter [.ticket 5] []

theorem matching_capture_declared : DeclaredCapture declarations request
    ⟨.resume 9 (.integer 17), .ticket 9 5, .live 5 .integer .integer saved .none outside⟩ 5 := by
  exact .capture selected_cut .hit operation_known
    ⟨trivial, rfl, by intro dependency member; simp [Code.dependencies] at member; subst dependency; trivial⟩
    (by intro name member; simp [Code.dependencies] at member)

theorem mismatched_capture_executes : RawStep request badAfter [.ticket 5] [] := by
  exact .capture family 0 5 9 5 (.resourceRef (.activation 7)) (.resume 9 (.integer 17))
    .none whole saved outside handler .unit selected_cut .hit
    ⟨trivial, rfl, by intro dependency member; simp [Code.dependencies] at member; subst dependency; trivial⟩
    (by intro name member; simp [Code.dependencies] at member)

theorem mismatched_capture_has_access : NamedAccessStep [] initial badState := by
  exact ⟨.event initial badAfter [.ticket 5] [] mismatched_capture_executes (by decide) (by decide),
    capture_checks_are_derived⟩

theorem mismatched_capture_preserves_ownership : Ledger badState.execution.erase :=
  (named_access_step_preserves mismatched_capture_has_access initial_valid.joint.ledger
    initial_valid.joint.names initial_valid.joint.support).1

theorem mismatched_capture_not_typed (tickets : TicketSignatures) (world : List Nat) :
    ¬ ConfigurationTyped (signature declarations) tickets world badAfter .integer := by
  intro typed
  obtain ⟨input, expression, stack⟩ := typed
  cases expression with
  | checked scope current => cases current with
      | resume operand effects formed => cases scope with
          | bound known => cases stack with
              | live recorded caller saved rest =>
                  obtain ⟨rfl, sameAnswer⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans recorded))
                  cases operand

theorem mismatched_capture_not_valid (registry : ClauseJoint.Registry) :
    ¬ ClauseJoint.Valid declarations policy registry [] badState .integer [] [] := by
  intro valid
  exact mismatched_capture_not_typed _ _ (effect_configuration_has_types valid.joint.effects)

theorem mismatched_capture_not_declared : ¬ DeclaredCapture declarations request badAfter 5 := by
  intro event
  obtain ⟨record, extended, step, valid⟩ := declared_capture_preserves event initial_valid (by decide)
  exact mismatched_capture_not_valid _ valid

end Examples

end Ash.OneShot.CaptureAnnotations

#print axioms Ash.OneShot.CaptureAnnotations.clause_selection_unique
#print axioms Ash.OneShot.CaptureAnnotations.first_order_annotation
#print axioms Ash.OneShot.CaptureAnnotations.finite_annotation
#print axioms Ash.OneShot.CaptureAnnotations.selected_output_bound
#print axioms Ash.OneShot.CaptureAnnotations.selected_capture_preserves
#print axioms Ash.OneShot.CaptureAnnotations.declared_capture_executes
#print axioms Ash.OneShot.CaptureAnnotations.declared_capture_preserves
#print axioms Ash.OneShot.CaptureAnnotations.Examples.matching_capture_declared
#print axioms Ash.OneShot.CaptureAnnotations.Examples.mismatched_capture_executes
#print axioms Ash.OneShot.CaptureAnnotations.Examples.mismatched_capture_has_access
#print axioms Ash.OneShot.CaptureAnnotations.Examples.mismatched_capture_preserves_ownership
#print axioms Ash.OneShot.CaptureAnnotations.Examples.mismatched_capture_not_typed
#print axioms Ash.OneShot.CaptureAnnotations.Examples.mismatched_capture_not_valid
#print axioms Ash.OneShot.CaptureAnnotations.Examples.mismatched_capture_not_declared
