import ResultCodeSubstitution

/-!
Actual typed values with first-order declared ports have exactly the explicit
resource support of those ports. This is independent of unknown result metadata
and is one sufficient source of release evidence, not a source restriction.
-/

namespace Ash.OneShot.ScopedPorts
open Syntax ScopedExpressions ScopedExecution

inductive Port.FirstOrder : Port → Prop where
  | unit : Port.FirstOrder .unit
  | boolean : Port.FirstOrder .boolean
  | integer : Port.FirstOrder .integer
  | reference : Port.FirstOrder (.reference identity)
  | product : Port.FirstOrder left → Port.FirstOrder right → Port.FirstOrder (.product left right)

/-- Canonical shapes, not the absence of identities in an arbitrary port,
    justify this equality. Function ports deliberately have no rule. -/
theorem typed_first_order_value_support
    (typed : Typed signature world environment ticket allowed value type)
    (isValue : value.IsValue) (shape : type.FirstOrder) :
    resourceDependencies value.dependencies = type.resources := by
  induction typed using Typed.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | unit | boolean | integer | reference => rfl
  | pair _ _ ihLeft ihRight =>
      cases shape with
      | product left right =>
          have leftBound := ihLeft isValue.1 left
          have rightBound := ihRight isValue.2 right
          simp only [resourceDependencies] at leftBound rightBound
          simp only [Code.dependencies, resourceDependencies, List.filterMap_append, Port.resources, leftBound, rightBound]
  | lambda => cases shape
  | «variable» | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases isValue
  | nil | cons => trivial

theorem typed_first_order_return_excludes_resource
    (typed : Typed signature world environment ticket allowed value type)
    (isValue : value.IsValue) (shape : type.FirstOrder) (excluded : identity ∉ type.resources) :
    identity ∉ resourceDependencies value.dependencies := by
  rw [typed_first_order_value_support typed isValue shape]
  exact excluded

theorem typed_unit_value_has_empty_support
    (typed : Typed signature world environment ticket allowed value .unit) (isValue : value.IsValue) :
    resourceDependencies value.dependencies = [] := typed_first_order_value_support typed isValue .unit

theorem typed_first_order_cell_return_excludes_identity
    (typed : ConfigurationTyped signature tickets world
      ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ result)
    (isValue : value.IsValue) (shape : (eraseType answer).FirstOrder) :
    identity ∉ resourceDependencies value.dependencies := by
  obtain ⟨input, expression, stack⟩ := typed
  cases stack with
  | push frame rest => cases frame with
      | cell known noEscape => cases expression with
          | checked scope typed => exact typed_first_order_return_excludes_resource typed isValue shape noEscape

/-- A structural certificate about the next control frame, sufficient only for
    the current value transition. It does not certify future source returns. -/
def FirstOrderRelease : Stack → Prop
  | .push (.cell _ _ _ answer) _ => (eraseType answer).FirstOrder
  | _ => True

theorem first_order_value_access_checks
    (typed : ConfigurationTyped signature tickets world configuration result)
    (isValue : configuration.expression.IsValue) (shape : FirstOrderRelease configuration.stack) :
    AccessChecks configuration ambient := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    rw [same] at typed shape
    exact typed_first_order_cell_return_excludes_identity typed closed.1 shape
  · intro requested operation operand scope whole cap tail handler same cut closed
    rw [same] at isValue
    cases isValue
  · intro binder owner scope caller input answer front cap tail plan same resolve built
    rw [same] at isValue
    cases isValue

theorem first_order_value_progress
    (valid : ScopedPortJoint.Valid signature policy registry ambient before result outgoing)
    (isValue : before.execution.configuration.expression.IsValue)
    (shape : FirstOrderRelease before.execution.configuration.stack) :
    before.execution.configuration.stack = .nil ∨
    ∃ after, NamedAccessStep ambient before after ∧
      ScopedPortJoint.Valid signature policy registry ambient after result outgoing :=
  ScopedPortJoint.checked_value_progress valid isValue
    (first_order_value_access_checks (effect_configuration_has_types valid.effects) isValue shape)

theorem first_order_ready_value_progress
    (ready : ScopedPortPrepared.Ready (withCellSignatures users) policy registry ambient before result outgoing)
    (isValue : before.execution.configuration.expression.IsValue)
    (shape : FirstOrderRelease before.execution.configuration.stack) :
    ScopedPortProgress.Terminal before.execution.configuration ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortPrepared.Ready (withCellSignatures users) policy registry ambient after result outgoing :=
  ScopedPortPrepared.checked_ready_value_progress ready isValue
    (first_order_value_access_checks (effect_configuration_has_types ready.joint.effects) isValue shape)

namespace BoundExamples

/-- A port may contain no identity and still classify a retaining closure. -/
theorem empty_port_resources_do_not_bound_callable_storage :
    Examples.callbackPort.resources = [] ∧
    Typed Examples.signature [0] TypeEnv.empty .none [] (ScopedSignatureGap.Examples.payload (.activation 0)) Examples.callbackPort ∧
    resourceDependencies (ScopedSignatureGap.Examples.payload (.activation 0)).dependencies = [0] ∧
    ¬ Examples.callbackPort.FirstOrder := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · exact Examples.payload_typed (by simp)
  · intro impossible
    cases impossible

open ScopedSignatureGap.Examples

theorem callable_request_checks :
    AccessChecks ⟨.perform (Instantiation.freezeEffect send) 0 (payload (.activation 0)),
      .none, .push (.handler handler) outside⟩ [] := by
  constructor
  · intro identity content answer savedScope scope value tail same closed
    cases same
  · intro requested operation argument scope whole cap tail selected same cut closed
    have expression := congrArg Configuration.expression same
    have instanceEq := freeze_effect_injective (Code.perform.inj expression).1
    subst requested
    cases same
    cases cut with
    | hit => simpa using actual_boundary_supports_payload.2.1
    | push frame rest cap tail handler miss next => exact False.elim (miss rfl)
  · intro binder owner scope caller input answer front cap tail plan same resolve built
    cases same

theorem callable_source_access_trace :
    AccessTrace [] ⟨program, .none, .nil⟩ ⟨.unit, .none, .nil⟩
      [.resource 0, .ticket 7] [.resource 0, .ticket 7] := by
  have unitClosed := ScopedExecution.Examples.unit_closed
  have entry := RawStep.enterCell 4 0 41 body .none .unit .nil program_resource_closed
  have install := RawStep.enterHandler handler
    (.perform (Instantiation.freezeEffect send) 0 (payload (.activation 0))) outside
  have request := RawStep.capture send 0 5 9 7 (payload (.activation 0)) (.resume 9 .unit)
    .none (.push (.handler handler) outside) capture outside handler .unit
    actual_boundary_supports_payload.1 .hit payload_closed
    (by intro name member; simp [Code.dependencies] at member)
  have resume := RawStep.resume 9 7 (.ticket 9 7) .none .unit .unit .nil capture outside
    .unit unitClosed rfl
  have leave := RawStep.leaveHandler handler .unit unitClosed (.ticket 9 7)
    (.spent 7 .unit .none outside)
  have finish := RawStep.leaveClause 7 .unit .unit unitClosed .none .none outside
  have release := RawStep.leaveCell 0 41 .unit .none .none .unit unitClosed .nil
  have entryChecks : AccessChecks ⟨program, .none, .nil⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [program, Code.IsValue])
      (by intro requested operation operand same; cases same) (by intro binder same; cases same)
  have installChecks : AccessChecks ⟨openedBody 0, .none, outside⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [openedBody, Code.IsValue])
      (by intro requested operation operand same; cases same) (by intro binder same; cases same)
  have leaveChecks := first_order_value_access_checks RetainedExamples.resumed_typed (by trivial) (by trivial) (ambient := [])
  have finishChecks := first_order_value_access_checks RetainedExamples.completion_states_typed.1 (by trivial) (by trivial) (ambient := [])
  have releaseChecks := first_order_value_access_checks RetainedExamples.completion_states_typed.2.1
    (by trivial) Port.FirstOrder.unit (ambient := [])
  exact .next entry entryChecks (.next install installChecks (.next request callable_request_checks
    (.next resume resume_access_checks (.next leave leaveChecks (.next finish finishChecks
      (.next release releaseChecks (.refl _)))))))

theorem callable_source_admitted_execution :
    AccessRunSteps [] ⟨⟨program, .none, .nil⟩, [], []⟩
      ⟨⟨.unit, .none, .nil⟩, [.resource 0, .ticket 7], [.resource 0, .ticket 7]⟩ :=
  access_trace_enacts callable_source_access_trace (by decide)

/-- The complete same-source execution combines derived boundary checks,
    canonical Unit release, and independent ownership conservation. -/
theorem callable_source_final_ledger_and_support :
    Ledger (RunState.erase ⟨⟨.unit, .none, .nil⟩, [.resource 0, .ticket 7], [.resource 0, .ticket 7]⟩) ∧
    AccessValid ⟨.unit, .none, .nil⟩ [] :=
  access_run_joint_preservation callable_source_admitted_execution
    ScopedPortJoint.Examples.safe_source_valid.ledger ScopedPortJoint.Examples.safe_source_valid.support

end BoundExamples
end Ash.OneShot.ScopedPorts

namespace Ash.OneShot.ResultSummaries

namespace ObservationGap

def target (identity : Nat) : Summary := .callable (.resource identity) (.resource identity)
def pending (identity : Nat) : Summary := .application (target identity) .scalar

theorem closed_pending_applications : (pending 7).Scoped 0 ∧ (pending 8).Scoped 0 := by
  trivial

theorem pending_applications_storage_equivalent : StorageEq (pending 7) (pending 8) := fun _ => rfl

theorem enclosing_callable_results_equivalent :
    ResultEq (.callable (pending 7) .scalar) (.callable (pending 8) .scalar) :=
  .callable pending_applications_storage_equivalent .scalar

theorem unfolded_pending_support_differs :
    (callResult (target 7) .scalar).support = some [7] ∧
    (callResult (target 8) .scalar).support = some [8] ∧
    (callResult (target 7) .scalar).support ≠ (callResult (target 8) .scalar).support := by
  decide

/-- Existing StorageEq is not a congruence for even this additional unfolding
    observation. The antecedent is satisfied by closed well-scoped metadata. -/
theorem current_comparison_does_not_justify_unfolding :
    ¬ (∀ (first second argument : Summary),
      StorageEq (.application first argument) (.application second argument) →
      (callResult first argument).support = (callResult second argument).support) := by
  intro sound
  exact unfolded_pending_support_differs.2.2 (sound (target 7) (target 8) .scalar pending_applications_storage_equivalent)

end ObservationGap
end Ash.OneShot.ResultSummaries

#print axioms Ash.OneShot.ScopedPorts.typed_first_order_value_support
#print axioms Ash.OneShot.ScopedPorts.typed_first_order_return_excludes_resource
#print axioms Ash.OneShot.ScopedPorts.typed_unit_value_has_empty_support
#print axioms Ash.OneShot.ScopedPorts.typed_first_order_cell_return_excludes_identity
#print axioms Ash.OneShot.ScopedPorts.first_order_value_access_checks
#print axioms Ash.OneShot.ScopedPorts.first_order_value_progress
#print axioms Ash.OneShot.ScopedPorts.first_order_ready_value_progress
#print axioms Ash.OneShot.ScopedPorts.BoundExamples.empty_port_resources_do_not_bound_callable_storage
#print axioms Ash.OneShot.ScopedPorts.BoundExamples.callable_request_checks
#print axioms Ash.OneShot.ScopedPorts.BoundExamples.callable_source_access_trace
#print axioms Ash.OneShot.ScopedPorts.BoundExamples.callable_source_admitted_execution
#print axioms Ash.OneShot.ScopedPorts.BoundExamples.callable_source_final_ledger_and_support
#print axioms Ash.OneShot.ResultSummaries.ObservationGap.closed_pending_applications
#print axioms Ash.OneShot.ResultSummaries.ObservationGap.pending_applications_storage_equivalent
#print axioms Ash.OneShot.ResultSummaries.ObservationGap.enclosing_callable_results_equivalent
#print axioms Ash.OneShot.ResultSummaries.ObservationGap.unfolded_pending_support_differs
#print axioms Ash.OneShot.ResultSummaries.ObservationGap.current_comparison_does_not_justify_unfolding
