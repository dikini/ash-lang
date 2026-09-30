import CaptureRecords

/-!
Preservation for supplied checked events and finite runs in the current result
fragment. Events share the existing raw machine and specify their exact registry
updates. Run constructors contain no intermediate-validity premises.
-/

namespace Ash.OneShot.CheckedEvents
open Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ScopedTyping (resourceWorld)
open DeclarationResults (signature)

inductive StableEvent : Configuration → Configuration → List Owner → Prop where
  | value (raw : RawStep before after [] discharged) (isValue : before.expression.IsValue) :
      StableEvent before after discharged
  | ordinary (step : ScopedPortJoint.OrdinaryStep before after) : StableEvent before after []
  | resume {front capture tail : Stack} (closed : ClosedValue value) (resolved : scope.resolve binder = some owner) :
      StableEvent
        ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩
        ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ [.ticket owner]

theorem stable_executes (event : StableEvent before after discharged) : RawStep before after [] discharged := by
  cases event with
  | value raw isValue => exact raw
  | ordinary step => exact ScopedPortJoint.ordinary_step_executes step
  | resume closed resolved => exact .resume _ _ _ _ _ _ _ _ _ _ closed resolved

theorem stable_boundary (event : StableEvent before after discharged) :
    GenerativeProgress.NoSourceRequest before := by
  cases event with
  | value raw isValue => exact GenerativeProgress.value_boundary isValue
  | ordinary step => cases step with
      | read selected | write selected => exact GenerativeProgress.builtin_boundary selected
      | bind | beta | ifTrue | ifFalse =>
          exact GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)
  | resume => exact GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)

theorem stable_effects
    (event : StableEvent before after discharged)
    (typed : EffectConfigurationTyped (signature declarations) tickets world before result outgoing) :
    EffectConfigurationTyped (signature declarations) tickets world after result outgoing := by
  cases event with
  | value raw isValue =>
      have closed := at_type_value_closed (effect_configuration_has_types typed).choose_spec.1 isValue
      exact raw_value_step_preserves_effect_configuration raw closed typed
  | ordinary step => exact ScopedPortJoint.ordinary_step_preserves_effects step typed
  | resume closed resolved => exact resume_preserves_effect_configuration resolved typed closed.1

theorem stable_preserves
    (event : StableEvent before.execution.configuration after discharged)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup) :
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] discharged) ∧
      ClauseJoint.Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [] discharged) result outgoing bound := by
  have raw := stable_executes event
  have boundary := stable_boundary event
  have checks := ClauseExecution.return_access_checks (ambient := ambient) valid.results boundary
  have fresh : (before.execution.issued ++ []).Nodup := by simpa [RunState.erase] using valid.joint.ledger.2
  have step : NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] discharged) :=
    ⟨.event before after [] discharged raw fresh freshHandlers, checks⟩
  obtain ⟨ledger, names, support⟩ := named_access_step_preserves step valid.joint.ledger valid.joint.names valid.joint.support
  have history := ScopedPortJoint.usage_history_iff.mpr valid.joint.registry
  have usage := raw_step_preserves_configuration_usage raw
    (usage_checks_from_allocation_and_access history fresh checks) valid.joint.usage
  have nextHistory := raw_step_preserves_usage_registry_history (policy := policy) raw history
  refine ⟨step, ⟨ledger, names, support, ?_, usage, ScopedPortJoint.usage_history_iff.mp nextHistory,
    raw_step_preserves_resource_closure raw valid.joint.closed⟩, ?_⟩
  · simpa [ScopedPortJoint.advanceState] using stable_effects event valid.joint.effects
  · exact ClauseExecution.named_preserves_results step valid.results boundary

inductive CheckedEvent (declarations : DeclarationRegistry) (policy : Syntax.TicketPolicy)
    (registry : ClauseJoint.Registry) (result : Port) (outgoing : List Instance)
    (bound : List Nat) (before : NamedState) :
    ClauseJoint.Registry → Configuration → List Owner → List Owner → Prop where
  | stable (event : StableEvent before.execution.configuration after discharged) :
      CheckedEvent declarations policy registry result outgoing bound before registry after [] discharged
  | entry (event : EntryAnnotations.EntryTyping (signature declarations) registry.joint.effects
      (resourceWorld before.execution.issued) result outgoing before.execution.configuration after created) :
      CheckedEvent declarations policy registry result outgoing bound before registry after created []
  | capture (event : CaptureRecords.CheckedCapture declarations policy registry
      (resourceWorld before.execution.issued) result outgoing bound before.execution.configuration after owner record) :
      CheckedEvent declarations policy registry result outgoing bound before (registry.insert owner record)
        after [.ticket owner] []

theorem checked_executes
    (event : CheckedEvent declarations policy registry result outgoing bound before nextRegistry after created discharged) :
    RawStep before.execution.configuration after created discharged := by
  cases event with
  | stable event => exact stable_executes event
  | entry event => exact EntryAnnotations.entry_executes event
  | capture event => exact CaptureRecords.checked_capture_executes event

theorem checked_preserves
    (event : CheckedEvent declarations policy registry result outgoing bound before nextRegistry after created discharged)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound)
    (fresh : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup) :
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after created discharged) ∧
      ClauseJoint.Valid declarations policy nextRegistry ambient
        (ScopedPortJoint.advanceState before after created discharged) result outgoing bound ∧
      ClauseJoint.RegistryExtends registry nextRegistry := by
  cases event with
  | stable event =>
      obtain ⟨step, valid⟩ := stable_preserves event valid freshHandlers
      exact ⟨step, valid, ClauseJoint.registry_extends_refl _⟩
  | entry event =>
      obtain ⟨step, valid⟩ := EntryAnnotations.entry_preserves event valid fresh freshHandlers
      exact ⟨step, valid, ClauseJoint.registry_extends_refl _⟩
  | capture event => exact CaptureRecords.checked_capture_preserves event valid fresh

inductive CheckedStep (declarations : DeclarationRegistry) (policy : Syntax.TicketPolicy)
    (result : Port) (outgoing : List Instance) (bound : List Nat) :
    ClauseJoint.Registry → NamedState → ClauseJoint.Registry → NamedState → Prop where
  | event (checked : CheckedEvent declarations policy registry result outgoing bound
      before nextRegistry after created discharged)
      (fresh : (before.execution.issued ++ created).Nodup)
      (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration after).Nodup) :
      CheckedStep declarations policy result outgoing bound registry before nextRegistry
        (ScopedPortJoint.advanceState before after created discharged)

inductive CheckedRun (declarations : DeclarationRegistry) (policy : Syntax.TicketPolicy)
    (result : Port) (outgoing : List Instance) (bound : List Nat) :
    ClauseJoint.Registry → NamedState → ClauseJoint.Registry → NamedState → Prop where
  | refl : CheckedRun declarations policy result outgoing bound registry state registry state
  | next (step : CheckedStep declarations policy result outgoing bound registry before nextRegistry middle)
      (rest : CheckedRun declarations policy result outgoing bound nextRegistry middle finalRegistry after) :
      CheckedRun declarations policy result outgoing bound registry before finalRegistry after

theorem step_preserves
    (checked : CheckedStep declarations policy result outgoing bound registry before nextRegistry after)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound) :
    NamedAccessStep ambient before after ∧
      ClauseJoint.Valid declarations policy nextRegistry ambient after result outgoing bound ∧
      ClauseJoint.RegistryExtends registry nextRegistry := by
  cases checked with
  | event checked fresh freshHandlers => exact checked_preserves checked valid fresh freshHandlers

theorem run_certified
    (run : CheckedRun declarations policy result outgoing bound registry before finalRegistry after)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound) :
    ClauseJoint.CertifiedSteps declarations policy ambient result outgoing bound registry before finalRegistry after := by
  induction run with
  | refl => exact .refl valid
  | next step rest ih =>
      obtain ⟨actual, nextValid, extended⟩ := step_preserves step valid
      exact .next valid actual extended (ih nextValid)

theorem run_preserves
    (run : CheckedRun declarations policy result outgoing bound registry before finalRegistry after)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound) :
    NamedAccessSteps ambient before after ∧
      ClauseJoint.Valid declarations policy finalRegistry ambient after result outgoing bound ∧
      ClauseJoint.RegistryExtends registry finalRegistry := by
  have certified := run_certified run valid
  exact ⟨ClauseJoint.certified_execution certified, ClauseJoint.certified_final certified,
    ClauseJoint.certified_registry_extension certified⟩

theorem run_closed_progress
    (run : CheckedRun declarations policy result [] bound registry before finalRegistry after)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result [] bound) :
    ScopedPortProgress.Terminal after.execution.configuration ∨
      ∃ next successor, NamedAccessStep ambient after successor ∧
        ClauseJoint.Valid declarations policy next ambient successor result [] bound ∧
        ClauseJoint.RegistryExtends finalRegistry next := by
  exact ClauseExecution.closed_progress (run_preserves run valid).2.1

theorem run_terminal_accounting
    (run : CheckedRun declarations policy result outgoing bound registry before finalRegistry after)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound)
    (terminal : ScopedPortProgress.Terminal after.execution.configuration) :
    after.execution.issued.Perm after.execution.completed ∧ after.execution.completed.Nodup := by
  exact ClauseExecution.terminal_accounting (run_preserves run valid).2.1 terminal

theorem run_terminal_result_support
    (run : CheckedRun declarations policy result outgoing bound registry before finalRegistry after)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound)
    (terminal : ScopedPortProgress.Terminal after.execution.configuration) :
    Syntax.resourceDependencies after.execution.configuration.expression.dependencies ⊆ bound := by
  exact ClauseExecution.terminal_result_support (run_preserves run valid).2.1 terminal

end Ash.OneShot.CheckedEvents

#print axioms Ash.OneShot.CheckedEvents.stable_executes
#print axioms Ash.OneShot.CheckedEvents.stable_boundary
#print axioms Ash.OneShot.CheckedEvents.stable_effects
#print axioms Ash.OneShot.CheckedEvents.stable_preserves
#print axioms Ash.OneShot.CheckedEvents.checked_executes
#print axioms Ash.OneShot.CheckedEvents.checked_preserves

#print axioms Ash.OneShot.CheckedEvents.step_preserves
#print axioms Ash.OneShot.CheckedEvents.run_certified
#print axioms Ash.OneShot.CheckedEvents.run_preserves
#print axioms Ash.OneShot.CheckedEvents.run_closed_progress
#print axioms Ash.OneShot.CheckedEvents.run_terminal_accounting
#print axioms Ash.OneShot.CheckedEvents.run_terminal_result_support
