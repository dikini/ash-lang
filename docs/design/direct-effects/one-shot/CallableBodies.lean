import CheckedProgress

/-!
Structural latent-body contracts on the existing lambda syntax. Captured storage,
argument storage and body results have separate checks. The beta bridge joins
an actual value application to ClauseJoint.Valid; global application admission
and higher-order behavior transport remain integration obligations.
-/

namespace Ash.OneShot.CallableBodies
open Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ResultSummaries (extendAnalysis)
open GenerativeResults (summary summary_support)
open DeclarationResults (signature)
open ScopedTyping (resourceWorld)
open ReturnSupport (Below)

inductive BodyChecked (declarations : DeclarationRegistry) (environment : ResultSummaries.Environment)
    (world : List Nat) : Code → List Nat → List Nat → Prop where
  | lambda (bodyChecked : ClauseResults.Derives declarations
      (extendAnalysis environment parameter (summary input)) world .none body output) :
      BodyChecked declarations environment world (.lambda parameter body) input output

structure StoredFunction (declarations : DeclarationRegistry) (environment : ResultSummaries.Environment)
    (world : List Nat) (ticket : ClauseResults.TicketBound) (function : Code)
    (captures input output : List Nat) : Prop where
  storage : ClauseResults.Derives declarations environment world ticket function captures
  body : BodyChecked declarations environment world function input output

theorem body_world_mono
    (checked : BodyChecked declarations environment world function input output) (larger : world ⊆ nextWorld) :
    BodyChecked declarations environment nextWorld function input output := by
  cases checked with
  | lambda body => exact .lambda (ClauseResults.world_mono body larger)

theorem body_substitution
    (checked : BodyChecked declarations environment world function input output)
    (closed : ClosedValue value)
    (bounded : Below (OperationResults.analyze (signature declarations) environment value) (environment name)) :
    BodyChecked declarations environment world (function.subst name value) input output := by
  cases checked with
  | @lambda parameter input body output checked =>
      change BodyChecked _ _ _ (.lambda parameter (if name = parameter then body else body.subst name value)) _ _
      by_cases same : name = parameter
      · rw [if_pos same]; exact .lambda checked
      · rw [if_neg same]
        exact .lambda (ClauseResults.substitution checked closed
          (ClauseResults.replacement_under_binding closed bounded same))

theorem stored_world_mono
    (checked : StoredFunction declarations environment world ticket function captures input output)
    (larger : world ⊆ nextWorld) :
    StoredFunction declarations environment nextWorld ticket function captures input output :=
  ⟨ClauseResults.world_mono checked.storage larger, body_world_mono checked.body larger⟩

theorem stored_substitution
    (checked : StoredFunction declarations environment world ticket function captures input output)
    (closed : ClosedValue value)
    (bounded : Below (OperationResults.analyze (signature declarations) environment value) (environment name)) :
    StoredFunction declarations environment world ticket (function.subst name value) captures input output :=
  ⟨ClauseResults.substitution checked.storage closed bounded, body_substitution checked.body closed bounded⟩

theorem stored_support
    (checked : StoredFunction declarations environment world ticket function captures input output)
    (closed : ClosedValue function) : Syntax.resourceDependencies function.dependencies ⊆ captures :=
  ClauseResults.value_support checked.storage closed

theorem argument_rebinding
    (closed : ClosedValue argument)
    (bounded : Syntax.resourceDependencies argument.dependencies ⊆ input) :
    Below (OperationResults.analyze (signature declarations) (extendAnalysis environment parameter (summary input)) argument)
      ((extendAnalysis environment parameter (summary input)) parameter) := by
  intro resources known
  simp only [extendAnalysis, ↓reduceIte, summary_support] at known
  cases known
  exact ⟨_, OperationResults.closed_value_storage_sound closed, bounded⟩

theorem body_application
    (checked : BodyChecked declarations environment world (.lambda parameter body) input output)
    (closed : ClosedValue argument)
    (argumentChecked : ClauseResults.Derives declarations argumentEnvironment world ticket argument input) :
    ClauseResults.Derives declarations (extendAnalysis environment parameter (summary input)) world .none
      (body.subst parameter argument) output := by
  cases checked with
  | lambda checked =>
      exact ClauseResults.substitution checked closed
        (argument_rebinding closed (ClauseResults.value_support argumentChecked closed))

theorem body_application_bounded
    (checked : BodyChecked declarations environment world (.lambda parameter body) input output)
    (closed : ClosedValue argument)
    (argumentChecked : ClauseResults.Derives declarations argumentEnvironment world ticket argument actualInput)
    (included : actualInput ⊆ input) :
    ClauseResults.Derives declarations (extendAnalysis environment parameter (summary input)) world .none
      (body.subst parameter argument) output := by
  cases checked with
  | lambda checked =>
      exact ClauseResults.substitution checked closed
        (argument_rebinding closed ((ClauseResults.value_support argumentChecked closed).trans included))

theorem beta_preserves
    (valid : ScopedPortJoint.Valid (signature declarations) policy registry.joint ambient
      ⟨⟨⟨.app (.lambda parameter body) argument, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : argument.IsValue)
    (functionChecked : BodyChecked declarations environment (resourceWorld issued) (.lambda parameter body) input output)
    (argumentChecked : ClauseResults.Derives declarations argumentEnvironment (resourceWorld issued) ticket argument actualInput)
    (included : actualInput ⊆ input)
    (tailChecked : ClauseFrames.StackReturns declarations registry.results (resourceWorld issued) tail output bound) :
    let before : NamedState := ⟨⟨⟨.app (.lambda parameter body) argument, scope, tail⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨body.subst parameter argument, .none, tail⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] []) ∧
      ClauseJoint.Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [] []) result outgoing bound := by
  obtain ⟨currentPort, current, ports⟩ := effect_configuration_has_types valid.effects
  cases current with
  | checked scopeTyped typed => cases typed with
      | app functionTyped argumentTyped available =>
          have argumentClosed := typed_value_closed argumentTyped isValue
          have functionClosed := typed_value_closed functionTyped (by trivial)
          obtain ⟨step, joint⟩ := ScopedPortJoint.ordinary_step_preserves_joint_configuration
            (.beta argumentClosed functionClosed) valid
          refine ⟨step, joint, ?_⟩
          simpa [ScopedPortJoint.advanceState] using
            (show ClauseFrames.ConfigurationReturns declarations registry.results (resourceWorld issued)
              ⟨body.subst parameter argument, .none, tail⟩ bound from
              ⟨_, .none, output, .none, body_application_bounded functionChecked argumentClosed argumentChecked included, tailChecked⟩)

theorem body_cannot_inherit_resume
    (input output : List Nat) :
    ¬ BodyChecked declarations environment world (.lambda parameter (.resume binder operand)) input output := by
  intro checked
  cases checked with
  | lambda body =>
      obtain ⟨resumeInput, impossible, operandChecked⟩ := ClauseResults.resume_inversion body
      cases impossible

namespace Examples
open GenerativeResults.Examples (declarations environment policy)

def retainingFactory : Code := .lambda 0 (.lambda 1 (.bind 2 (.variable 0) (.integer 17)))
def constantFactory : Code := .lambda 0 (.lambda 1 (.integer 17))
def handle : Code := .resourceRef (.activation 7)

theorem retaining_factory_checked :
    StoredFunction declarations environment [7] .none retainingFactory [] [7] [7] := by
  constructor
  · exact .existing (.leaf (Or.inl trivial) rfl (by decide))
  · exact .lambda (.existing (.leaf (Or.inl trivial) rfl (by decide)))

theorem constant_factory_checked :
    StoredFunction declarations environment [7] .none constantFactory [] [7] [] := by
  constructor
  · exact .existing (.leaf (Or.inl trivial) rfl (by decide))
  · exact .lambda (.existing (.leaf (Or.inl trivial) rfl (by decide)))

theorem same_factory_storage :
    Syntax.resourceDependencies retainingFactory.dependencies = [] ∧
      Syntax.resourceDependencies constantFactory.dependencies = [] := by decide

theorem retaining_result_not_empty :
    ¬ BodyChecked declarations environment [7] retainingFactory [7] [] := by
  intro bad
  have argumentChecked : ClauseResults.Derives declarations environment [7] .none handle [7] :=
    .existing (.leaf (Or.inl trivial) rfl (by decide))
  have closed : ClosedValue handle := by
    simp [handle, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
      ResourceName.freeNames, Code.dependencies]
  have applied := body_application bad closed argumentChecked
  have retained := ClauseResults.value_support applied (by
    simp [Code.subst, handle, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
      ResourceName.freeNames, Code.dependencies, Syntax.without])
  have impossible := retained (by decide : 7 ∈ Syntax.resourceDependencies
    ((Code.lambda 1 (.bind 2 (.variable 0) (.integer 17))).subst 0 handle).dependencies)
  cases impossible

theorem storage_does_not_supply_body :
    ClauseResults.Derives declarations environment [7] .none retainingFactory [] ∧
      ¬ BodyChecked declarations environment [7] retainingFactory [7] [] :=
  ⟨retaining_factory_checked.storage, retaining_result_not_empty⟩

def identityCall : Code := .app (.lambda 0 (.variable 0)) (.integer 17)
def before : NamedState := ⟨⟨⟨identityCall, .none, .nil⟩, [], []⟩, []⟩
def after : NamedState := ⟨⟨⟨.integer 17, .none, .nil⟩, [], []⟩, []⟩
def registry : ClauseJoint.Registry := fun _ => none

theorem identity_call_typed :
    Typed (signature declarations) [] TypeEnv.empty .none [] identityCall .integer :=
  .app (.lambda (.variable rfl (List.nil_subset _)) (List.nil_subset _)) .integer (List.nil_subset _)

theorem identity_call_joint :
    ScopedPortJoint.Valid (signature declarations) policy registry.joint [] before .integer [] := by
  exact ScopedPortJoint.initial_configuration_valid identity_call_typed (.app (.lambda .variable) .integer) rfl

theorem identity_call_body : BodyChecked declarations environment [] (.lambda 0 (.variable 0)) [] [] :=
  .lambda (.existing (.leaf (Or.inr ⟨0, rfl⟩) rfl (by decide)))

theorem identity_call_executes : NamedAccessStep [] before after ∧
    ClauseJoint.Valid declarations policy registry [] after .integer [] [] := by
  have argumentChecked : ClauseResults.Derives declarations environment [] .none (.integer 17) [] :=
    .existing (.leaf (Or.inl trivial) rfl (by decide))
  simpa [before, after, identityCall, ScopedPortJoint.advanceState, Code.subst, enteredActivations] using
    beta_preserves identity_call_joint (by trivial) identity_call_body argumentChecked (List.Subset.refl _)
      (.nil (List.Subset.refl _))

def effectfulCall : Code := .app (.lambda 0 ClauseResults.Examples.innerHandler) .unit
def effectfulBefore : NamedState := ⟨⟨⟨effectfulCall, .none, .nil⟩, [], []⟩, []⟩

theorem effectful_call_typed :
    Typed (signature GenerativeFrames.Examples.declarations) [] TypeEnv.empty .none [] effectfulCall .integer :=
  .app (.lambda (ClauseResults.Examples.inner_handler_typed _ _ _ _) (List.nil_subset _)) .unit (List.nil_subset _)

theorem effectful_call_joint :
    ScopedPortJoint.Valid (signature GenerativeFrames.Examples.declarations) ClauseResults.Examples.policy
      ClauseJoint.Examples.emptyRegistry.joint [] effectfulBefore .integer [] :=
  ScopedPortJoint.initial_configuration_valid effectful_call_typed
    (.app (.lambda (.handle (.perform .unit) (.cons (.resume rfl .integer) .nil))) .unit) rfl

theorem effectful_call_executes : NamedAccessStep [] effectfulBefore ClauseJoint.Examples.initial ∧
    ClauseJoint.Valid GenerativeFrames.Examples.declarations ClauseResults.Examples.policy
      ClauseJoint.Examples.emptyRegistry [] ClauseJoint.Examples.initial .integer [] [] := by
  have bodyChecked : BodyChecked GenerativeFrames.Examples.declarations environment []
      (.lambda 0 ClauseResults.Examples.innerHandler) [] [] :=
    .lambda (ClauseResults.Examples.inner_handler_checked _ _ _)
  have argumentChecked : ClauseResults.Derives GenerativeFrames.Examples.declarations environment [] .none .unit [] :=
    .existing (.leaf (Or.inl trivial) rfl (by decide))
  simpa [effectfulBefore, effectfulCall, ClauseJoint.Examples.initial, ClauseResults.Examples.innerHandler,
    ClauseResults.Examples.innerClauses, ScopedPortJoint.advanceState, Code.subst, Clauses.subst, enteredActivations] using
    beta_preserves effectful_call_joint (by trivial) bodyChecked argumentChecked (List.Subset.refl _)
      (.nil (List.Subset.refl _))

theorem effectful_call_completes : ∃ record,
    NamedAccessSteps [] effectfulBefore ClauseJoint.Examples.final ∧
      ClauseJoint.Valid GenerativeFrames.Examples.declarations ClauseResults.Examples.policy
        (ClauseJoint.Examples.emptyRegistry.insert 5 record) [] ClauseJoint.Examples.final .integer [] [] := by
  obtain ⟨record, run⟩ := ClauseJoint.Examples.single_handler_execution
  exact ⟨record, .next effectful_call_executes.1 (ClauseJoint.certified_execution run), ClauseJoint.certified_final run⟩

end Examples

end Ash.OneShot.CallableBodies

#print axioms Ash.OneShot.CallableBodies.body_world_mono
#print axioms Ash.OneShot.CallableBodies.body_substitution
#print axioms Ash.OneShot.CallableBodies.stored_world_mono
#print axioms Ash.OneShot.CallableBodies.stored_substitution
#print axioms Ash.OneShot.CallableBodies.stored_support
#print axioms Ash.OneShot.CallableBodies.argument_rebinding
#print axioms Ash.OneShot.CallableBodies.body_application
#print axioms Ash.OneShot.CallableBodies.beta_preserves

#print axioms Ash.OneShot.CallableBodies.body_application_bounded
#print axioms Ash.OneShot.CallableBodies.Examples.retaining_factory_checked
#print axioms Ash.OneShot.CallableBodies.Examples.constant_factory_checked
#print axioms Ash.OneShot.CallableBodies.Examples.same_factory_storage
#print axioms Ash.OneShot.CallableBodies.Examples.retaining_result_not_empty
#print axioms Ash.OneShot.CallableBodies.Examples.storage_does_not_supply_body
#print axioms Ash.OneShot.CallableBodies.Examples.identity_call_typed
#print axioms Ash.OneShot.CallableBodies.Examples.identity_call_joint
#print axioms Ash.OneShot.CallableBodies.Examples.identity_call_body
#print axioms Ash.OneShot.CallableBodies.Examples.identity_call_executes

#print axioms Ash.OneShot.CallableBodies.body_cannot_inherit_resume

#print axioms Ash.OneShot.CallableBodies.Examples.effectful_call_typed
#print axioms Ash.OneShot.CallableBodies.Examples.effectful_call_joint
#print axioms Ash.OneShot.CallableBodies.Examples.effectful_call_executes
#print axioms Ash.OneShot.CallableBodies.Examples.effectful_call_completes
