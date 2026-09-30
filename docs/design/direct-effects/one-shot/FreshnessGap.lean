import PreparedExecution

/-!
A repeated-call counterexample for the uninstantiated administrative syntax.
Typing, usage, and retained disposal readiness do not freshen resource sites.
This isolates a missing source-to-runtime step; it does not relax lifetime
freshness or classify a failed freshness check as a permitted terminal result.
-/

namespace Ash.OneShot.FreshnessGap
open Syntax Execution Typing Joint Admission Progress PreparedExecution

def signature : Signature := fun _ _ => none
def policy : TicketPolicy := fun _ => ⟨true, false⟩
def acquisition : Expr := .resource 4 (.integer 0) .unit
def function : Expr := .lambda 2 acquisition
def functionType : Ty := .function .unit .unit [] []
def calls : Expr := .bind 1 (.app (.variable 0) .unit) (.app (.variable 0) .unit)
def program : Expr := .bind 0 function calls
def call : Expr := .app function .unit
def suffix : PlainData := ⟨.bind 1 call, .none, .unit, .unit, [], rfl⟩
def initial : NamedState := ⟨⟨⟨program, .none, .nil⟩, [], []⟩, []⟩
def blocked : NamedState := ⟨⟨⟨acquisition, .none, .nil⟩, [.resource 4], [.resource 4]⟩, []⟩

theorem acquisition_typed : Typed signature environment ticket allowed acquisition .unit :=
  .resource (residual := []) .integer .unit (by simp [Ty.resources]) (by simp) (List.nil_subset _)

theorem function_typed : Typed signature TypeEnv.empty .none [] function functionType := by
  apply Typed.lambda acquisition_typed
  simp [retainedSupport, acquisition, Expr.dependencies, without]

theorem program_typed : Typed signature TypeEnv.empty .none [] program .unit := by
  apply Typed.bind function_typed
  apply Typed.bind (input := .unit)
  · exact .app (input := .unit) (latent := []) (retained := [])
      (.variable (by simp [TypeEnv.extend, functionType])) .unit (List.nil_subset _)
  · exact .app (input := .unit) (latent := []) (retained := [])
      (.variable (by simp [TypeEnv.extend, functionType])) .unit (List.nil_subset _)

theorem initial_ready : Ready signature policy (fun _ => none) [] initial .unit [] := by
  apply ready_initial_configuration program_typed
  · exact .bind (.lambda (.resource .integer .unit))
      (.bind (.app .variable .unit) (.app .variable .unit))
  · simp [program, function, acquisition, calls, Expr.dependencies, resourceDependencies, without]

theorem blocked_ready : Ready signature policy (fun _ => none) [] blocked .unit [] := by
  have empty : Ready signature policy (fun _ => none) []
      ⟨⟨⟨acquisition, .none, .nil⟩, [], []⟩, []⟩ .unit [] :=
    ready_initial_configuration acquisition_typed (.resource .integer .unit)
      (by simp [acquisition, Expr.dependencies, resourceDependencies, without])
  refine ⟨⟨⟨.refl _, by decide⟩, ?_, empty.joint.support, empty.joint.effects, empty.joint.usage, ?_⟩, .nil⟩
  · constructor
    · intro owner
      simp [blocked, Stack.erase, Control.ticketNames]
    · intro activation
      simp [blocked, Stack.erase, Control.activations]
    · decide
  · intro owner
    simp [blocked]

theorem function_closed : ClosedValue function := by
  simp [ClosedValue, function, acquisition, Expr.IsValue, Expr.dependencies, without]

/-- The same lambda body reaches resource entry twice. The first acquisition
    has already discharged its owner before the second entry is attempted. -/
theorem repeated_call_prefix :
    RawTrace initial.execution.configuration blocked.execution.configuration [.resource 4] [.resource 4] := by
  have e0 := RawStep.bind 0 function calls .none Stack.nil function_closed
    (by simp [ClosedExcept, calls, Expr.dependencies, without])
    (by simp [ResourceFresh, function, acquisition, Expr.dependencies, without])
  have e1 := RawStep.focus suffix (Focus.bind (initializer := call) (by simp [call, Expr.IsValue])) Stack.nil
  have e2 := RawStep.beta 2 acquisition .unit .none (.push (.plain suffix) .nil) Execution.Examples.closed_unit
    function_closed (by simp [ResourceFresh, Expr.dependencies])
  have e3 := RawStep.enterCell 4 0 .unit .none .unit (.push (.plain suffix) .nil)
  have e4 := RawStep.leaveCell 4 0 .unit .none .none .unit Execution.Examples.closed_unit (.push (.plain suffix) .nil)
  have e5 := RawStep.plug suffix .unit Execution.Examples.closed_unit .none Stack.nil
  have e6 := RawStep.bind 1 .unit call .none Stack.nil Execution.Examples.closed_unit
    (by simp [ClosedExcept, call, function, acquisition, Expr.dependencies, without])
    (by simp [ResourceFresh, Expr.dependencies])
  have e7 := RawStep.beta 2 acquisition .unit .none Stack.nil Execution.Examples.closed_unit
    function_closed (by simp [ResourceFresh, Expr.dependencies])
  exact .next e0 (.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.next e7 (.refl _))))))))

theorem repeated_call_execution : RunSteps initial.execution blocked.execution :=
  raw_trace_enacts repeated_call_prefix (issued := []) (completed := []) (by decide)

theorem integer_resource_cannot_focus
    (focus : Focus (.resource identity (.integer payload) body) child context) : False := by
  cases focus with
  | resource notValue => exact notValue (by trivial)

theorem resource_entry_creates_its_owner
    (step : RawStep ⟨.resource identity (.integer payload) body, scope, tail⟩ after created discharged) :
    created = [.resource identity] := by
  cases step with
  | focus plain focus tail => exact False.elim (integer_resource_cannot_focus focus)
  | plug plain value closed scope tail => exact False.elim closed.1
  | leaveHandler handler value closed scope tail => exact False.elim closed.1
  | leaveCell identity payload answer savedScope scope value closed tail => exact False.elim closed.1
  | startCleanup action saved closed scope tail => exact False.elim closed.1
  | leaveClause owner answer value closed scope caller tail => exact False.elim closed.1
  | enterCell => rfl

/-- The only possible allocating rule repeats resource identity 4. Historical
    freshness rejects it; the value initializer cannot take a focus step. -/
theorem blocked_has_no_named_step : ¬ ∃ after, NamedStep blocked after := by
  intro ⟨after, step⟩
  cases step with
  | event after created discharged raw freshOwners freshHandlers =>
      change RawStep ⟨.resource 4 (.integer 0) .unit, .none, .nil⟩ after created discharged at raw
      have allocated := resource_entry_creates_its_owner raw
      rw [allocated] at freshOwners
      simp [blocked] at freshOwners

theorem blocked_is_not_value : ¬ blocked.execution.configuration.expression.IsValue := by
  simp [blocked, acquisition, Expr.IsValue]

theorem uninstantiated_checks_do_not_establish_progress :
    Ready signature policy (fun _ => none) [] initial .unit [] ∧
    RunSteps initial.execution blocked.execution ∧
    Ready signature policy (fun _ => none) [] blocked .unit [] ∧
    ¬ blocked.execution.configuration.expression.IsValue ∧
    ¬ ∃ after, NamedStep blocked after :=
  ⟨initial_ready, repeated_call_execution, blocked_ready, blocked_is_not_value, blocked_has_no_named_step⟩

end Ash.OneShot.FreshnessGap

#print axioms Ash.OneShot.FreshnessGap.initial_ready
#print axioms Ash.OneShot.FreshnessGap.repeated_call_execution
#print axioms Ash.OneShot.FreshnessGap.blocked_has_no_named_step
#print axioms Ash.OneShot.FreshnessGap.uninstantiated_checks_do_not_establish_progress
