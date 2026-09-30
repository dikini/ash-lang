import ScopedPortPrepared

/-!
Symbolic value/result metadata on the existing Code grammar. Callable capture
support is distinct from its body-result summary. De Bruijn parameters scope
only the result body of a callable; its captured value is in the outer scope.
This is a first analysis component, not source admission or a theorem that all
analyzed computations return values realizing their summaries.
-/

namespace Ash.OneShot.ResultSummaries
open Syntax Instantiation ScopedExpressions ScopedExecution

inductive Summary where
  | scalar
  | resource : Nat → Summary
  | parameter : Nat → Summary
  | product : Summary → Summary → Summary
  | callable : Summary → Summary → Summary
  | application : Summary → Summary → Summary
  | join : Summary → Summary → Summary
  | unknown
  deriving DecidableEq, Repr

def liftRename (rename : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rename n + 1

def Summary.rename (rename : Nat → Nat) : Summary → Summary
  | .scalar => .scalar
  | .resource identity => .resource identity
  | .parameter index => .parameter (rename index)
  | .product left right => .product (left.rename rename) (right.rename rename)
  | .callable captures result => .callable (captures.rename rename) (result.rename (liftRename rename))
  | .application function argument => .application (function.rename rename) (argument.rename rename)
  | .join left right => .join (left.rename rename) (right.rename rename)
  | .unknown => .unknown

def liftSubstitution (substitute : Nat → Summary) : Nat → Summary
  | 0 => .parameter 0
  | n + 1 => (substitute n).rename Nat.succ

def Summary.substitute (substitute : Nat → Summary) : Summary → Summary
  | .scalar => .scalar
  | .resource identity => .resource identity
  | .parameter index => substitute index
  | .product left right => .product (left.substitute substitute) (right.substitute substitute)
  | .callable captures result => .callable (captures.substitute substitute) (result.substitute (liftSubstitution substitute))
  | .application function argument => .application (function.substitute substitute) (argument.substitute substitute)
  | .join left right => .join (left.substitute substitute) (right.substitute substitute)
  | .unknown => .unknown

def Summary.instantiate (body argument : Summary) : Summary :=
  body.substitute fun index => match index with
    | 0 => argument
    | n + 1 => .parameter n

/-- One known-call unfolding; unresolved applications retain both operands. -/
def callResult (function argument : Summary) : Summary := match function with
  | .callable _ body => body.instantiate argument
  | _ => .application function argument

/-- None denotes unresolved support, not the empty resource set. Callable
    storage uses its captures; its eventual result has a separate summary. -/
def Summary.support : Summary → Option (List Nat)
  | .scalar => some []
  | .resource identity => some [identity]
  | .parameter _ | .application _ _ | .unknown => none
  | .product left right | .join left right => do
      let first ← left.support
      let second ← right.support
      pure (first ++ second)
  | .callable captures _ => captures.support

def Summary.Scoped (depth : Nat) : Summary → Prop
  | .scalar | .resource _ | .unknown => True
  | .parameter index => index < depth
  | .product left right | .application left right | .join left right => left.Scoped depth ∧ right.Scoped depth
  | .callable captures result => captures.Scoped depth ∧ result.Scoped (depth + 1)

@[simp] theorem lift_rename_identity : liftRename id = id := by
  funext index
  cases index <;> rfl

@[simp] theorem rename_identity (summary : Summary) : summary.rename id = summary := by
  induction summary <;> simp_all [Summary.rename]

theorem rename_preserves_scope {summary : Summary} (wellScoped : summary.Scoped depth)
    (mapped : ∀ index, index < depth → rename index < next) :
    (summary.rename rename).Scoped next := by
  induction summary generalizing depth next rename with
  | scalar | resource | unknown => trivial
  | parameter index => exact mapped index wellScoped
  | product left right ihLeft ihRight | application left right ihLeft ihRight | join left right ihLeft ihRight =>
      exact ⟨ihLeft wellScoped.1 mapped, ihRight wellScoped.2 mapped⟩
  | callable captures result ihCaptures ihResult =>
      refine ⟨ihCaptures wellScoped.1 mapped, ihResult wellScoped.2 ?_⟩
      intro index below
      cases index with
      | zero => exact Nat.zero_lt_succ _
      | succ index => exact Nat.succ_lt_succ (mapped index (Nat.lt_of_succ_lt_succ below))

theorem substitute_preserves_scope {summary : Summary} (wellScoped : summary.Scoped depth)
    (mapped : ∀ index, index < depth → (substitute index).Scoped next) :
    (summary.substitute substitute).Scoped next := by
  induction summary generalizing depth next substitute with
  | scalar | resource | unknown => trivial
  | parameter index => exact mapped index wellScoped
  | product left right ihLeft ihRight | application left right ihLeft ihRight | join left right ihLeft ihRight =>
      exact ⟨ihLeft wellScoped.1 mapped, ihRight wellScoped.2 mapped⟩
  | callable captures result ihCaptures ihResult =>
      refine ⟨ihCaptures wellScoped.1 mapped, ihResult wellScoped.2 ?_⟩
      intro index below
      cases index with
      | zero => exact Nat.zero_lt_succ _
      | succ index =>
          exact rename_preserves_scope (mapped index (Nat.lt_of_succ_lt_succ below))
            (fun _ member => Nat.succ_lt_succ member)

theorem instantiate_preserves_scope {summary argument : Summary} (body : summary.Scoped (depth + 1)) (value : argument.Scoped depth) :
    (summary.instantiate argument).Scoped depth := by
  apply substitute_preserves_scope body
  intro index below
  cases index with
  | zero => exact value
  | succ index => exact Nat.lt_of_succ_lt_succ below

@[simp] theorem support_renaming (summary : Summary) (rename : Nat → Nat) :
    (summary.rename rename).support = summary.support := by
  induction summary generalizing rename <;> simp_all [Summary.rename, Summary.support]

@[simp] theorem scalar_result_ignores_argument : callResult (.callable captures .scalar) argument = .scalar := rfl
@[simp] theorem parameter_result_returns_argument : callResult (.callable captures (.parameter 0)) argument = argument := rfl

/-- The inner formal parameter remains bound. The outer argument is lifted
    only inside the inner body; the inner captures retain its full structure. -/
theorem returned_callable_instantiation :
    callResult (.callable captures (.callable (.parameter 0) (.application (.parameter 1) (.parameter 0)))) argument =
      .callable argument (.application (argument.rename Nat.succ) (.parameter 0)) := rfl

theorem returned_callable_retains_argument_support :
    (callResult (.callable captures (.callable (.parameter 0) body)) argument).support = argument.support := rfl

theorem unresolved_support_is_not_empty : Summary.unknown.support ≠ some [] ∧
    (Summary.parameter index).support ≠ some [] ∧ (Summary.application function argument).support ≠ some [] := by
  simp [Summary.support]

abbrev Environment := Nat → Summary

def captured (environment : Environment) : List Dependency → Summary
  | [] => .scalar
  | dependency :: rest =>
      .join (match dependency with
        | .resource identity => .resource identity
        | .variable name => environment name
        | .ticket _ => .unknown) (captured environment rest)

/-- Structural result metadata. Control-sensitive forms are explicitly unknown
    until the handler/resource/continuation summary rules are established. -/
def analyze (environment : Environment) : Code → Summary
  | .unit | .boolean _ | .integer _ => .scalar
  | .variable name => environment name
  | .resourceRef (.activation identity) => .resource identity
  | .resourceRef (.bound _) => .unknown
  | .pair left right => .product (analyze environment left) (analyze environment right)
  | .lambda parameter body =>
      .callable (captured environment (Code.lambda parameter body).dependencies)
        (analyze (fun name => if name = parameter then .parameter 0 else (environment name).rename Nat.succ) body)
  | .app function argument => .application (analyze environment function) (analyze environment argument)
  | .bind parameter initializer body =>
      analyze (fun name => if name = parameter then analyze environment initializer else environment name) body
  | .branch _ yes no => .join (analyze environment yes) (analyze environment no)
  | .perform _ _ _ | .handle _ _ _ | .resume _ _ | .discard _ | .resource _ _ _ | .cleanup _ _ => .unknown

theorem captured_preserves_scope
    (environmentScoped : ∀ name, (environment name).Scoped depth) :
    (captured environment dependencies).Scoped depth := by
  induction dependencies with
  | nil => trivial
  | cons dependency rest ih =>
      refine ⟨?_, ih⟩
      cases dependency with
      | resource | ticket => trivial
      | «variable» name => exact environmentScoped name

/-- Well-scoping of computed metadata is distinct from execution soundness. -/
theorem analyze_preserves_scope {code : Code}
    (environmentScoped : ∀ name, (environment name).Scoped depth) :
    (analyze environment code).Scoped depth := by
  cases code with
  | unit | boolean | integer | perform | handle | resume | discard | resource | cleanup => trivial
  | «variable» name => exact environmentScoped name
  | resourceRef name => cases name <;> trivial
  | pair left right | app left right =>
      exact ⟨analyze_preserves_scope environmentScoped, analyze_preserves_scope environmentScoped⟩
  | branch condition yes no =>
      exact ⟨analyze_preserves_scope environmentScoped, analyze_preserves_scope environmentScoped⟩
  | bind parameter initializer body =>
      apply analyze_preserves_scope (code := body)
        (environment := fun name => if name = parameter then analyze environment initializer else environment name)
      intro name
      split
      · exact analyze_preserves_scope environmentScoped
      · exact environmentScoped name
  | lambda parameter body =>
      refine ⟨captured_preserves_scope environmentScoped, analyze_preserves_scope ?_⟩
      intro name
      split
      · exact Nat.zero_lt_succ _
      · exact rename_preserves_scope (environmentScoped name) (fun _ member => Nat.succ_lt_succ member)
termination_by sizeOf code

theorem captured_support_when_closed
    (closed : ∀ dependency ∈ dependencies, match dependency with | .resource _ => True | _ => False) :
    (captured environment dependencies).support = some (resourceDependencies dependencies) := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      have first := closed dependency List.mem_cons_self
      have tail := ih (fun dep member => closed dep (List.mem_cons_of_mem _ member))
      cases dependency with
      | resource identity => simp [captured, Summary.support, resourceDependencies, tail]
      | «variable» | ticket => cases first

/-- This theorem concerns storage of actual closed values. It does not prove
    soundness of the inferred body-result summaries for general computations. -/
theorem closed_value_storage_sound {value : Code} (closed : ClosedValue value) :
    (analyze environment value).support = some (resourceDependencies value.dependencies) := by
  cases value with
  | unit | boolean | integer => rfl
  | resourceRef name => cases name with
      | bound name => cases closed.2.1
      | activation identity => rfl
  | pair left right =>
      have leftClosed : ClosedValue left := ⟨closed.1.1, by simpa [Code.ResourceClosed, Code.freeNames] using (List.append_eq_nil_iff.mp closed.2.1).1,
        fun dep member => closed.2.2 dep (List.mem_append_left _ member)⟩
      have rightClosed : ClosedValue right := ⟨closed.1.2, (List.append_eq_nil_iff.mp closed.2.1).2,
        fun dep member => closed.2.2 dep (List.mem_append_right _ member)⟩
      simp [analyze, Summary.support, Code.dependencies, resourceDependencies, closed_value_storage_sound leftClosed, closed_value_storage_sound rightClosed]
  | lambda parameter body => exact captured_support_when_closed closed.2.2
  | «variable» | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases closed.1

termination_by sizeOf value

namespace Examples

def retainingConstant (identity : Nat) : Code :=
  .lambda 0 (.bind 1 (.resourceRef (.activation identity)) (.integer 42))

theorem constant_capture_and_result_differ :
    (analyze (fun _ => .unknown) (retainingConstant identity)).support = some [identity] ∧
    (callResult (analyze (fun _ => .unknown) (retainingConstant identity)) argument).support = some [] := by
  simp [retainingConstant, analyze, Code.dependencies, without, captured, Summary.support, callResult, Summary.instantiate,
    Summary.substitute]

theorem factory_keeps_callable_structure :
    callResult (.callable .scalar (.callable (.parameter 0) (.application (.parameter 1) (.parameter 0))))
      (.callable (.resource identity) .scalar) =
      .callable (.callable (.resource identity) .scalar)
        (.application (.callable (.resource identity) .scalar) (.parameter 0)) := rfl

/-- The constant-result metadata agrees with an actual beta followed by bind
    reduction. These are raw steps, not a general source-admission theorem. -/
theorem retaining_constant_beta_bind :
    RawStep ⟨.app (retainingConstant identity) .unit, scope, tail⟩
      ⟨.bind 1 (.resourceRef (.activation identity)) (.integer 42), .none, tail⟩ [] [] ∧
    RawStep ⟨.bind 1 (.resourceRef (.activation identity)) (.integer 42), .none, tail⟩
      ⟨.integer 42, .none, tail⟩ [] [] := by
  have closed : ClosedValue (retainingConstant identity) := by
    simp [ScopedExpressions.ClosedValue, retainingConstant, Code.IsValue, Code.ResourceClosed, Code.freeNames,
      ResourceName.freeNames, Code.dependencies, without]
  have reference : ClosedValue (.resourceRef (.activation identity)) := by
    simp [ScopedExpressions.ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, ResourceName.freeNames, Code.dependencies]
  exact ⟨.beta 0 _ .unit scope tail ScopedExecution.Examples.unit_closed closed,
    .bind 1 _ _ .none tail reference (by simp [ScopedExpressions.ClosedExcept, Code.dependencies])⟩

/-- Actual substitution flattens the stored dependencies of an inserted
    closure. Symbolic parameter substitution retains its value structure. -/
theorem factory_beta_summary_is_not_syntactic_equality :
    callResult (analyze (fun _ => .unknown) (.lambda 3 (.lambda 2 (.variable 3))))
      (analyze (fun _ => .unknown) (retainingConstant 7)) ≠
    analyze (fun _ => .unknown) ((Code.lambda 2 (.variable 3)).subst 3 (retainingConstant 7)) := by
  decide

theorem factory_beta_summaries_agree_on_storage :
    (callResult (analyze (fun _ => .unknown) (.lambda 3 (.lambda 2 (.variable 3))))
      (analyze (fun _ => .unknown) (retainingConstant 7))).support = some [7] ∧
    (analyze (fun _ => .unknown) ((Code.lambda 2 (.variable 3)).subst 3 (retainingConstant 7))).support = some [7] := by
  decide

/-- Current unresolved support equality is not a substitution congruence. -/
theorem current_support_equality_is_not_stable :
    (Summary.parameter 0).support = (Summary.parameter 1).support ∧
    ((Summary.parameter 0).substitute (fun index => .resource index)).support ≠
      ((Summary.parameter 1).substitute (fun index => .resource index)).support := by
  decide

end Examples
end Ash.OneShot.ResultSummaries

#print axioms Ash.OneShot.ResultSummaries.lift_rename_identity
#print axioms Ash.OneShot.ResultSummaries.rename_identity
#print axioms Ash.OneShot.ResultSummaries.rename_preserves_scope
#print axioms Ash.OneShot.ResultSummaries.substitute_preserves_scope
#print axioms Ash.OneShot.ResultSummaries.instantiate_preserves_scope
#print axioms Ash.OneShot.ResultSummaries.support_renaming
#print axioms Ash.OneShot.ResultSummaries.scalar_result_ignores_argument
#print axioms Ash.OneShot.ResultSummaries.parameter_result_returns_argument
#print axioms Ash.OneShot.ResultSummaries.returned_callable_instantiation
#print axioms Ash.OneShot.ResultSummaries.returned_callable_retains_argument_support
#print axioms Ash.OneShot.ResultSummaries.unresolved_support_is_not_empty
#print axioms Ash.OneShot.ResultSummaries.captured_preserves_scope
#print axioms Ash.OneShot.ResultSummaries.analyze_preserves_scope
#print axioms Ash.OneShot.ResultSummaries.captured_support_when_closed
#print axioms Ash.OneShot.ResultSummaries.closed_value_storage_sound
#print axioms Ash.OneShot.ResultSummaries.Examples.constant_capture_and_result_differ
#print axioms Ash.OneShot.ResultSummaries.Examples.factory_keeps_callable_structure
#print axioms Ash.OneShot.ResultSummaries.Examples.retaining_constant_beta_bind
#print axioms Ash.OneShot.ResultSummaries.Examples.factory_beta_summary_is_not_syntactic_equality
#print axioms Ash.OneShot.ResultSummaries.Examples.factory_beta_summaries_agree_on_storage
#print axioms Ash.OneShot.ResultSummaries.Examples.current_support_equality_is_not_stable
