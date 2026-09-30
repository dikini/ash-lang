import ResultTransport

/-!
Concrete closed-value substitution and result-summary correspondence on the
existing Code grammar. This connects metadata transport to actual bind/beta
reducts, but does not prove general computation-result soundness.
-/

namespace Ash.OneShot.ResultSummaries
open Syntax ScopedExpressions

def expandDependencies (name : Nat) (replacement : List Dependency) (dependencies : List Dependency) : List Dependency :=
  dependencies.flatMap fun dependency => if dependency = .variable name then replacement else [dependency]

theorem expand_append (left right : List Dependency) :
    expandDependencies name replacement (left ++ right) =
      expandDependencies name replacement left ++ expandDependencies name replacement right := by
  simp [expandDependencies]

theorem expand_without_same (dependencies : List Dependency) :
    expandDependencies name replacement (without (.variable name) dependencies) = without (.variable name) dependencies := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      by_cases same : dependency = .variable name
      · simp [without, same, expandDependencies] at ih ⊢; exact ih
      · simp [without, same, expandDependencies] at ih ⊢; exact ih

theorem expand_without (dependencies : List Dependency) (different : binder ≠ Dependency.variable name)
    (absent : binder ∉ replacement) :
    expandDependencies name replacement (without binder dependencies) =
      without binder (expandDependencies name replacement dependencies) := by
  have unchanged : without binder replacement = replacement := by
    apply List.filter_eq_self.mpr
    intro dependency member
    have distinct : dependency ≠ binder := by intro equal; subst dependency; exact absent member
    simpa using distinct
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      by_cases bound : dependency = binder
      · subst dependency
        simp [without, different, expandDependencies] at ih ⊢
        exact ih
      · by_cases replaced : dependency = .variable name
        · subst dependency
          simp only [expandDependencies, List.flatMap_cons, without, List.filter_cons,
            bne_iff_ne.mpr bound, ↓reduceIte, List.filter_append] at ih ⊢
          change replacement ++ _ = without binder replacement ++ _
          rw [unchanged]
          exact congrArg (replacement ++ ·) ih
        · simp [without, bound, replaced, expandDependencies] at ih ⊢
          exact ih

theorem expand_resource_atoms (identities : List Nat) :
    expandDependencies name replacement (identities.map Dependency.resource) = identities.map Dependency.resource := by
  induction identities with
  | nil => rfl
  | cons identity rest ih => simp [expandDependencies] at ih ⊢; exact ih

mutual
theorem code_substitution_dependencies (code : Code) (name : Nat)
    (closed : ScopedExpressions.ClosedValue value) :
    (code.subst name value).dependencies = expandDependencies name value.dependencies code.dependencies := by
  have variableAbsent : ∀ binder, Dependency.variable binder ∉ value.dependencies :=
    fun binder member => closed.2.2 (.variable binder) member
  cases code with
  | unit | boolean | integer => rfl
  | resourceRef reference => cases reference <;> simp [Code.subst, Code.dependencies, expandDependencies]
  | «variable» other =>
      by_cases same : name = other
      · simp [Code.subst, Code.dependencies, expandDependencies, same]
      · simp [Code.subst, Code.dependencies, expandDependencies, same, Ne.symm same]
  | pair left right | app left right | cleanup left right | resource _ left right =>
      simp only [Code.subst, Code.dependencies, expand_append, code_substitution_dependencies left name closed,
        code_substitution_dependencies right name closed]
  | lambda parameter body =>
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte, Code.dependencies, expand_without_same]
      · simp only [Code.subst, if_neg same, Code.dependencies, code_substitution_dependencies body name closed]
        exact (expand_without body.dependencies (by simpa using Ne.symm same) (variableAbsent parameter)).symm
  | bind parameter initializer body =>
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte, Code.dependencies, expand_append, expand_without_same,
          code_substitution_dependencies initializer name closed]
      · simp only [Code.subst, if_neg same, Code.dependencies, expand_append,
          code_substitution_dependencies initializer name closed, code_substitution_dependencies body name closed]
        rw [expand_without body.dependencies (by simpa using Ne.symm same) (variableAbsent parameter)]
  | branch condition yes no =>
      simp only [Code.subst, Code.dependencies, expand_append, code_substitution_dependencies condition name closed,
        code_substitution_dependencies yes name closed, code_substitution_dependencies no name closed]
  | perform effect operation operand =>
      simp only [Code.subst, Code.dependencies, expand_append, expand_resource_atoms,
        code_substitution_dependencies operand name closed]
  | handle effect body clauses =>
      simp only [Code.subst, Code.dependencies, expand_append, expand_resource_atoms,
        code_substitution_dependencies body name closed, clauses_substitution_dependencies clauses name closed]
  | resume ticket operand =>
      simpa [Code.subst, Code.dependencies, expandDependencies] using code_substitution_dependencies operand name closed
  | discard ticket => simp [Code.subst, Code.dependencies, expandDependencies]
termination_by sizeOf code

theorem clauses_substitution_dependencies (clauses : ScopedExpressions.Clauses) (name : Nat)
    (closed : ScopedExpressions.ClosedValue value) :
    (clauses.subst name value).dependencies = expandDependencies name value.dependencies clauses.dependencies := by
  have variableAbsent : ∀ binder, Dependency.variable binder ∉ value.dependencies :=
    fun binder member => closed.2.2 (.variable binder) member
  have ticketAbsent : ∀ binder, Dependency.ticket binder ∉ value.dependencies :=
    fun binder member => closed.2.2 (.ticket binder) member
  cases clauses with
  | nil => rfl
  | cons operation parameter ticket body rest =>
      by_cases same : name = parameter
      · subst parameter
        simp only [ScopedExpressions.Clauses.subst, ↓reduceIte, ScopedExpressions.Clauses.dependencies, expand_append,
          clauses_substitution_dependencies rest name closed]
        rw [expand_without _ (by simp) (ticketAbsent ticket), expand_without_same]
      · simp only [ScopedExpressions.Clauses.subst, if_neg same, ScopedExpressions.Clauses.dependencies, expand_append,
          code_substitution_dependencies body name closed, clauses_substitution_dependencies rest name closed]
        rw [expand_without _ (by simp) (ticketAbsent ticket),
          expand_without _ (by simpa using Ne.symm same) (variableAbsent parameter)]
termination_by sizeOf clauses
end

def extendAnalysis (environment : Environment) (name : Nat) (value : Summary) : Environment :=
  fun other => if other = name then value else environment other

theorem captured_append_support (left right : List Dependency) :
    (captured environment (left ++ right)).support =
      (Summary.join (captured environment left) (captured environment right)).support := by
  induction left with
  | nil => simp [captured, Summary.support]
  | cons dependency rest ih =>
      simp only [List.cons_append, captured, Summary.support, ih]
      cases head : (match dependency with
        | .resource identity => Summary.resource identity
        | .variable name => environment name
        | .ticket _ => Summary.unknown).support <;>
        cases tail : (captured environment rest).support <;>
        cases suffix : (captured environment right).support <;>
        simp [List.append_assoc]

theorem expanded_capture_correspondence (dependencies : List Dependency) (name : Nat)
    (closed : ScopedExpressions.ClosedValue value) :
    StorageEq (captured environment (expandDependencies name value.dependencies dependencies))
      (captured (extendAnalysis environment name (analyze environment value)) dependencies) := by
  intro substitute
  simp only [captured_substitute]
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      by_cases same : dependency = .variable name
      · subst dependency
        simp only [expandDependencies, List.flatMap_cons, ↓reduceIte] at ih ⊢
        rw [captured_append_support]
        simp only [captured, Summary.support, extendAnalysis, ↓reduceIte,
          captured_support_when_closed closed.2.2, closed_value_analysis_substitute closed,
          closed_value_storage_sound closed, ih]
      · cases dependency <;> simp_all [expandDependencies, captured, Summary.support, extendAnalysis]

theorem code_capture_substitution (code : Code) (name : Nat)
    (closed : ScopedExpressions.ClosedValue value) :
    StorageEq (captured environment (code.subst name value).dependencies)
      (captured (extendAnalysis environment name (analyze environment value)) code.dependencies) := by
  rw [code_substitution_dependencies code name closed]
  exact expanded_capture_correspondence _ name closed

/-- Concrete source substitution agrees with analysis in the extended
    environment modulo result structure and substitution-stable storage. -/
theorem analyze_code_substitution (code : Code) (name : Nat)
    (closed : ScopedExpressions.ClosedValue value) :
    ResultEq (analyze environment (code.subst name value))
      (analyze (extendAnalysis environment name (analyze environment value)) code) := by
  cases code with
  | unit | boolean | integer => exact .scalar
  | resourceRef reference => cases reference with
      | bound => exact .unknown
      | activation => exact .resource
  | perform | handle | resume | discard | resource | cleanup => exact .unknown
  | «variable» other =>
      by_cases same : name = other
      · subst other
        simp only [Code.subst, ↓reduceIte, analyze, extendAnalysis]
        exact ResultEq.refl _
      · simp only [Code.subst, if_neg same, analyze, extendAnalysis, if_neg (Ne.symm same)]
        exact ResultEq.refl _
  | pair left right => exact .product (analyze_code_substitution left name closed) (analyze_code_substitution right name closed)
  | app function argument => exact .application (analyze_code_substitution function name closed) (analyze_code_substitution argument name closed)
  | branch condition yes no => exact .join (analyze_code_substitution yes name closed) (analyze_code_substitution no name closed)
  | lambda parameter body =>
      have captures := code_capture_substitution (environment := environment) (.lambda parameter body) name closed
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte, analyze]
        refine .callable (by simpa only [Code.subst, ↓reduceIte] using captures) ?_
        have environments :
            (fun other => if other = name then Summary.parameter 0 else (environment other).rename Nat.succ) =
            (fun other => if other = name then Summary.parameter 0 else
              (extendAnalysis environment name (analyze environment value) other).rename Nat.succ) := by
          funext other
          by_cases equal : other = name <;> simp [extendAnalysis, equal]
        rw [environments]
        exact ResultEq.refl _
      · simp only [Code.subst, if_neg same, analyze]
        refine .callable (by simpa only [Code.subst, if_neg same] using captures) ?_
        have bodyEq := analyze_code_substitution (environment :=
          fun other => if other = parameter then Summary.parameter 0 else (environment other).rename Nat.succ) body name closed
        have environments :
            extendAnalysis (fun other => if other = parameter then Summary.parameter 0 else (environment other).rename Nat.succ)
              name (analyze (fun other => if other = parameter then Summary.parameter 0 else (environment other).rename Nat.succ) value) =
            (fun other => if other = parameter then Summary.parameter 0 else
              (extendAnalysis environment name (analyze environment value) other).rename Nat.succ) := by
          funext other
          by_cases atName : other = name
          · subst other
            simp only [extendAnalysis, ↓reduceIte, if_neg same, closed_value_analysis_rename closed]
            exact closed_value_analysis_environment_independent closed
          · by_cases atParameter : other = parameter
            · subst other
              simp [extendAnalysis, Ne.symm same]
            · simp [extendAnalysis, atName, atParameter]
        rw [environments] at bodyEq
        exact bodyEq
  | bind parameter initializer body =>
      have initializerEq := analyze_code_substitution (environment := environment) initializer name closed
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte, analyze]
        apply analyze_result_congr (code := body)
        intro other
        by_cases atName : other = name
        · simp only [if_pos atName]
          exact initializerEq
        · simp only [if_neg atName, extendAnalysis]
          exact ResultEq.refl _
      · simp only [Code.subst, if_neg same, analyze]
        have bodyEq := analyze_code_substitution (environment := extendAnalysis environment parameter
          (analyze environment (initializer.subst name value))) body name closed
        apply bodyEq.trans
        apply analyze_result_congr (code := body)
        intro other
        by_cases atParameter : other = parameter
        · subst other
          simp only [extendAnalysis, if_neg (Ne.symm same), ↓reduceIte]
          exact initializerEq
        · by_cases atName : other = name
          · subst other
            simp only [extendAnalysis, ↓reduceIte, if_neg atParameter]
            rw [closed_value_analysis_environment_independent (second := environment) closed]
            exact ResultEq.refl _
          · simp only [extendAnalysis, if_neg atParameter, if_neg atName]
            exact ResultEq.refl _
termination_by sizeOf code

theorem known_lambda_result (parameter : Nat) (body : Code) :
    callResult (analyze environment (.lambda parameter body)) argument =
      analyze (extendAnalysis environment parameter argument) body := by
  simp only [analyze, callResult, Summary.instantiate, analyze_substitute]
  congr 1
  funext name
  by_cases same : name = parameter
  · simp only [if_pos same, Summary.substitute, extendAnalysis]
  · simp only [if_neg same, rename_substitute, extendAnalysis]
    exact substitute_parameters _

theorem beta_summary_correspondence (parameter : Nat) (body : Code)
    (closed : ScopedExpressions.ClosedValue value) :
    ResultEq (callResult (analyze environment (.lambda parameter body)) (analyze environment value))
      (analyze environment (body.subst parameter value)) := by
  rw [known_lambda_result]
  exact (analyze_code_substitution body parameter closed).symm

theorem bind_summary_correspondence (parameter : Nat) (body : Code)
    (closed : ScopedExpressions.ClosedValue value) :
    ResultEq (analyze environment (.bind parameter value body))
      (analyze environment (body.subst parameter value)) :=
  (analyze_code_substitution body parameter closed).symm

/-- The correspondence accompanies the same actual beta event. Its statement
    does not infer access, ownership or result realization from metadata. -/
theorem beta_constructs_summary_correspondence (parameter : Nat) (body : Code)
    (argumentClosed : ScopedExpressions.ClosedValue value)
    (functionClosed : ScopedExpressions.ClosedValue (.lambda parameter body)) :
    ScopedExecution.RawStep ⟨.app (.lambda parameter body) value, scope, tail⟩
      ⟨body.subst parameter value, .none, tail⟩ [] [] ∧
    ResultEq (callResult (analyze environment (.lambda parameter body)) (analyze environment value))
      (analyze environment (body.subst parameter value)) :=
  ⟨.beta parameter body value scope tail argumentClosed functionClosed,
    beta_summary_correspondence parameter body argumentClosed⟩

theorem bind_constructs_summary_correspondence (parameter : Nat) (body : Code)
    (valueClosed : ScopedExpressions.ClosedValue value)
    (suffixClosed : ScopedExpressions.ClosedExcept parameter body) :
    ScopedExecution.RawStep ⟨.bind parameter value body, scope, tail⟩
      ⟨body.subst parameter value, scope, tail⟩ [] [] ∧
    ResultEq (analyze environment (.bind parameter value body))
      (analyze environment (body.subst parameter value)) :=
  ⟨.bind parameter value body scope tail valueClosed suffixClosed,
    bind_summary_correspondence parameter body valueClosed⟩

namespace Examples

theorem retaining_factory_beta_correspondence :
    ResultEq (callResult (analyze (fun _ => .unknown) (.lambda 3 (.lambda 2 (.variable 3))))
      (analyze (fun _ => .unknown) (retainingConstant 7)))
      (analyze (fun _ => .unknown) ((Code.lambda 2 (.variable 3)).subst 3 (retainingConstant 7))) := by
  apply beta_summary_correspondence
  simp [ScopedExpressions.ClosedValue, retainingConstant, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Instantiation.ResourceName.freeNames, Code.dependencies, without]

theorem shadowed_parameter_substitution_correspondence
    (closed : ScopedExpressions.ClosedValue value) :
    ResultEq (analyze environment (.lambda 3 (.variable 3)))
      (analyze (extendAnalysis environment 3 (analyze environment value)) (.lambda 3 (.variable 3))) := by
  simpa only [Code.subst, ↓reduceIte] using analyze_code_substitution (.lambda 3 (.variable 3)) 3 closed

end Examples

end Ash.OneShot.ResultSummaries

#print axioms Ash.OneShot.ResultSummaries.expand_append
#print axioms Ash.OneShot.ResultSummaries.expand_without_same
#print axioms Ash.OneShot.ResultSummaries.expand_without
#print axioms Ash.OneShot.ResultSummaries.expand_resource_atoms
#print axioms Ash.OneShot.ResultSummaries.code_substitution_dependencies
#print axioms Ash.OneShot.ResultSummaries.clauses_substitution_dependencies
#print axioms Ash.OneShot.ResultSummaries.captured_append_support
#print axioms Ash.OneShot.ResultSummaries.expanded_capture_correspondence
#print axioms Ash.OneShot.ResultSummaries.code_capture_substitution
#print axioms Ash.OneShot.ResultSummaries.analyze_code_substitution
#print axioms Ash.OneShot.ResultSummaries.known_lambda_result
#print axioms Ash.OneShot.ResultSummaries.beta_summary_correspondence
#print axioms Ash.OneShot.ResultSummaries.bind_summary_correspondence
#print axioms Ash.OneShot.ResultSummaries.beta_constructs_summary_correspondence
#print axioms Ash.OneShot.ResultSummaries.bind_constructs_summary_correspondence
#print axioms Ash.OneShot.ResultSummaries.Examples.retaining_factory_beta_correspondence
#print axioms Ash.OneShot.ResultSummaries.Examples.shadowed_parameter_substitution_correspondence
