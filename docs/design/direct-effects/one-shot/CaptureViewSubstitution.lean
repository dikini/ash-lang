import CaptureViews

/-!
Concrete closed-value substitution compared through normalized capture/result
views. Pending applications retain their operands and callable result structure.
This remains substitution correspondence, not computation-result realization.
-/

namespace Ash.OneShot.CaptureViews
open ResultSummaries Syntax ScopedExpressions

theorem captured_congr (dependencies : List Dependency)
    (same : ∀ name, Related (first name) (second name)) :
    SameCapture (captured first dependencies) (captured second dependencies) := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      unfold SameCapture at ih
      unfold Related at same
      cases dependency with
      | resource | ticket => simp only [SameCapture, captured, normalize, View.capture, ih]
      | «variable» name => simp only [SameCapture, captured, normalize, View.capture, same name, ih]

theorem analyze_congr {code : Code}
    (same : ∀ name, Related (first name) (second name)) :
    Related (analyze first code) (analyze second code) := by
  cases code with
  | unit | boolean | integer => rfl
  | resourceRef name => cases name <;> rfl
  | «variable» name => exact same name
  | pair left right => exact Related.product (analyze_congr same) (analyze_congr same)
  | app function argument => exact Related.application (analyze_congr same) (analyze_congr same)
  | branch condition yes no => exact Related.join (analyze_congr same) (analyze_congr same)
  | perform | handle | resume | discard | resource | cleanup => rfl
  | lambda parameter body =>
      refine Related.callable (captured_congr _ same) (analyze_congr ?_)
      intro name
      split
      · rfl
      · exact (same name).rename Nat.succ
  | bind parameter initializer body =>
      apply analyze_congr (code := body)
        (first := fun name => if name = parameter then analyze first initializer else first name)
        (second := fun name => if name = parameter then analyze second initializer else second name)
      intro name
      split
      · exact analyze_congr same
      · exact same name
termination_by sizeOf code

theorem captured_append (left right : List Dependency) :
    (normalize (captured environment (left ++ right))).capture =
      (normalize (captured environment left)).capture ++ (normalize (captured environment right)).capture := by
  induction left with
  | nil => rfl
  | cons dependency rest ih => simp only [List.cons_append, captured, normalize, View.capture, ih, List.append_assoc]

theorem closed_captured_view
    (closed : ∀ dependency ∈ dependencies, match dependency with | .resource _ => True | _ => False) :
    (normalize (captured environment dependencies)).capture = (resourceDependencies dependencies).map Atom.resource := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      have first := closed dependency List.mem_cons_self
      have tail := ih (fun dep member => closed dep (List.mem_cons_of_mem _ member))
      cases dependency with
      | resource identity => simp [captured, normalize, View.capture, resourceDependencies, tail]
      | «variable» | ticket => cases first

/-- Actual closed values normalize to their exact resource storage atoms.
    This does not certify the result body of a callable. -/
theorem closed_value_capture_view {value : Code} (closed : ScopedExpressions.ClosedValue value) :
    (normalize (analyze environment value)).capture = (resourceDependencies value.dependencies).map Atom.resource := by
  cases value with
  | unit | boolean | integer => rfl
  | resourceRef name => cases name with
      | bound name => cases closed.2.1
      | activation identity => rfl
  | pair left right =>
      have leftClosed : ScopedExpressions.ClosedValue left :=
        ⟨closed.1.1, (List.append_eq_nil_iff.mp closed.2.1).1,
          fun dep member => closed.2.2 dep (List.mem_append_left _ member)⟩
      have rightClosed : ScopedExpressions.ClosedValue right :=
        ⟨closed.1.2, (List.append_eq_nil_iff.mp closed.2.1).2,
          fun dep member => closed.2.2 dep (List.mem_append_right _ member)⟩
      simp only [analyze, normalize, View.capture, Code.dependencies, ScopedExecution.resource_dependencies_append,
        List.map_append, closed_value_capture_view leftClosed, closed_value_capture_view rightClosed]
  | lambda parameter body => exact closed_captured_view closed.2.2
  | «variable» | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases closed.1
termination_by sizeOf value

theorem expanded_capture_correspondence (dependencies : List Dependency) (name : Nat)
    (closed : ScopedExpressions.ClosedValue value) :
    SameCapture (captured environment (expandDependencies name value.dependencies dependencies))
      (captured (extendAnalysis environment name (analyze environment value)) dependencies) := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      by_cases same : dependency = .variable name
      · subst dependency
        simp only [SameCapture, expandDependencies, List.flatMap_cons, ↓reduceIte] at ih ⊢
        rw [captured_append]
        simp only [captured, normalize, View.capture, extendAnalysis, ↓reduceIte,
          closed_captured_view closed.2.2, closed_value_capture_view closed, ih]
      · cases dependency <;> simp_all [SameCapture, expandDependencies, captured, normalize, View.capture, extendAnalysis]

theorem code_capture_substitution (code : Code) (name : Nat)
    (closed : ScopedExpressions.ClosedValue value) :
    SameCapture (captured environment (code.subst name value).dependencies)
      (captured (extendAnalysis environment name (analyze environment value)) code.dependencies) := by
  rw [code_substitution_dependencies code name closed]
  exact expanded_capture_correspondence _ name closed

/-- Concrete source substitution agrees with analysis in the extended
    environment modulo result structure and substitution-stable storage. -/
theorem analyze_code_substitution (code : Code) (name : Nat)
    (closed : ScopedExpressions.ClosedValue value) :
    Related (analyze environment (code.subst name value))
      (analyze (extendAnalysis environment name (analyze environment value)) code) := by
  cases code with
  | unit | boolean | integer => rfl
  | resourceRef reference => cases reference with
      | bound => rfl
      | activation => rfl
  | perform | handle | resume | discard | resource | cleanup => rfl
  | «variable» other =>
      by_cases same : name = other
      · subst other
        simp only [Code.subst, ↓reduceIte, analyze, extendAnalysis]
        exact Related.refl _
      · simp only [Code.subst, if_neg same, analyze, extendAnalysis, if_neg (Ne.symm same)]
        exact Related.refl _
  | pair left right => exact Related.product (analyze_code_substitution left name closed) (analyze_code_substitution right name closed)
  | app function argument => exact Related.application (analyze_code_substitution function name closed) (analyze_code_substitution argument name closed)
  | branch condition yes no => exact Related.join (analyze_code_substitution yes name closed) (analyze_code_substitution no name closed)
  | lambda parameter body =>
      have captures := code_capture_substitution (environment := environment) (.lambda parameter body) name closed
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte, analyze]
        refine Related.callable (by simpa only [Code.subst, ↓reduceIte] using captures) ?_
        have environments :
            (fun other => if other = name then Summary.parameter 0 else (environment other).rename Nat.succ) =
            (fun other => if other = name then Summary.parameter 0 else
              (extendAnalysis environment name (analyze environment value) other).rename Nat.succ) := by
          funext other
          by_cases equal : other = name <;> simp [extendAnalysis, equal]
        rw [environments]
        exact Related.refl _
      · simp only [Code.subst, if_neg same, analyze]
        refine Related.callable (by simpa only [Code.subst, if_neg same] using captures) ?_
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
        apply analyze_congr (code := body)
        intro other
        by_cases atName : other = name
        · simp only [if_pos atName]
          exact initializerEq
        · simp only [if_neg atName, extendAnalysis]
          exact Related.refl _
      · simp only [Code.subst, if_neg same, analyze]
        have bodyEq := analyze_code_substitution (environment := extendAnalysis environment parameter
          (analyze environment (initializer.subst name value))) body name closed
        apply bodyEq.trans
        apply analyze_congr (code := body)
        intro other
        by_cases atParameter : other = parameter
        · subst other
          simp only [extendAnalysis, if_neg (Ne.symm same), ↓reduceIte]
          exact initializerEq
        · by_cases atName : other = name
          · subst other
            simp only [extendAnalysis, ↓reduceIte, if_neg atParameter]
            rw [closed_value_analysis_environment_independent (second := environment) closed]
            exact Related.refl _
          · simp only [extendAnalysis, if_neg atParameter, if_neg atName]
            exact Related.refl _
termination_by sizeOf code

theorem beta_summary_correspondence (parameter : Nat) (body : Code)
    (closed : ScopedExpressions.ClosedValue value) :
    Related (ResultSummaries.callResult (analyze environment (.lambda parameter body)) (analyze environment value))
      (analyze environment (body.subst parameter value)) := by
  rw [known_lambda_result]
  exact (analyze_code_substitution body parameter closed).symm

theorem bind_summary_correspondence (parameter : Nat) (body : Code)
    (closed : ScopedExpressions.ClosedValue value) :
    Related (analyze environment (.bind parameter value body))
      (analyze environment (body.subst parameter value)) :=
  (analyze_code_substitution body parameter closed).symm

/-- The correspondence accompanies the same actual beta event. Its statement
    does not infer access, ownership or result realization from metadata. -/
theorem beta_constructs_summary_correspondence (parameter : Nat) (body : Code)
    (argumentClosed : ScopedExpressions.ClosedValue value)
    (functionClosed : ScopedExpressions.ClosedValue (.lambda parameter body)) :
    ScopedExecution.RawStep ⟨.app (.lambda parameter body) value, scope, tail⟩
      ⟨body.subst parameter value, .none, tail⟩ [] [] ∧
    Related (ResultSummaries.callResult (analyze environment (.lambda parameter body)) (analyze environment value))
      (analyze environment (body.subst parameter value)) :=
  ⟨.beta parameter body value scope tail argumentClosed functionClosed,
    beta_summary_correspondence parameter body argumentClosed⟩

theorem bind_constructs_summary_correspondence (parameter : Nat) (body : Code)
    (valueClosed : ScopedExpressions.ClosedValue value)
    (suffixClosed : ScopedExpressions.ClosedExcept parameter body) :
    ScopedExecution.RawStep ⟨.bind parameter value body, scope, tail⟩
      ⟨body.subst parameter value, scope, tail⟩ [] [] ∧
    Related (analyze environment (.bind parameter value body))
      (analyze environment (body.subst parameter value)) :=
  ⟨.bind parameter value body scope tail valueClosed suffixClosed,
    bind_summary_correspondence parameter body valueClosed⟩

namespace Examples

theorem retaining_factory_beta_correspondence :
    Related (ResultSummaries.callResult (analyze (fun _ => .unknown) (.lambda 3 (.lambda 2 (.variable 3))))
      (analyze (fun _ => .unknown) (ResultSummaries.Examples.retainingConstant 7)))
      (analyze (fun _ => .unknown) ((Code.lambda 2 (.variable 3)).subst 3 (ResultSummaries.Examples.retainingConstant 7))) := by
  apply beta_summary_correspondence
  simp [ScopedExpressions.ClosedValue, ResultSummaries.Examples.retainingConstant, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Instantiation.ResourceName.freeNames, Code.dependencies, without]

theorem shadowed_parameter_substitution_correspondence
    (closed : ScopedExpressions.ClosedValue value) :
    Related (analyze environment (.lambda 3 (.variable 3)))
      (analyze (extendAnalysis environment 3 (analyze environment value)) (.lambda 3 (.variable 3))) := by
  simpa only [Code.subst, ↓reduceIte] using analyze_code_substitution (.lambda 3 (.variable 3)) 3 closed

end Examples

end Ash.OneShot.CaptureViews

#print axioms Ash.OneShot.CaptureViews.captured_congr
#print axioms Ash.OneShot.CaptureViews.analyze_congr
#print axioms Ash.OneShot.CaptureViews.captured_append
#print axioms Ash.OneShot.CaptureViews.closed_captured_view
#print axioms Ash.OneShot.CaptureViews.closed_value_capture_view
#print axioms Ash.OneShot.CaptureViews.expanded_capture_correspondence
#print axioms Ash.OneShot.CaptureViews.code_capture_substitution
#print axioms Ash.OneShot.CaptureViews.analyze_code_substitution
#print axioms Ash.OneShot.CaptureViews.beta_summary_correspondence
#print axioms Ash.OneShot.CaptureViews.bind_summary_correspondence
#print axioms Ash.OneShot.CaptureViews.beta_constructs_summary_correspondence
#print axioms Ash.OneShot.CaptureViews.bind_constructs_summary_correspondence
#print axioms Ash.OneShot.CaptureViews.Examples.retaining_factory_beta_correspondence
#print axioms Ash.OneShot.CaptureViews.Examples.shadowed_parameter_substitution_correspondence
