import ResultSummaries

/-!
Substitution-stable comparison for result metadata. Storage observations may
forget the shape of a captured value, but result and application structure
remain explicit. These relations do not by themselves realize actual values.
-/

namespace Ash.OneShot.ResultSummaries

theorem lift_rename_comp (first second : Nat → Nat) :
    (fun index => liftRename second (liftRename first index)) =
      liftRename (fun index => second (first index)) := by
  funext index
  cases index <;> rfl

theorem rename_comp (summary : Summary) (first second : Nat → Nat) :
    (summary.rename first).rename second = summary.rename (fun index => second (first index)) := by
  induction summary generalizing first second <;> simp_all [Summary.rename, lift_rename_comp]

@[simp] theorem substitute_parameters (summary : Summary) :
    summary.substitute Summary.parameter = summary := by
  have lifted : liftSubstitution Summary.parameter = Summary.parameter := by
    funext index
    cases index <;> rfl
  induction summary <;> simp_all [Summary.substitute]

theorem rename_substitute (summary : Summary) (rename : Nat → Nat) (substitute : Nat → Summary) :
    (summary.rename rename).substitute substitute = summary.substitute (fun index => substitute (rename index)) := by
  induction summary generalizing rename substitute with
  | scalar | resource | parameter | unknown => rfl
  | product | application | join => simp_all [Summary.rename, Summary.substitute]
  | callable captures result ihCaptures ihResult =>
      have lifted : (fun index => liftSubstitution substitute (liftRename rename index)) =
          liftSubstitution (fun index => substitute (rename index)) := by
        funext index
        cases index <;> rfl
      simp [Summary.rename, Summary.substitute, ihCaptures, ihResult, lifted]

theorem substitute_rename (summary : Summary) (substitute : Nat → Summary) (rename : Nat → Nat) :
    (summary.substitute substitute).rename rename = summary.substitute (fun index => (substitute index).rename rename) := by
  induction summary generalizing substitute rename with
  | scalar | resource | parameter | unknown => rfl
  | product | application | join => simp_all [Summary.rename, Summary.substitute]
  | callable captures result ihCaptures ihResult =>
      have lifted : (fun index => (liftSubstitution substitute index).rename (liftRename rename)) =
          liftSubstitution (fun index => (substitute index).rename rename) := by
        funext index
        cases index with
        | zero => rfl
        | succ index => simp only [liftSubstitution, rename_comp]; rfl
      simp [Summary.rename, Summary.substitute, ihCaptures, ihResult, lifted]

theorem substitute_comp (summary : Summary) (first second : Nat → Summary) :
    (summary.substitute first).substitute second =
      summary.substitute (fun index => (first index).substitute second) := by
  induction summary generalizing first second with
  | scalar | resource | parameter | unknown => rfl
  | product | application | join => simp_all [Summary.substitute]
  | callable captures result ihCaptures ihResult =>
      have lifted : (fun index => (liftSubstitution first index).substitute (liftSubstitution second)) =
          liftSubstitution (fun index => (first index).substitute second) := by
        funext index
        cases index with
        | zero => rfl
        | succ index => simp only [liftSubstitution, rename_substitute, substitute_rename]
      simp [Summary.substitute, ihCaptures, ihResult, lifted]

theorem support_substitution_congr (summary : Summary)
    (same : ∀ index, (first index).support = (second index).support) :
    (summary.substitute first).support = (summary.substitute second).support := by
  induction summary with
  | scalar | resource | unknown => rfl
  | parameter index => exact same index
  | product | join => simp_all [Summary.substitute, Summary.support]
  | callable _ _ captures => exact captures
  | application => rfl

/-- Compare storage after every parameter substitution, including substitutions
    that resolve parameters previously reporting unknown support. -/
def StorageEq (left right : Summary) : Prop :=
  ∀ substitute, (left.substitute substitute).support = (right.substitute substitute).support

namespace StorageEq

theorem refl (summary : Summary) : StorageEq summary summary := fun _ => rfl

theorem symm (equivalent : StorageEq left right) : StorageEq right left := fun substitute => (equivalent substitute).symm

theorem trans (first : StorageEq left middle) (second : StorageEq middle right) : StorageEq left right :=
  fun substitute => (first substitute).trans (second substitute)

theorem support (equivalent : StorageEq left right) : left.support = right.support := by
  simpa using equivalent Summary.parameter

theorem substitute (equivalent : StorageEq left right) (substitute : Nat → Summary) :
    StorageEq (left.substitute substitute) (right.substitute substitute) := by
  intro next
  simpa only [substitute_comp] using equivalent (fun index => (substitute index).substitute next)

theorem rename (equivalent : StorageEq left right) (rename : Nat → Nat) :
    StorageEq (left.rename rename) (right.rename rename) := by
  intro substitute
  simpa only [rename_substitute] using equivalent (fun index => substitute (rename index))

theorem substitute_congr (equivalent : StorageEq left right)
    (same : ∀ index, StorageEq (first index) (second index)) :
    StorageEq (left.substitute first) (right.substitute second) := by
  intro next
  simp only [substitute_comp]
  exact (equivalent _).trans (support_substitution_congr right (fun index => same index next))

theorem callable_captures (captures result : Summary) : StorageEq (.callable captures result) captures := fun _ => rfl

end StorageEq

/-- Result equivalence preserves callable, parameter and application structure.
    Only a callable's capture component uses storage observations. -/
inductive ResultEq : Summary → Summary → Prop where
  | scalar : ResultEq .scalar .scalar
  | resource : ResultEq (.resource identity) (.resource identity)
  | parameter : ResultEq (.parameter index) (.parameter index)
  | product : ResultEq left first → ResultEq right second → ResultEq (.product left right) (.product first second)
  | callable : StorageEq captures saved → ResultEq body result → ResultEq (.callable captures body) (.callable saved result)
  | application : ResultEq function target → ResultEq argument supplied → ResultEq (.application function argument) (.application target supplied)
  | join : ResultEq left first → ResultEq right second → ResultEq (.join left right) (.join first second)
  | unknown : ResultEq .unknown .unknown

namespace ResultEq

theorem refl (summary : Summary) : ResultEq summary summary := by
  induction summary with
  | scalar => exact .scalar
  | resource => exact .resource
  | parameter => exact .parameter
  | product _ _ first second => exact .product first second
  | callable captures _ _ result => exact .callable (StorageEq.refl captures) result
  | application _ _ first second => exact .application first second
  | join _ _ first second => exact .join first second
  | unknown => exact .unknown

theorem symm (equivalent : ResultEq left right) : ResultEq right left := by
  induction equivalent with
  | scalar => exact .scalar
  | resource => exact .resource
  | parameter => exact .parameter
  | product _ _ first second => exact .product first second
  | callable captures _ result => exact .callable captures.symm result
  | application _ _ first second => exact .application first second
  | join _ _ first second => exact .join first second
  | unknown => exact .unknown

theorem storage (equivalent : ResultEq left right) : StorageEq left right := by
  intro substitute
  induction equivalent with
  | scalar | resource | parameter | unknown => rfl
  | product | join => simp_all [Summary.substitute, Summary.support]
  | callable captures => exact captures substitute
  | application => rfl

theorem substitute (equivalent : ResultEq left right) (substitute : Nat → Summary) :
    ResultEq (left.substitute substitute) (right.substitute substitute) := by
  induction equivalent generalizing substitute with
  | scalar => exact .scalar
  | resource => exact .resource
  | parameter => exact refl _
  | product _ _ first second => exact .product (first substitute) (second substitute)
  | callable captures _ result => exact .callable (captures.substitute substitute) (result _)
  | application _ _ first second => exact .application (first substitute) (second substitute)
  | join _ _ first second => exact .join (first substitute) (second substitute)
  | unknown => exact .unknown

theorem rename (equivalent : ResultEq left right) (rename : Nat → Nat) :
    ResultEq (left.rename rename) (right.rename rename) := by
  induction equivalent generalizing rename with
  | scalar => exact .scalar
  | resource => exact .resource
  | parameter => exact .parameter
  | product _ _ first second => exact .product (first rename) (second rename)
  | callable captures _ result => exact .callable (captures.rename rename) (result _)
  | application _ _ first second => exact .application (first rename) (second rename)
  | join _ _ first second => exact .join (first rename) (second rename)
  | unknown => exact .unknown

theorem trans (first : ResultEq left middle) (second : ResultEq middle right) : ResultEq left right := by
  induction first generalizing right with
  | scalar => cases second; exact .scalar
  | resource => cases second; exact .resource
  | parameter => cases second; exact .parameter
  | unknown => cases second; exact .unknown
  | product _ _ ihLeft ihRight =>
      cases second with
      | product left right => exact .product (ihLeft left) (ihRight right)
  | application _ _ ihFunction ihArgument =>
      cases second with
      | application function argument => exact .application (ihFunction function) (ihArgument argument)
  | join _ _ ihLeft ihRight =>
      cases second with
      | join left right => exact .join (ihLeft left) (ihRight right)
  | callable captures _ ihResult =>
      cases second with
      | callable saved result => exact .callable (captures.trans saved) (ihResult result)

theorem substitute_congr (equivalent : ResultEq left right)
    (same : ∀ index, ResultEq (first index) (second index)) :
    ResultEq (left.substitute first) (right.substitute second) := by
  induction equivalent generalizing first second with
  | scalar => exact .scalar
  | resource => exact .resource
  | parameter => exact same _
  | product _ _ ihLeft ihRight => exact .product (ihLeft same) (ihRight same)
  | application _ _ ihFunction ihArgument => exact .application (ihFunction same) (ihArgument same)
  | join _ _ ihLeft ihRight => exact .join (ihLeft same) (ihRight same)
  | unknown => exact .unknown
  | callable captures _ ihResult =>
      refine .callable (captures.substitute_congr (fun index => (same index).storage)) (ihResult ?_)
      intro index
      cases index with
      | zero => exact .parameter
      | succ index => exact (same index).rename Nat.succ

theorem call_result (functionEq : ResultEq function target) (argumentEq : ResultEq argument supplied) :
    ResultEq (callResult function argument) (callResult target supplied) := by
  cases functionEq with
  | scalar => exact .application .scalar argumentEq
  | resource => exact .application .resource argumentEq
  | parameter => exact .application .parameter argumentEq
  | product left right => exact .application (.product left right) argumentEq
  | application function argument => exact .application (.application function argument) argumentEq
  | join left right => exact .application (.join left right) argumentEq
  | unknown => exact .application .unknown argumentEq
  | callable captures result =>
      apply result.substitute_congr
      intro index
      cases index with
      | zero => exact argumentEq
      | succ index => exact .parameter

end ResultEq
open Syntax ScopedExpressions

theorem captured_rename (dependencies : List Dependency) :
    (captured environment dependencies).rename rename = captured (fun name => (environment name).rename rename) dependencies := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih => cases dependency <;> simp [captured, Summary.rename, ih]

theorem captured_substitute (dependencies : List Dependency) :
    (captured environment dependencies).substitute substitute =
      captured (fun name => (environment name).substitute substitute) dependencies := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih => cases dependency <;> simp [captured, Summary.substitute, ih]

theorem captured_result_congr (dependencies : List Dependency)
    (same : ∀ name, ResultEq (first name) (second name)) :
    StorageEq (captured first dependencies) (captured second dependencies) := by
  intro substitute
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      cases dependency with
      | resource | ticket => simp [captured, Summary.substitute, Summary.support, ih]
      | «variable» name => simp [captured, Summary.substitute, Summary.support, (same name).storage substitute, ih]

theorem analyze_result_congr {code : Code}
    (same : ∀ name, ResultEq (first name) (second name)) :
    ResultEq (analyze first code) (analyze second code) := by
  cases code with
  | unit | boolean | integer => exact .scalar
  | resourceRef name => cases name with
      | bound => exact .unknown
      | activation => exact .resource
  | «variable» name => exact same name
  | pair left right => exact .product (analyze_result_congr same) (analyze_result_congr same)
  | app function argument => exact .application (analyze_result_congr same) (analyze_result_congr same)
  | branch condition yes no => exact .join (analyze_result_congr same) (analyze_result_congr same)
  | perform | handle | resume | discard | resource | cleanup => exact .unknown
  | lambda parameter body =>
      refine .callable (captured_result_congr _ same) (analyze_result_congr ?_)
      intro name
      split
      · exact .parameter
      · exact (same name).rename Nat.succ
  | bind parameter initializer body =>
      apply analyze_result_congr (code := body)
        (first := fun name => if name = parameter then analyze first initializer else first name)
        (second := fun name => if name = parameter then analyze second initializer else second name)
      intro name
      split
      · exact analyze_result_congr same
      · exact same name
termination_by sizeOf code

theorem analyze_rename (code : Code) (environment : Environment) (rename : Nat → Nat) :
    (analyze environment code).rename rename = analyze (fun name => (environment name).rename rename) code := by
  cases code with
  | unit | boolean | integer | «variable» | perform | handle | resume | discard | resource | cleanup => rfl
  | resourceRef name => cases name <;> rfl
  | pair left right | app left right => simp only [analyze, Summary.rename, analyze_rename left, analyze_rename right]
  | branch condition yes no => simp only [analyze, Summary.rename, analyze_rename yes, analyze_rename no]
  | lambda parameter body =>
      simp only [analyze, Summary.rename, captured_rename, analyze_rename body]
      congr 2
      funext name
      split <;> simp only [Summary.rename, liftRename, rename_comp]
  | bind parameter initializer body =>
      simp only [analyze, analyze_rename body]
      congr 1
      funext name
      split <;> simp only [analyze_rename initializer]
termination_by sizeOf code

theorem analyze_substitute (code : Code) (environment : Environment) (substitute : Nat → Summary) :
    (analyze environment code).substitute substitute =
      analyze (fun name => (environment name).substitute substitute) code := by
  cases code with
  | unit | boolean | integer | «variable» | perform | handle | resume | discard | resource | cleanup => rfl
  | resourceRef name => cases name <;> rfl
  | pair left right | app left right => simp only [analyze, Summary.substitute, analyze_substitute left, analyze_substitute right]
  | branch condition yes no => simp only [analyze, Summary.substitute, analyze_substitute yes, analyze_substitute no]
  | lambda parameter body =>
      simp only [analyze, Summary.substitute, captured_substitute, analyze_substitute body]
      congr 2
      funext name
      split <;> simp only [Summary.substitute, liftSubstitution, rename_substitute, substitute_rename]
  | bind parameter initializer body =>
      simp only [analyze, analyze_substitute body]
      congr 1
      funext name
      split <;> simp only [analyze_substitute initializer]
termination_by sizeOf code

theorem captured_environment_congr {dependencies : List Dependency}
    (same : ∀ name, Dependency.variable name ∈ dependencies → first name = second name) :
    captured first dependencies = captured second dependencies := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      have tail := ih (fun name member => same name (List.mem_cons_of_mem _ member))
      cases dependency with
      | resource | ticket => simp [captured, tail]
      | «variable» name => simp [captured, tail, same name List.mem_cons_self]

theorem analyze_environment_congr {code : Code}
    (same : ∀ name, Dependency.variable name ∈ code.dependencies → first name = second name) :
    analyze first code = analyze second code := by
  cases code with
  | unit | boolean | integer | perform | handle | resume | discard | resource | cleanup => rfl
  | resourceRef name => cases name <;> rfl
  | «variable» name => exact same name List.mem_cons_self
  | pair left right | app left right =>
      have leftEq := analyze_environment_congr (code := left) (fun name member => same name (List.mem_append_left _ member))
      have rightEq := analyze_environment_congr (code := right) (fun name member => same name (List.mem_append_right _ member))
      simp only [analyze, leftEq, rightEq]
  | branch condition yes no =>
      have yesEq := analyze_environment_congr (code := yes)
        (fun name member => same name (List.mem_append_left _ (List.mem_append_right _ member)))
      have noEq := analyze_environment_congr (code := no) (fun name member => same name (List.mem_append_right _ member))
      simp only [analyze, yesEq, noEq]
  | lambda parameter body =>
      have capturesEq := captured_environment_congr same
      simp only [analyze, capturesEq]
      congr 1
      apply analyze_environment_congr (code := body)
      intro name member
      by_cases equal : name = parameter
      · simp only [equal, if_pos]
      · simp only [if_neg equal]
        rw [same name (mem_without.mpr ⟨member, by simpa using equal⟩)]
  | bind parameter initializer body =>
      have initializerEq := analyze_environment_congr (code := initializer)
        (fun name member => same name (List.mem_append_left _ member))
      apply analyze_environment_congr (code := body)
        (first := fun name => if name = parameter then analyze first initializer else first name)
        (second := fun name => if name = parameter then analyze second initializer else second name)
      intro name member
      by_cases equal : name = parameter
      · simp only [if_pos equal, initializerEq]
      · simp only [if_neg equal]
        exact same name (List.mem_append_right _ (mem_without.mpr ⟨member, by simpa using equal⟩))
termination_by sizeOf code

theorem closed_value_analysis_environment_independent (closed : ScopedExpressions.ClosedValue value) :
    analyze first value = analyze second value := by
  apply analyze_environment_congr
  intro name member
  exact False.elim (closed.2.2 (.variable name) member)

theorem closed_value_analysis_rename (closed : ScopedExpressions.ClosedValue value) :
    (analyze environment value).rename rename = analyze environment value :=
  (analyze_rename _ _ _).trans (closed_value_analysis_environment_independent closed)

theorem closed_value_analysis_substitute (closed : ScopedExpressions.ClosedValue value) :
    (analyze environment value).substitute substitute = analyze environment value :=
  (analyze_substitute _ _ _).trans (closed_value_analysis_environment_independent closed)

namespace Examples

theorem factory_beta_summaries_correspond :
    ResultEq
      (callResult (analyze (fun _ => .unknown) (.lambda 3 (.lambda 2 (.variable 3))))
        (analyze (fun _ => .unknown) (retainingConstant 7)))
      (analyze (fun _ => .unknown) ((ScopedExpressions.Code.lambda 2 (.variable 3)).subst 3 (retainingConstant 7))) := by
  apply ResultEq.callable
  · intro substitute
    rfl
  · exact ResultEq.refl _

theorem distinct_parameters_not_storage_equivalent : ¬ StorageEq (.parameter 0) (.parameter 1) := by
  intro equivalent
  have impossible := equivalent (fun index => .resource index)
  contradiction

theorem unknown_not_parameter_equivalent : ¬ StorageEq .unknown (.parameter 0) := by
  intro equivalent
  have impossible := equivalent (fun _ => .scalar)
  contradiction

theorem equal_storage_does_not_equate_callable_results :
    StorageEq (.callable .scalar .scalar) (.callable .scalar (.resource 7)) ∧
    ¬ ResultEq (.callable .scalar .scalar) (.callable .scalar (.resource 7)) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro equivalent
  cases equivalent with
  | callable _ result => cases result

end Examples

end Ash.OneShot.ResultSummaries

#print axioms Ash.OneShot.ResultSummaries.lift_rename_comp
#print axioms Ash.OneShot.ResultSummaries.rename_comp
#print axioms Ash.OneShot.ResultSummaries.substitute_parameters
#print axioms Ash.OneShot.ResultSummaries.rename_substitute
#print axioms Ash.OneShot.ResultSummaries.substitute_rename
#print axioms Ash.OneShot.ResultSummaries.substitute_comp
#print axioms Ash.OneShot.ResultSummaries.support_substitution_congr
#print axioms Ash.OneShot.ResultSummaries.StorageEq.refl
#print axioms Ash.OneShot.ResultSummaries.StorageEq.symm
#print axioms Ash.OneShot.ResultSummaries.StorageEq.trans
#print axioms Ash.OneShot.ResultSummaries.StorageEq.support
#print axioms Ash.OneShot.ResultSummaries.StorageEq.substitute
#print axioms Ash.OneShot.ResultSummaries.StorageEq.rename
#print axioms Ash.OneShot.ResultSummaries.StorageEq.substitute_congr
#print axioms Ash.OneShot.ResultSummaries.StorageEq.callable_captures
#print axioms Ash.OneShot.ResultSummaries.ResultEq.refl
#print axioms Ash.OneShot.ResultSummaries.ResultEq.symm
#print axioms Ash.OneShot.ResultSummaries.ResultEq.storage
#print axioms Ash.OneShot.ResultSummaries.ResultEq.substitute
#print axioms Ash.OneShot.ResultSummaries.ResultEq.rename
#print axioms Ash.OneShot.ResultSummaries.ResultEq.trans
#print axioms Ash.OneShot.ResultSummaries.ResultEq.substitute_congr
#print axioms Ash.OneShot.ResultSummaries.ResultEq.call_result
#print axioms Ash.OneShot.ResultSummaries.captured_rename
#print axioms Ash.OneShot.ResultSummaries.captured_substitute
#print axioms Ash.OneShot.ResultSummaries.captured_result_congr
#print axioms Ash.OneShot.ResultSummaries.analyze_result_congr
#print axioms Ash.OneShot.ResultSummaries.analyze_rename
#print axioms Ash.OneShot.ResultSummaries.analyze_substitute
#print axioms Ash.OneShot.ResultSummaries.captured_environment_congr
#print axioms Ash.OneShot.ResultSummaries.analyze_environment_congr
#print axioms Ash.OneShot.ResultSummaries.closed_value_analysis_environment_independent
#print axioms Ash.OneShot.ResultSummaries.closed_value_analysis_rename
#print axioms Ash.OneShot.ResultSummaries.closed_value_analysis_substitute
#print axioms Ash.OneShot.ResultSummaries.Examples.factory_beta_summaries_correspond
#print axioms Ash.OneShot.ResultSummaries.Examples.distinct_parameters_not_storage_equivalent
#print axioms Ash.OneShot.ResultSummaries.Examples.unknown_not_parameter_equivalent
#print axioms Ash.OneShot.ResultSummaries.Examples.equal_storage_does_not_equate_callable_results
