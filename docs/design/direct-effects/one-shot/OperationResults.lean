import ContinuationBounds

/-!
Signature-aware stored-result analysis on the existing Code grammar. Exact
realized operation keys select declared result ports; unresolved keys remain
unknown. This module establishes analysis and substitution properties, not
general execution soundness or initial-term admission.
-/

namespace Ash.OneShot.OperationResults
open Instantiation Syntax ScopedExpressions ScopedExecution ScopedPorts
open ResultSummaries (Summary captured extendAnalysis)
open ReturnSupport (Below)
open ContinuationBounds (portBound)

def decodeName : ResourceName → Option Nat
  | .activation identity => some identity
  | .bound _ => none

def decodeArgument : Argument → Option TypeArgument
  | .nominal identity => some (.nominal identity)
  | .resource name => (decodeName name).map TypeArgument.resource
  | .apply head argument => do
      let left ← decodeArgument head
      let right ← decodeArgument argument
      pure (.apply left right)

def decodeArguments : List Argument → Option (List TypeArgument)
  | [] => some []
  | head :: tail => do
      let first ← decodeArgument head
      let rest ← decodeArguments tail
      pure (first :: rest)

def decodeEffect : Effect → Option Instance
  | .user family arguments => (decodeArguments arguments).map (Instance.user family)
  | .cell name => (decodeName name).map Instance.cell

theorem decode_frozen_argument (argument : TypeArgument) : decodeArgument (freezeArgument argument) = some argument := by
  induction argument with
  | nominal | resource => rfl
  | apply head argument ihHead ihArgument => simp [freezeArgument, decodeArgument, ihHead, ihArgument]

theorem decode_frozen_arguments (arguments : List TypeArgument) :
    decodeArguments (arguments.map freezeArgument) = some arguments := by
  induction arguments with
  | nil => rfl
  | cons head tail ih => simp [decodeArguments, decode_frozen_argument, ih]

theorem decode_frozen_effect (effect : Instance) : decodeEffect (freezeEffect effect) = some effect := by
  cases effect with
  | user => simp [freezeEffect, decodeEffect, decode_frozen_arguments]
  | cell => rfl

def operationBound (signature : Signature) (effect : Effect) (operation : Nat) : Summary :=
  match decodeEffect effect with
  | none => .unknown
  | some key => match signature key operation with
      | none => .unknown
      | some (_, output) => portBound output

theorem operation_bound_known (known : signature effect operation = some (input, output)) :
    operationBound signature (freezeEffect effect) operation = portBound output := by
  simp [operationBound, decode_frozen_effect, known]

def analyze (signature : Signature) (environment : ResultSummaries.Environment) : Code → Summary
  | .unit | .boolean _ | .integer _ => .scalar
  | .variable name => environment name
  | .resourceRef (.activation identity) => .resource identity
  | .resourceRef (.bound _) => .unknown
  | .pair left right => .product (analyze signature environment left) (analyze signature environment right)
  | .lambda parameter body =>
      .callable (captured environment (Code.lambda parameter body).dependencies)
        (analyze signature (fun name => if name = parameter then .parameter 0 else (environment name).rename Nat.succ) body)
  | .app function argument => .application (analyze signature environment function) (analyze signature environment argument)
  | .bind parameter initializer body =>
      analyze signature (fun name => if name = parameter then analyze signature environment initializer else environment name) body
  | .branch _ yes no => .join (analyze signature environment yes) (analyze signature environment no)
  | .perform effect operation _ => operationBound signature effect operation
  | .handle _ _ _ | .resume _ _ | .discard _ | .resource _ _ _ | .cleanup _ _ => .unknown

theorem analyze_perform_known (known : signature effect operation = some (input, output)) :
    analyze signature environment (.perform (freezeEffect effect) operation operand) = portBound output :=
  operation_bound_known known

theorem captured_support_congr (dependencies : List Dependency)
    (same : ∀ name, (first name).support = (second name).support) :
    (captured first dependencies).support = (captured second dependencies).support := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih => cases dependency with
      | resource | ticket => simp [captured, Summary.support, ih]
      | «variable» name => simp [captured, Summary.support, same name, ih]

theorem analyze_support_congr (code : Code)
    (same : ∀ name, (first name).support = (second name).support) :
    (analyze signature first code).support = (analyze signature second code).support := by
  cases code with
  | unit | boolean | integer | app | perform | handle | resume | discard | resource | cleanup => rfl
  | resourceRef name => cases name <;> rfl
  | «variable» name => exact same name
  | pair left right => simp only [analyze, Summary.support, analyze_support_congr left same, analyze_support_congr right same]
  | branch condition yes no => simp only [analyze, Summary.support, analyze_support_congr yes same, analyze_support_congr no same]
  | lambda parameter body => exact captured_support_congr _ same
  | bind parameter initializer body =>
      apply analyze_support_congr body
      intro name
      split
      · exact analyze_support_congr initializer same
      · exact same name
termination_by sizeOf code

theorem analyze_monotone (code : Code) (bound : ∀ name, Below (first name) (second name)) :
    Below (analyze signature first code) (analyze signature second code) := by
  cases code with
  | unit | boolean | integer | perform | handle | resume | discard | resource | cleanup => exact Below.refl _
  | resourceRef name => cases name <;> exact Below.refl _
  | «variable» name => exact bound name
  | pair left right => exact Below.combine (analyze_monotone left bound) (analyze_monotone right bound)
  | branch condition yes no => exact Below.join (analyze_monotone yes bound) (analyze_monotone no bound)
  | app => exact Below.unknown _
  | lambda parameter body => exact ReturnSupport.captured_monotone _ bound
  | bind parameter initializer body =>
      apply analyze_monotone body
      intro name
      split
      · exact analyze_monotone initializer bound
      · exact bound name
termination_by sizeOf code

/-- Exact storage of actual closed values is unchanged; a callable's result
    metadata is separate from the resources physically retained by it. -/
theorem closed_value_storage_sound (closed : ScopedExpressions.ClosedValue value) :
    (analyze signature environment value).support = some (resourceDependencies value.dependencies) := by
  cases value with
  | unit | boolean | integer => rfl
  | resourceRef name => cases name with
      | activation => rfl
      | bound => cases closed.2.1
  | lambda => exact ResultSummaries.captured_support_when_closed closed.2.2
  | pair left right =>
      have leftClosed : ScopedExpressions.ClosedValue left := ⟨closed.1.1, (List.append_eq_nil_iff.mp closed.2.1).1,
        fun dependency member => closed.2.2 dependency (List.mem_append_left _ member)⟩
      have rightClosed : ScopedExpressions.ClosedValue right := ⟨closed.1.2, (List.append_eq_nil_iff.mp closed.2.1).2,
        fun dependency member => closed.2.2 dependency (List.mem_append_right _ member)⟩
      simp [analyze, Summary.support, Code.dependencies, resourceDependencies,
        closed_value_storage_sound leftClosed, closed_value_storage_sound rightClosed]
  | «variable» | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases closed.1
termination_by sizeOf value

theorem closed_value_old_support (closed : ScopedExpressions.ClosedValue value) :
    (analyze signature environment value).support = (ResultSummaries.analyze other value).support := by
  rw [closed_value_storage_sound closed, ResultSummaries.closed_value_storage_sound closed]

theorem closed_value_environment_support (closed : ScopedExpressions.ClosedValue value) :
    (analyze signature first value).support = (analyze signature second value).support := by
  rw [closed_value_storage_sound closed, closed_value_storage_sound closed]

theorem capture_substitution_support (code : Code) (name : Nat) (closed : ScopedExpressions.ClosedValue value) :
    (captured environment (code.subst name value).dependencies).support =
      (captured (extendAnalysis environment name (analyze signature environment value)) code.dependencies).support := by
  apply (ResultSummaries.code_capture_substitution code name closed).support.trans
  apply captured_support_congr
  intro other
  by_cases same : other = name
  · simp only [extendAnalysis, if_pos same]
    exact (closed_value_old_support closed).symm
  · simp only [extendAnalysis, if_neg same]

theorem analyze_substitution_support (code : Code) (name : Nat) (closed : ScopedExpressions.ClosedValue value) :
    (analyze signature environment (code.subst name value)).support =
      (analyze signature (extendAnalysis environment name (analyze signature environment value)) code).support := by
  cases code with
  | unit | boolean | integer | app | perform | handle | resume | discard | resource | cleanup => rfl
  | resourceRef reference => cases reference <;> rfl
  | «variable» other =>
      by_cases same : name = other
      · subst other
        simp [Code.subst, analyze, extendAnalysis]
      · simp [Code.subst, analyze, extendAnalysis, same, Ne.symm same]
  | pair left right =>
      simp only [Code.subst, analyze, Summary.support,
        analyze_substitution_support left name closed, analyze_substitution_support right name closed]
  | branch condition yes no =>
      simp only [Code.subst, analyze, Summary.support,
        analyze_substitution_support yes name closed, analyze_substitution_support no name closed]
  | lambda parameter body => exact capture_substitution_support (.lambda parameter body) name closed
  | bind parameter initializer body =>
      have first := analyze_substitution_support (signature := signature) (environment := environment) initializer name closed
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte, analyze]
        apply analyze_support_congr body
        intro other
        by_cases atName : other = name
        · simp only [if_pos atName]
          exact first
        · simp only [if_neg atName, extendAnalysis]
      · simp only [Code.subst, if_neg same, analyze]
        have second := analyze_substitution_support (signature := signature)
          (environment := extendAnalysis environment parameter (analyze signature environment (initializer.subst name value))) body name closed
        apply second.trans
        apply analyze_support_congr body
        intro other
        by_cases atParameter : other = parameter
        · subst other
          simp only [extendAnalysis, if_neg (Ne.symm same), ↓reduceIte]
          exact first
        · by_cases atName : other = name
          · subst other
            simp only [extendAnalysis, ↓reduceIte, if_neg atParameter]
            exact closed_value_environment_support closed
          · simp only [extendAnalysis, if_neg atParameter, if_neg atName]
termination_by sizeOf code

theorem analyze_refines_old (code : Code) (bound : ∀ name, Below (first name) (second name)) :
    Below (analyze signature first code) (ResultSummaries.analyze second code) := by
  cases code with
  | unit | boolean | integer => exact Below.refl _
  | resourceRef name => cases name <;> exact Below.refl _
  | «variable» name => exact bound name
  | pair left right => exact Below.combine (analyze_refines_old left bound) (analyze_refines_old right bound)
  | branch condition yes no => exact Below.join (analyze_refines_old yes bound) (analyze_refines_old no bound)
  | app | perform | handle | resume | discard | resource | cleanup => exact Below.unknown _
  | lambda parameter body => exact ReturnSupport.captured_monotone _ bound
  | bind parameter initializer body =>
      apply analyze_refines_old body
      intro name
      split
      · exact analyze_refines_old initializer bound
      · exact bound name
termination_by sizeOf code

def contextResult (signature : Signature) (environment : ResultSummaries.Environment) : Context → Summary → Summary
  | .pairLeft right, result => .product result (analyze signature environment right)
  | .pairRight left, result => .product (analyze signature environment left) result
  | .appFunction argument, result => .application result (analyze signature environment argument)
  | .appArgument function, result => .application (analyze signature environment function) result
  | .bind parameter suffix, result => analyze signature (extendAnalysis environment parameter result) suffix
  | .branch yes no, _ => .join (analyze signature environment yes) (analyze signature environment no)
  | .perform effect operation, _ => operationBound signature effect operation
  | .resume _, _ | .resource _ _, _ | .cleanup _, _ => .unknown

theorem context_result_plug (context : Context) (code : Code) :
    contextResult signature environment context (analyze signature environment code) =
      analyze signature environment (context.plug code) := by
  cases context <;> rfl

theorem context_result_monotone (context : Context) (bound : Below actual upper) :
    Below (contextResult signature environment context actual) (contextResult signature environment context upper) := by
  cases context with
  | pairLeft => exact Below.combine bound (Below.refl _)
  | pairRight => exact Below.combine (Below.refl _) bound
  | appFunction | appArgument | resume | resource | cleanup => exact Below.unknown _
  | branch | perform => exact Below.refl _
  | bind parameter suffix =>
      apply analyze_monotone suffix
      intro name
      unfold extendAnalysis
      split
      · exact bound
      · exact Below.refl _

theorem typed_value_below_port
    (typed : Typed signature world TypeEnv.empty ticket allowed value type)
    (isValue : value.IsValue) : Below (analyze signature environment value) (portBound type) :=
  (Below.of_support_eq (closed_value_old_support (other := environment) (typed_value_closed typed isValue))).trans
    (ContinuationBounds.typed_value_below_port typed isValue (environment := environment))

theorem resumed_value_below_input {front cap tail : Stack}
    (resolved : scope.resolve binder = some owner)
    (typed : ConfigurationTyped signature tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer cap callerScope tail)⟩ result)
    (isValue : value.IsValue) :
    Below (analyze signature environment value) (portBound (eraseType input)) := by
  obtain ⟨closed, bound⟩ := ContinuationBounds.resume_operand_bound resolved typed isValue (environment := environment)
  exact (Below.of_support_eq (closed_value_old_support closed)).trans bound

theorem bind_constructs_support_correspondence (parameter : Nat) (body : Code)
    (closed : ScopedExpressions.ClosedValue value)
    (ready : ScopedExpressions.ClosedExcept parameter body) :
    RawStep ⟨.bind parameter value body, scope, tail⟩ ⟨body.subst parameter value, scope, tail⟩ [] [] ∧
    (analyze signature environment (.bind parameter value body)).support =
      (analyze signature environment (body.subst parameter value)).support :=
  ⟨.bind parameter value body scope tail closed ready, (analyze_substitution_support body parameter closed).symm⟩

/-- This equality concerns the expression result of the actual builtin step.
    Whole-stack preservation under the new analyzer is a further obligation. -/
theorem read_constructs_result (selected : CellUpdate identity payload payload before after) :
    RawStep ⟨.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before⟩
      ⟨.integer payload, scope, after⟩ [] [] ∧
    analyze (withCellSignatures users) environment
      (.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity))) =
      analyze (withCellSignatures users) environment (.integer payload) :=
  ⟨.readCell identity payload scope before after selected, rfl⟩

theorem write_constructs_result (selected : CellUpdate identity old new before after) :
    RawStep ⟨.perform (freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before⟩
      ⟨.unit, scope, after⟩ [] [] ∧
    analyze (withCellSignatures users) environment
      (.perform (freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer new))) =
      analyze (withCellSignatures users) environment .unit :=
  ⟨.writeCell identity old new scope before after selected, rfl⟩

namespace Examples

def environment : ResultSummaries.Environment := fun _ => .unknown
def users : Signature := fun _ _ => none
def readCopiedClosure : Code := .bind 3
  (.perform (freezeEffect (.cell 7)) 0 (.resourceRef (.activation 7))) (.lambda 0 (.variable 3))

theorem copied_read_closure_has_empty_bound :
    (analyze (withCellSignatures users) environment readCopiedClosure).support = some [] ∧
    (ResultSummaries.analyze environment readCopiedClosure).support = none := ⟨rfl, rfl⟩

theorem copied_template_opening_has_empty_bound (identity : Nat) :
    (analyze (withCellSignatures users) environment
      (TemplateSupport.Examples.copiedReadClosure.instantiate (Instantiation.Environment.empty.bind 4 identity))).support = some [] := rfl

def readLater : Code := .lambda 0 (.perform (freezeEffect (.cell 7)) 0 (.resourceRef (.activation 7)))

theorem stored_read_still_retains_its_owner :
    (analyze (withCellSignatures users) environment readLater).support = some [7, 7] := rfl

theorem generic_integer_result_flows_through_bind :
    (analyze ContinuationBounds.Examples.signature environment
      (.bind 3 (.perform (freezeEffect ContinuationBounds.Examples.family) 0 .unit) (.lambda 0 (.variable 3)))).support = some [] := rfl

theorem unresolved_operation_key_is_unknown :
    operationBound (withCellSignatures users) (.cell (.bound 7)) 0 = .unknown := rfl

theorem unresolved_nested_argument_is_unknown :
    decodeEffect (.user 4 [.apply (.nominal 1) (.resource (.bound 7))]) = none := rfl

theorem callable_result_keeps_unknown_storage :
    operationBound (fun _ _ => some (.unit, .function .unit .integer []))
      (freezeEffect (.user 4 [])) 0 = .unknown := rfl

theorem known_application_remains_unknown :
    (analyze (withCellSignatures users) environment (.app (.lambda 0 (.integer 42)) .unit)).support = none := rfl

/-- Runtime dependency projection still drops bound names. This analyzer
    cannot replace template checking before resource opening. -/
theorem unopened_capture_requires_template_analysis :
    (analyze (withCellSignatures users) environment (.lambda 0 (.resourceRef (.bound 4)))).support = some [] ∧
    TemplateSupport.check environment [] (.lambda 0 (.resourceRef (.bound 4))) = false := ⟨rfl, rfl⟩

/-- Current expression typing does not constrain an arbitrary raw capture's
    annotation. Finite operation-result preservation must use signature-derived
    input annotations, as the typed capture constructor already does. -/
theorem finite_result_requires_capture_annotation_agreement :
    let before := ContinuationBounds.Examples.requesting
    let after : Configuration := ⟨.resume 9 (.integer 42), .ticket 9 5,
      .live 5 (.reference 7) ContinuationBounds.Examples.answer ContinuationBounds.Examples.saved .none .nil⟩
    RawStep before after [.ticket 5] [] ∧
    ConfigurationTyped ContinuationBounds.Examples.signature (fun _ => none) [7] before
      (eraseType ContinuationBounds.Examples.answer) ∧
    ContinuationBounds.Checked environment before.stack
      (analyze ContinuationBounds.Examples.signature environment before.expression) ∧
    ¬ ContinuationBounds.ConfigurationChecked environment after := by
  have raw : RawStep ContinuationBounds.Examples.requesting
      ⟨.resume 9 (.integer 42), .ticket 9 5,
        .live 5 (.reference 7) ContinuationBounds.Examples.answer ContinuationBounds.Examples.saved .none .nil⟩ [.ticket 5] [] :=
    .capture ContinuationBounds.Examples.family 0 5 9 5 .unit (.resume 9 (.integer 42)) .none
      ContinuationBounds.Examples.saved ContinuationBounds.Examples.saved .nil ContinuationBounds.Examples.handler
      (.reference 7) ContinuationBounds.Examples.saved_cut .hit ScopedExecution.Examples.unit_closed
      (by intro name member; simp [Code.dependencies] at member)
  refine ⟨raw, ContinuationBounds.Examples.requesting_typed, ContinuationBounds.Examples.saved_integer_bound, ?_⟩
  intro checked
  rcases checked.1.2.1 with ⟨resources, known, absent⟩ | ⟨shape, _⟩
  · have same : [7] = resources := Option.some.inj known
    subst resources
    exact absent List.mem_cons_self
  · cases shape

end Examples
end Ash.OneShot.OperationResults

#print axioms Ash.OneShot.OperationResults.decode_frozen_argument
#print axioms Ash.OneShot.OperationResults.decode_frozen_arguments
#print axioms Ash.OneShot.OperationResults.decode_frozen_effect
#print axioms Ash.OneShot.OperationResults.operation_bound_known
#print axioms Ash.OneShot.OperationResults.analyze_perform_known
#print axioms Ash.OneShot.OperationResults.captured_support_congr
#print axioms Ash.OneShot.OperationResults.analyze_support_congr
#print axioms Ash.OneShot.OperationResults.analyze_monotone
#print axioms Ash.OneShot.OperationResults.closed_value_storage_sound
#print axioms Ash.OneShot.OperationResults.closed_value_old_support
#print axioms Ash.OneShot.OperationResults.closed_value_environment_support
#print axioms Ash.OneShot.OperationResults.capture_substitution_support
#print axioms Ash.OneShot.OperationResults.analyze_substitution_support
#print axioms Ash.OneShot.OperationResults.analyze_refines_old
#print axioms Ash.OneShot.OperationResults.context_result_plug
#print axioms Ash.OneShot.OperationResults.context_result_monotone
#print axioms Ash.OneShot.OperationResults.typed_value_below_port
#print axioms Ash.OneShot.OperationResults.resumed_value_below_input
#print axioms Ash.OneShot.OperationResults.bind_constructs_support_correspondence
#print axioms Ash.OneShot.OperationResults.read_constructs_result
#print axioms Ash.OneShot.OperationResults.write_constructs_result
#print axioms Ash.OneShot.OperationResults.Examples.copied_read_closure_has_empty_bound
#print axioms Ash.OneShot.OperationResults.Examples.copied_template_opening_has_empty_bound
#print axioms Ash.OneShot.OperationResults.Examples.stored_read_still_retains_its_owner
#print axioms Ash.OneShot.OperationResults.Examples.generic_integer_result_flows_through_bind
#print axioms Ash.OneShot.OperationResults.Examples.unresolved_operation_key_is_unknown
#print axioms Ash.OneShot.OperationResults.Examples.unresolved_nested_argument_is_unknown
#print axioms Ash.OneShot.OperationResults.Examples.callable_result_keeps_unknown_storage
#print axioms Ash.OneShot.OperationResults.Examples.known_application_remains_unknown
#print axioms Ash.OneShot.OperationResults.Examples.unopened_capture_requires_template_analysis
#print axioms Ash.OneShot.OperationResults.Examples.finite_result_requires_capture_annotation_agreement
