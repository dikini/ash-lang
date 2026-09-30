import CoreValueRelation

/-! Concrete strict-redex correspondence components for TASK-0032.
Each witness records an actual Core next equation, one positive ordinary
ScopedExecution.RawStep and the actual successor's lexical value relation.
Core and target tails are arbitrary explicit parameters and remain unchanged.
These components do not assert that those tails, scopes, whole frames or whole
configurations are related. Static translation and current operand/lexical
relations are inputs; future successor validity and calculus execution are not.
No discard transition is used, including the older eager-discard rule. -/
namespace Ash.OneShot.CoreStrictSteps
open ScopedExpressions ScopedExecution CoreValueRelation

/-- The completed Core application enters its closure's saved environment.
    The calculus beta step enters the substituted closed body in scope none. -/
def ApplicationWitness (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (base : CoreMachine.State) (parameter body : Nat) (saved : MEnv)
    (value : MValue) (argumentCode result : Code) (coreTail : List CoreMachine.Frame)
    (scope : Scope) (targetTail : Stack) : Prop :=
  ∃ fuel rawBody,
    CoreTranslation.translateFuel graph fuel [] body = .ok rawBody ∧
    CoreMachine.next graph { base with control := .returned value, frames := .applyArgument (.closure parameter body saved) :: coreTail } =
      .stepped { base with control := .evaluate body (.binding parameter value saved), frames := coreTail } ∧
    RawStep ⟨.app (.lambda parameter result) argumentCode, scope, targetTail⟩
      ⟨result.subst parameter argumentCode, .none, targetTail⟩ [] [] ∧
    EnvCloses graph [] base.heap (.binding parameter value saved)
      rawBody (result.subst parameter argumentCode) ∧
    ValueRel graph owners base.heap value argumentCode

theorem application_complete {base : CoreMachine.State}
    (function : ValueRel graph owners base.heap (.closure parameter body saved) (.lambda parameter result))
    (argument : ValueRel graph owners base.heap value argumentCode)
    (coreTail : List CoreMachine.Frame) (scope : Scope) (targetTail : Stack) :
    ApplicationWitness graph owners base parameter body saved value argumentCode result coreTail scope targetTail := by
  obtain ⟨fuel, rawBody, translated, environment, closed⟩ := function.closure_view
  exact ⟨fuel, rawBody, translated, rfl,
    .beta parameter result argumentCode scope targetTail argument.closed closed,
    environment.beta_argument (argument.owner_transport []), argument⟩

/-- Bind readiness is a property of the current closed suffix, not a premise
    about the successor. Its source derivation remains a static obligation. -/
theorem bind_complete {base : CoreMachine.State}
    (translated : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (environment : EnvCloses graph owners base.heap saved (.lambda parameter rawBody) (.lambda parameter suffix))
    (argument : ValueRel graph owners base.heap value argumentCode)
    (ready : ClosedExcept parameter suffix)
    (coreTail : List CoreMachine.Frame) (scope : Scope) (targetTail : Stack) :
    CoreMachine.next graph { base with control := .returned value, frames := .bind parameter body saved :: coreTail } =
      .stepped { base with control := .evaluate body (.binding parameter value saved), frames := coreTail } ∧
    RawStep ⟨.bind parameter argumentCode suffix, scope, targetTail⟩
      ⟨suffix.subst parameter argumentCode, scope, targetTail⟩ [] [] ∧
    EnvCloses graph owners base.heap (.binding parameter value saved)
      rawBody (suffix.subst parameter argumentCode) ∧
    CoreTranslation.translateFuel graph fuel owners body = .ok rawBody :=
  ⟨rfl, .bind parameter argumentCode suffix scope targetTail argument.closed ready,
    environment.beta_argument argument, translated⟩

/-- The source fragment permits both exact exhaustive Boolean arm orders. -/
def booleanArms (yes no : CoreSyntax.NodeRef) (reversed : Bool) : List CoreSyntax.MatchArm :=
  if reversed then [⟨.boolean false, no⟩, ⟨.boolean true, yes⟩]
  else [⟨.boolean true, yes⟩, ⟨.boolean false, no⟩]

theorem select_boolean (condition reversed : Bool) (yes no : CoreSyntax.NodeRef) :
    CoreMachine.selectArm (booleanArms yes no reversed) (.boolean condition) =
      .ok (if condition then yes else no) := by
  cases condition <;> cases reversed <;> rfl

/-- Branch selection preserves the saved environment and chooses the same
    translated arm. Neither operand rows nor arm order chooses the result. -/
theorem branch_complete {base : CoreMachine.State}
    (yesTranslated : CoreTranslation.translateFuel graph fuel owners yes = .ok rawYes)
    (noTranslated : CoreTranslation.translateFuel graph fuel owners no = .ok rawNo)
    (yesEnvironment : EnvCloses graph owners base.heap saved rawYes yesCode)
    (noEnvironment : EnvCloses graph owners base.heap saved rawNo noCode)
    (condition reversed : Bool) (coreTail : List CoreMachine.Frame) (scope : Scope) (targetTail : Stack) :
    CoreMachine.next graph { base with control := .returned (.boolean condition), frames := .matchCases (booleanArms yes no reversed) saved :: coreTail } =
      .stepped { base with control := .evaluate (if condition then yes else no) saved, frames := coreTail } ∧
    RawStep ⟨.branch (.boolean condition) yesCode noCode, scope, targetTail⟩
      ⟨(if condition then yesCode else noCode), scope, targetTail⟩ [] [] ∧
    EnvCloses graph owners base.heap saved (if condition then rawYes else rawNo)
      (if condition then yesCode else noCode) ∧
    CoreTranslation.translateFuel graph fuel owners (if condition then yes else no) =
      .ok (if condition then rawYes else rawNo) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [CoreMachine.next, select_boolean]
  · cases condition
    · exact .ifFalse yesCode noCode scope targetTail
    · exact .ifTrue yesCode noCode scope targetTail
  · cases condition
    · exact noEnvironment
    · exact yesEnvironment
  · cases condition
    · exact noTranslated
    · exact yesTranslated

namespace Examples
open CoreMachineExamples

private def base : CoreMachine.State := { control := .returned .unit }

/-- This uses the existing lexical graph and closes the actual Core successor
    under its captured 17, regardless of a caller's possible binding to 99. -/
theorem lexical_application (coreTail : List CoreMachine.Frame) (scope : Scope) (targetTail : Stack) :
    ApplicationWitness lexicalClosure [] base 2 1 (.binding 1 (.integer 17) .empty)
      .unit .unit (.integer 17) coreTail scope targetTail :=
  application_complete CoreValueRelation.Examples.lexical_closure .unit coreTail scope targetTail

/-- The main template lookup produces a self-inclusive finite saved suffix;
    completed application erases only the proved unused self binding. -/
theorem main_application (coreTail : List CoreMachine.Frame) (scope : Scope) (targetTail : Stack) :
    ApplicationWitness entryWrapper [] base 8 0 (.functionTemplate 5 8 0 .empty)
      .unit .unit (.integer 17) coreTail scope targetTail :=
  application_complete CoreValueRelation.Examples.main_lookup_value .unit coreTail scope targetTail

/-- A same-name old parameter binding cannot override the supplied argument. -/
theorem parameter_beta : EnvCloses lexicalClosure [] []
    (.binding 1 (.integer 11) (.binding 1 (.integer 99) .empty)) (.variable 1) (.integer 11) := by
  have previous : EnvCloses lexicalClosure [] [] (.binding 1 (.integer 99) .empty)
      (.lambda 1 (.variable 1)) (.lambda 1 (.variable 1)) :=
    CoreValueRelation.Examples.parameter_shadow
  simpa [Code.subst] using previous.beta_argument (ValueRel.integer (value := 11))

/-- The inserted argument retains activation 7 under a same-static resource
    binder whose captured environment resolves to activation 11. -/
theorem resource_beta : EnvCloses cellGraph [] []
    (.binding 4 (.handle 7) (.resource 3 11 .empty)) (.variable 4) (.resourceRef (.activation 7)) := by
  have previous : EnvCloses cellGraph [] [] (.resource 3 11 .empty)
      (.lambda 4 (.variable 4)) (.lambda 4 (.variable 4)) := .resource .empty
  simpa [Code.subst] using previous.beta_argument (ValueRel.handle (key := 7))

/-- Ordinary bind completion returns the current 99 through both models. -/
theorem bind_shadow (coreTail : List CoreMachine.Frame) (scope : Scope) (targetTail : Stack) :
    CoreMachine.next lexicalClosure { base with control := .returned (.integer 99), frames := .bind 1 1 (.binding 1 (.integer 17) .empty) :: coreTail } =
      .stepped { base with control := .evaluate 1 (.binding 1 (.integer 99) (.binding 1 (.integer 17) .empty)), frames := coreTail } ∧
    RawStep ⟨.bind 1 (.integer 99) (.variable 1), scope, targetTail⟩
      ⟨.integer 99, scope, targetTail⟩ [] [] ∧
    EnvCloses lexicalClosure [] []
      (.binding 1 (.integer 99) (.binding 1 (.integer 17) .empty)) (.variable 1) (.integer 99) := by
  have environment : EnvCloses lexicalClosure [] [] (.binding 1 (.integer 17) .empty)
      (.lambda 1 (.variable 1)) (.lambda 1 (.variable 1)) :=
    EnvCloses.parameter_shadow .integer .empty
  have completed := bind_complete (base := base) (graph := lexicalClosure) (owners := [])
    (fuel := 1) (body := 1) (rawBody := .variable 1) rfl environment
    (ValueRel.integer (value := 99)) (by intro name member; simpa [Code.dependencies] using member)
    coreTail scope targetTail
  exact ⟨completed.1, by simpa [Code.subst] using completed.2.1,
    by simpa [Code.subst, base] using completed.2.2.1⟩

/-- Both source arm orders select 7 for the existing false Boolean graph. -/
theorem branch_false (reversed : Bool) (coreTail : List CoreMachine.Frame)
    (scope : Scope) (targetTail : Stack) :
    CoreMachine.next boolGraph { base with control := .returned (.boolean false), frames := .matchCases (booleanArms 1 2 reversed) .empty :: coreTail } =
      .stepped { base with control := .evaluate 2 .empty, frames := coreTail } ∧
    RawStep ⟨.branch (.boolean false) (.integer 11) (.integer 7), scope, targetTail⟩
      ⟨.integer 7, scope, targetTail⟩ [] [] ∧
    EnvCloses boolGraph [] [] .empty (.integer 7) (.integer 7) := by
  have completed := branch_complete (base := base) (graph := boolGraph) (owners := [])
    (fuel := 1) (yes := 1) (no := 2) (rawYes := .integer 11) (rawNo := .integer 7)
    rfl rfl EnvCloses.empty EnvCloses.empty false reversed coreTail scope targetTail
  exact ⟨completed.1, completed.2.1, completed.2.2.1⟩

end Examples

#print axioms application_complete
#print axioms bind_complete
#print axioms branch_complete
#print axioms Examples.lexical_application
#print axioms Examples.main_application
#print axioms Examples.parameter_beta
#print axioms Examples.resource_beta
#print axioms Examples.bind_shadow
#print axioms Examples.branch_false

end Ash.OneShot.CoreStrictSteps
