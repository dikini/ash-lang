import Instantiation

/-!
Binding-aware lexical instantiation of the one-shot expression grammar.
This is a scoped representation of code, not another computation calculus.
Resource declarations remain templates until acquired. Existing activation
atoms are internal metadata and never bind source names. Evaluation and the
relation to the administrative expression machine remain separate obligations.
-/

namespace Ash.OneShot.Instantiation

def Environment.mask (environment : Environment) (binder : Nat) : Environment :=
  fun name => if name = binder then none else environment name

def ResourceName.instantiate (environment : Environment) : ResourceName → ResourceName
  | .bound name => match environment name with
    | some key => .activation key
    | none => .bound name
  | .activation key => .activation key

def ResourceName.freeNames : ResourceName → List Nat
  | .bound name => [name]
  | .activation _ => []

def Argument.instantiate (environment : Environment) : Argument → Argument
  | .nominal identity => .nominal identity
  | .resource name => .resource (name.instantiate environment)
  | .apply head argument => .apply (head.instantiate environment) (argument.instantiate environment)

def Argument.freeNames : Argument → List Nat
  | .nominal _ => []
  | .resource name => name.freeNames
  | .apply head argument => head.freeNames ++ argument.freeNames

def Effect.instantiate (environment : Environment) : Effect → Effect
  | .user family arguments => .user family (arguments.map (Argument.instantiate environment))
  | .cell name => .cell (name.instantiate environment)

def Effect.freeNames : Effect → List Nat
  | .user _ arguments => arguments.flatMap Argument.freeNames
  | .cell name => name.freeNames

end Ash.OneShot.Instantiation

namespace Ash.OneShot.ScopedExpressions
open Instantiation

mutual
inductive Code where
  | unit
  | boolean : Bool → Code
  | integer : Int → Code
  | variable : Nat → Code
  | resourceRef : ResourceName → Code
  | pair : Code → Code → Code
  | lambda : Nat → Code → Code
  | app : Code → Code → Code
  | bind : Nat → Code → Code → Code
  | branch : Code → Code → Code → Code
  | perform : Effect → Nat → Code → Code
  | handle : Effect → Code → Clauses → Code
  | resume : Nat → Code → Code
  | discard : Nat → Code
  | resource : Nat → Code → Code → Code
  | cleanup : Code → Code → Code
  deriving Repr

inductive Clauses where
  | nil
  | cons : Nat → Nat → Nat → Code → Clauses → Clauses
  deriving Repr
end

mutual
def Code.instantiate (environment : Environment) : Code → Code
  | .unit => .unit
  | .boolean value => .boolean value
  | .integer value => .integer value
  | .variable name => .variable name
  | .resourceRef name => .resourceRef (name.instantiate environment)
  | .pair left right => .pair (left.instantiate environment) (right.instantiate environment)
  | .lambda parameter body => .lambda parameter (body.instantiate environment)
  | .app function argument => .app (function.instantiate environment) (argument.instantiate environment)
  | .bind parameter initializer body =>
      .bind parameter (initializer.instantiate environment) (body.instantiate environment)
  | .branch condition yes no =>
      .branch (condition.instantiate environment) (yes.instantiate environment) (no.instantiate environment)
  | .perform effect operation operand => .perform (effect.instantiate environment) operation (operand.instantiate environment)
  | .handle effect body clauses =>
      .handle (effect.instantiate environment) (body.instantiate environment) (clauses.instantiate environment)
  | .resume ticket operand => .resume ticket (operand.instantiate environment)
  | .discard ticket => .discard ticket
  | .resource binder initializer body =>
      .resource binder (initializer.instantiate environment) (body.instantiate (environment.mask binder))
  | .cleanup action body => .cleanup (action.instantiate environment) (body.instantiate environment)

def Clauses.instantiate (environment : Environment) : Clauses → Clauses
  | .nil => .nil
  | .cons operation parameter ticket body rest =>
      .cons operation parameter ticket (body.instantiate environment) (rest.instantiate environment)
end

mutual
def Code.freeNames : Code → List Nat
  | .unit | .boolean _ | .integer _ | .variable _ | .discard _ => []
  | .resourceRef name => name.freeNames
  | .pair left right | .app left right | .bind _ left right | .cleanup left right =>
      left.freeNames ++ right.freeNames
  | .lambda _ body | .resume _ body => body.freeNames
  | .branch condition yes no => condition.freeNames ++ yes.freeNames ++ no.freeNames
  | .perform effect _ operand => effect.freeNames ++ operand.freeNames
  | .handle effect body clauses => effect.freeNames ++ body.freeNames ++ clauses.freeNames
  | .resource binder initializer body => initializer.freeNames ++ body.freeNames.filter (· != binder)

def Clauses.freeNames : Clauses → List Nat
  | .nil => []
  | .cons _ _ _ body rest => body.freeNames ++ rest.freeNames
end

def unresolved (environment : Environment) (names : List Nat) : List Nat :=
  names.filter (fun name => (environment name).isNone)

theorem unresolved_append (environment : Environment) (left right : List Nat) :
    unresolved environment (left ++ right) = unresolved environment left ++ unresolved environment right := by
  simp [unresolved]

theorem name_instantiation_free (environment : Environment) (name : ResourceName) :
    (name.instantiate environment).freeNames = unresolved environment name.freeNames := by
  cases name with
  | activation => rfl
  | bound name => cases known : environment name <;> simp [ResourceName.instantiate, ResourceName.freeNames, unresolved, known]

theorem argument_instantiation_free (environment : Environment) (argument : Argument) :
    (argument.instantiate environment).freeNames = unresolved environment argument.freeNames := by
  induction argument with
  | nominal => rfl
  | resource name => exact name_instantiation_free environment name
  | apply head argument ihHead ihArgument =>
      simp only [Argument.instantiate, Argument.freeNames, ihHead, ihArgument, unresolved_append]

theorem effect_instantiation_free (environment : Environment) (effect : Effect) :
    (effect.instantiate environment).freeNames = unresolved environment effect.freeNames := by
  cases effect with
  | cell name => exact name_instantiation_free environment name
  | user family arguments =>
      change (arguments.map (Argument.instantiate environment)).flatMap Argument.freeNames =
        unresolved environment (arguments.flatMap Argument.freeNames)
      induction arguments with
      | nil => rfl
      | cons argument rest ih =>
          simp only [List.map_cons, List.flatMap_cons, argument_instantiation_free, ih, unresolved_append]

theorem masked_unresolved (environment : Environment) (binder : Nat) (names : List Nat) :
    (unresolved (environment.mask binder) names).filter (· != binder) =
      unresolved environment (names.filter (· != binder)) := by
  simp only [unresolved, List.filter_filter]
  congr 1
  funext name
  by_cases same : name = binder
  · simp [Environment.mask, same]
  · simp [Environment.mask, same, Bool.and_comm]

mutual
/-- Exact free-name accounting, including resource declaration shadowing. -/
theorem Code.instantiation_free (code : Code) (environment : Environment) :
    (code.instantiate environment).freeNames = unresolved environment code.freeNames := by
  cases code with
  | unit | boolean _ | integer _ | «variable» _ | discard _ => rfl
  | resourceRef name => exact name_instantiation_free environment name
  | pair left right | app left right | bind _ left right | cleanup left right =>
      simp only [Code.instantiate, Code.freeNames, left.instantiation_free, right.instantiation_free, unresolved_append]
  | lambda _ body | resume _ body => exact body.instantiation_free environment
  | branch condition yes no =>
      simp only [Code.instantiate, Code.freeNames, condition.instantiation_free, yes.instantiation_free,
        no.instantiation_free, unresolved_append]
  | perform effect operation operand =>
      simp only [Code.instantiate, Code.freeNames, effect_instantiation_free, operand.instantiation_free, unresolved_append]
  | handle effect body clauses =>
      simp only [Code.instantiate, Code.freeNames, effect_instantiation_free, body.instantiation_free,
        clauses.instantiation_free, unresolved_append]
  | resource binder initializer body =>
      simp only [Code.instantiate, Code.freeNames, initializer.instantiation_free, body.instantiation_free,
        masked_unresolved, unresolved_append]

theorem Clauses.instantiation_free (clauses : Clauses) (environment : Environment) :
    (clauses.instantiate environment).freeNames = unresolved environment clauses.freeNames := by
  cases clauses with
  | nil => rfl
  | cons operation parameter ticket body rest =>
      simp only [Clauses.instantiate, Clauses.freeNames, body.instantiation_free, rest.instantiation_free, unresolved_append]
end

def Missing (environment : Environment) (names : List Nat) : Prop :=
  ∀ name, name ∈ names → environment name = none

theorem missing_append (checked : Missing environment (left ++ right)) :
    Missing environment left ∧ Missing environment right :=
  ⟨fun name member => checked name (List.mem_append_left _ member),
   fun name member => checked name (List.mem_append_right _ member)⟩

theorem missing_mask (checked : Missing environment (names.filter (· != binder))) :
    Missing (Environment.mask environment binder) names := by
  intro name member
  by_cases same : name = binder
  · simp [Environment.mask, same]
  · simp only [Environment.mask, if_neg same]
    exact checked name (by simp [member, same])

theorem name_instantiation_identity (name : ResourceName) (environment : Environment)
    (missing : Missing environment name.freeNames) : name.instantiate environment = name := by
  cases name with
  | activation => rfl
  | bound name => simp [ResourceName.instantiate, missing name List.mem_cons_self]

theorem argument_instantiation_identity (argument : Argument) (environment : Environment)
    (missing : Missing environment argument.freeNames) : argument.instantiate environment = argument := by
  induction argument with
  | nominal => rfl
  | resource name => exact congrArg Argument.resource (name_instantiation_identity name environment missing)
  | apply head argument ihHead ihArgument =>
      obtain ⟨left, right⟩ := missing_append missing
      simp only [Argument.instantiate, ihHead left, ihArgument right]

theorem effect_instantiation_identity (effect : Effect) (environment : Environment)
    (missing : Missing environment effect.freeNames) : effect.instantiate environment = effect := by
  cases effect with
  | cell name => exact congrArg Effect.cell (name_instantiation_identity name environment missing)
  | user family arguments =>
      apply congrArg (Effect.user family)
      induction arguments with
      | nil => rfl
      | cons argument rest ih =>
          obtain ⟨headMissing, restMissing⟩ := missing_append missing
          simp only [List.map_cons, argument_instantiation_identity argument environment headMissing, ih restMissing]

mutual
theorem Code.instantiation_identity (code : Code) (environment : Environment)
    (missing : Missing environment code.freeNames) : code.instantiate environment = code := by
  cases code with
  | unit | boolean _ | integer _ | «variable» _ | discard _ => rfl
  | resourceRef name => exact congrArg Code.resourceRef (name_instantiation_identity name environment missing)
  | pair left right | app left right | bind _ left right | cleanup left right =>
      obtain ⟨leftMissing, rightMissing⟩ := missing_append missing
      simp only [Code.instantiate, left.instantiation_identity environment leftMissing,
        right.instantiation_identity environment rightMissing]
  | lambda _ body | resume _ body =>
      simp only [Code.instantiate, body.instantiation_identity environment missing]
  | branch condition yes no =>
      obtain ⟨firstMissing, noMissing⟩ := missing_append missing
      obtain ⟨conditionMissing, yesMissing⟩ := missing_append firstMissing
      simp only [Code.instantiate, condition.instantiation_identity environment conditionMissing,
        yes.instantiation_identity environment yesMissing, no.instantiation_identity environment noMissing]
  | perform effect operation operand =>
      obtain ⟨effectMissing, operandMissing⟩ := missing_append missing
      simp only [Code.instantiate, effect_instantiation_identity effect environment effectMissing,
        operand.instantiation_identity environment operandMissing]
  | handle effect body clauses =>
      obtain ⟨firstMissing, clausesMissing⟩ := missing_append missing
      obtain ⟨effectMissing, bodyMissing⟩ := missing_append firstMissing
      simp only [Code.instantiate, effect_instantiation_identity effect environment effectMissing,
        body.instantiation_identity environment bodyMissing, clauses.instantiation_identity environment clausesMissing]
  | resource binder initializer body =>
      obtain ⟨initializerMissing, bodyMissing⟩ := missing_append missing
      simp only [Code.instantiate, initializer.instantiation_identity environment initializerMissing,
        body.instantiation_identity (environment.mask binder) (missing_mask bodyMissing)]

theorem Clauses.instantiation_identity (clauses : Clauses) (environment : Environment)
    (missing : Missing environment clauses.freeNames) : clauses.instantiate environment = clauses := by
  cases clauses with
  | nil => rfl
  | cons operation parameter ticket body rest =>
      obtain ⟨bodyMissing, restMissing⟩ := missing_append missing
      simp only [Clauses.instantiate, body.instantiation_identity environment bodyMissing,
        rest.instantiation_identity environment restMissing]
end

def Covered (environment : Environment) (names : List Nat) : Prop :=
  ∀ name, name ∈ names → ∃ activation, environment name = some activation

theorem unresolved_empty_iff (environment : Environment) (names : List Nat) :
    unresolved environment names = [] ↔ Covered environment names := by
  constructor
  · intro closed name member
    cases known : environment name with
    | some activation => exact ⟨activation, rfl⟩
    | none =>
        have present : name ∈ unresolved environment names := by simp [unresolved, member, known]
        rw [closed] at present
        cases present
  · intro covered
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name present
    obtain ⟨member, absent⟩ := List.mem_filter.mp present
    obtain ⟨activation, known⟩ := covered name member
    simp [known] at absent

/-- Resource-closed code may still contain locally bound acquisition templates. -/
def Code.ResourceClosed (code : Code) : Prop := code.freeNames = []

theorem Code.instantiation_closes_iff (code : Code) (environment : Environment) :
    (code.instantiate environment).ResourceClosed ↔ Covered environment code.freeNames := by
  rw [Code.ResourceClosed, code.instantiation_free]
  exact unresolved_empty_iff environment code.freeNames

theorem Code.closed_instantiation_identity (code : Code) (environment : Environment)
    (closed : code.ResourceClosed) : code.instantiate environment = code :=
  code.instantiation_identity environment (fun _ member => False.elim (by rw [closed] at member; cases member))

mutual
def Code.subst (code : Code) (name : Nat) (value : Code) : Code := match code with
  | .unit => .unit
  | .boolean value => .boolean value
  | .integer value => .integer value
  | .variable other => if name = other then value else .variable other
  | .resourceRef resource => .resourceRef resource
  | .pair left right => .pair (left.subst name value) (right.subst name value)
  | .lambda parameter body => .lambda parameter (if name = parameter then body else body.subst name value)
  | .app function argument => .app (function.subst name value) (argument.subst name value)
  | .bind parameter initializer body =>
      .bind parameter (initializer.subst name value) (if name = parameter then body else body.subst name value)
  | .branch condition yes no => .branch (condition.subst name value) (yes.subst name value) (no.subst name value)
  | .perform effect operation operand => .perform effect operation (operand.subst name value)
  | .handle effect body clauses => .handle effect (body.subst name value) (clauses.subst name value)
  | .resume ticket operand => .resume ticket (operand.subst name value)
  | .discard ticket => .discard ticket
  | .resource binder initializer body => .resource binder (initializer.subst name value) (body.subst name value)
  | .cleanup action body => .cleanup (action.subst name value) (body.subst name value)

def Clauses.subst (clauses : Clauses) (name : Nat) (value : Code) : Clauses := match clauses with
  | .nil => .nil
  | .cons operation parameter ticket body rest =>
      .cons operation parameter ticket (if name = parameter then body else body.subst name value) (rest.subst name value)
end

mutual
/-- Inserting previously resource-closed code cannot subject its activations
    to a new lexical instantiation, including beneath same-name resource sites.
    This is a commutation law, not a typing or ordinary-variable hygiene rule. -/
theorem Code.instantiation_subst (code : Code) (name : Nat) (value : Code) (environment : Environment)
    (closed : value.ResourceClosed) :
    (code.subst name value).instantiate environment = (code.instantiate environment).subst name value := by
  cases code with
  | unit | boolean _ | integer _ | resourceRef _ | discard _ => rfl
  | «variable» other =>
      by_cases same : name = other
      · simp only [Code.subst, if_pos same, value.closed_instantiation_identity environment closed, Code.instantiate]
      · simp only [Code.subst, if_neg same, Code.instantiate]
  | pair left right | app left right | cleanup left right =>
      simp only [Code.subst, Code.instantiate, left.instantiation_subst name value environment closed,
        right.instantiation_subst name value environment closed]
  | lambda parameter body =>
      by_cases same : name = parameter
      · simp only [Code.subst, Code.instantiate, if_pos same]
      · simp only [Code.subst, Code.instantiate, if_neg same, body.instantiation_subst name value environment closed]
  | bind parameter initializer body =>
      by_cases same : name = parameter
      · simp only [Code.subst, Code.instantiate, if_pos same, initializer.instantiation_subst name value environment closed]
      · simp only [Code.subst, Code.instantiate, if_neg same, initializer.instantiation_subst name value environment closed,
          body.instantiation_subst name value environment closed]
  | branch condition yes no =>
      simp only [Code.subst, Code.instantiate, condition.instantiation_subst name value environment closed,
        yes.instantiation_subst name value environment closed, no.instantiation_subst name value environment closed]
  | perform effect operation operand | resume operation operand =>
      simp only [Code.subst, Code.instantiate, operand.instantiation_subst name value environment closed]
  | handle effect body clauses =>
      simp only [Code.subst, Code.instantiate, body.instantiation_subst name value environment closed,
        clauses.instantiation_subst name value environment closed]
  | resource binder initializer body =>
      simp only [Code.subst, Code.instantiate, initializer.instantiation_subst name value environment closed,
        body.instantiation_subst name value (environment.mask binder) closed]

theorem Clauses.instantiation_subst (clauses : Clauses) (name : Nat) (value : Code) (environment : Environment)
    (closed : value.ResourceClosed) :
    (clauses.subst name value).instantiate environment = (clauses.instantiate environment).subst name value := by
  cases clauses with
  | nil => rfl
  | cons operation parameter ticket body rest =>
      by_cases same : name = parameter
      · simp only [Clauses.subst, Clauses.instantiate, if_pos same, rest.instantiation_subst name value environment closed]
      · simp only [Clauses.subst, Clauses.instantiate, if_neg same, body.instantiation_subst name value environment closed,
          rest.instantiation_subst name value environment closed]
end

/-- Acquisition instantiates the body, not its enclosing declaration (which
    would mask the new binding again). The already-closed declaration permits
    no unresolved external resource names in that body. -/
theorem acquisition_closes_body (environment : Environment) (prepared : PreparedActivation issued)
    (closed : (Code.resource binder initializer body).ResourceClosed) :
    (body.instantiate (prepared.bodyEnvironment environment binder)).ResourceClosed := by
  apply (body.instantiation_closes_iff _).mpr
  intro name member
  by_cases same : name = binder
  · exact ⟨prepared.identity, by simp [PreparedActivation.bodyEnvironment, Environment.bind, same]⟩
  · have present : name ∈ (Code.resource binder initializer body).freeNames := by
      simp only [Code.freeNames, List.mem_append, List.mem_filter]
      exact Or.inr ⟨member, by simp [same]⟩
    rw [closed] at present
    cases present

theorem name_instantiation_realizes (checked : NameRealizes environment source target) :
    source.instantiate environment = ResourceName.activation target := by
  cases checked with
  | activation => rfl
  | bound known => simp [ResourceName.instantiate, known]

theorem argument_instantiation_realizes (checked : ArgumentRealizes environment source target) :
    source.instantiate environment = freezeArgument target := by
  induction checked with
  | nominal => rfl
  | resource name => exact congrArg Argument.resource (name_instantiation_realizes name)
  | apply head argument ihHead ihArgument => simp only [Argument.instantiate, freezeArgument, ihHead, ihArgument]

/-- The executable metadata traversal agrees with the preceding structural
    realization judgment whenever its lexical lookup checks hold. -/
theorem effect_instantiation_realizes (checked : EffectRealizes environment source target) :
    source.instantiate environment = freezeEffect target := by
  cases checked with
  | cell name => exact congrArg Effect.cell (name_instantiation_realizes name)
  | user arguments =>
      apply congrArg (Effect.user _)
      induction arguments with
      | nil => rfl
      | cons head rest ih => simp only [List.map_cons, argument_instantiation_realizes head, ih]

namespace Examples

def request : Effect := .user 9 [.resource (.bound 4)]
def outerRequest : Effect := .user 9 [.resource (.activation 0)]
def innerRequest : Effect := .user 9 [.resource (.activation 1)]
def outer : Environment := Environment.empty.bind 4 0
def inner : Environment := Environment.empty.bind 4 1

/-- Shadowing starts in the body; the initializer still sees the outer name. -/
theorem nested_same_name_initializer :
    (Code.resource 4 (.perform request 0 .unit) (.perform request 0 .unit)).instantiate outer =
      .resource 4 (.perform outerRequest 0 .unit) (.perform request 0 .unit) := rfl

def sourceClosure : Code := .lambda 7 (.pair (.perform request 0 .unit)
  (.resource 4 (.integer 1) (.perform request 0 .unit)))
def oldClosure : Code := sourceClosure.instantiate outer

theorem closure_keeps_outer_and_defers_inner :
    oldClosure = .lambda 7 (.pair (.perform outerRequest 0 .unit)
      (.resource 4 (.integer 1) (.perform request 0 .unit))) := rfl

theorem old_closure_resource_closed : oldClosure.ResourceClosed := rfl

theorem old_closure_cannot_be_rebound : oldClosure.instantiate inner = oldClosure :=
  oldClosure.closed_instantiation_identity inner old_closure_resource_closed

/-- A fully closed lambda can still contain a resource site to be acquired on
    each invocation. Closing the lambda must not allocate that local site. -/
theorem local_acquisition_stays_deferred :
    (Code.lambda 7 (.resource 4 (.integer 0) (.perform request 0 .unit))).ResourceClosed ∧
    (Code.lambda 7 (.resource 4 (.integer 0) (.perform request 0 .unit))).instantiate outer =
      .lambda 7 (.resource 4 (.integer 0) (.perform request 0 .unit)) := ⟨rfl, rfl⟩

theorem inserted_old_closure_is_stable :
    ((Code.resource 4 (.integer 1) (.app (.variable 0) .unit)).subst 0 oldClosure).instantiate inner =
      .resource 4 (.integer 1) (.app oldClosure .unit) := by
  rw [Code.instantiation_subst _ 0 oldClosure inner old_closure_resource_closed]
  rfl

def prepared : PreparedActivation [.resource 0] := prepareActivation [.resource 0]
def acquisitionBody : Code := .pair (.perform request 0 .unit) (.app oldClosure .unit)

theorem acquired_body_selects_new_and_keeps_old :
    acquisitionBody.instantiate (prepared.bodyEnvironment outer 4) =
      .pair (.perform innerRequest 0 .unit) (.app oldClosure .unit) := by
  change Code.pair (.perform innerRequest 0 .unit)
    (.app (oldClosure.instantiate (prepared.bodyEnvironment outer 4)) .unit) = _
  rw [oldClosure.closed_instantiation_identity _ old_closure_resource_closed]

theorem acquired_body_is_closed :
    (acquisitionBody.instantiate (prepared.bodyEnvironment outer 4)).ResourceClosed :=
  acquisition_closes_body outer prepared (show (Code.resource 4 (.integer 1) acquisitionBody).ResourceClosed from rfl)

end Examples

end Ash.OneShot.ScopedExpressions

#print axioms Ash.OneShot.ScopedExpressions.Code.instantiation_free
#print axioms Ash.OneShot.ScopedExpressions.Code.instantiation_closes_iff
#print axioms Ash.OneShot.ScopedExpressions.Code.closed_instantiation_identity
#print axioms Ash.OneShot.ScopedExpressions.Code.instantiation_subst
#print axioms Ash.OneShot.ScopedExpressions.acquisition_closes_body
#print axioms Ash.OneShot.ScopedExpressions.effect_instantiation_realizes
#print axioms Ash.OneShot.ScopedExpressions.Examples.nested_same_name_initializer
#print axioms Ash.OneShot.ScopedExpressions.Examples.old_closure_cannot_be_rebound
#print axioms Ash.OneShot.ScopedExpressions.Examples.inserted_old_closure_is_stable
#print axioms Ash.OneShot.ScopedExpressions.Examples.acquired_body_selects_new_and_keeps_old
#print axioms Ash.OneShot.ScopedExpressions.Examples.acquired_body_is_closed
