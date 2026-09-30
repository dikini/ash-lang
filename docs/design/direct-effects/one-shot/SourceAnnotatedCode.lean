import SourceFocusAnnotationGap

/-! Finite source nodes retain lexical type hints across ordinary substitution
and resource instantiation. Erasure is the existing scoped code, with its one
sequencing form and unchanged handler/resource syntax. This metadata layer is
not by itself a typing or ownership judgment. -/
namespace Ash.OneShot.SourceAnnotatedCode
open Instantiation

mutual
inductive Term where
  | unit (hint : ValueType)
  | boolean (hint : ValueType) (value : Bool)
  | integer (hint : ValueType) (value : Int)
  | variable (hint : ValueType) (name : Nat)
  | resourceRef (hint : ValueType) (name : ResourceName)
  | pair (hint : ValueType) (left right : Term)
  | lambda (hint : ValueType) (parameter : Nat) (body : Term)
  | app (hint : ValueType) (function argument : Term)
  | bind (hint : ValueType) (parameter : Nat) (initializer body : Term)
  | branch (hint : ValueType) (condition yes no : Term)
  | perform (hint : ValueType) (effect : Effect) (operation : Nat) (operand : Term)
  | handle (hint : ValueType) (effect : Effect) (body : Term) (clauses : Clauses)
  | resume (hint : ValueType) (binder : Nat) (operand : Term)
  | discard (hint : ValueType) (binder : Nat)
  | resource (hint : ValueType) (binder : Nat) (initializer body : Term)
  | cleanup (hint : ValueType) (action body : Term)
  deriving Repr

inductive Clauses where
  | nil
  | cons (operation parameter binder : Nat) (body : Term) (rest : Clauses)
  deriving Repr
end

def Term.hint : Term → ValueType
  | .unit h | .boolean h _ | .integer h _ | .variable h _ | .resourceRef h _
  | .pair h _ _ | .lambda h _ _ | .app h _ _ | .bind h _ _ _ | .branch h _ _ _
  | .perform h _ _ _ | .handle h _ _ _ | .resume h _ _ | .discard h _
  | .resource h _ _ _ | .cleanup h _ _ => h

mutual
def Term.erase : Term → ScopedExpressions.Code
  | .unit _ => .unit
  | .boolean _ value => .boolean value
  | .integer _ value => .integer value
  | .variable _ name => .variable name
  | .resourceRef _ name => .resourceRef name
  | .pair _ left right => .pair left.erase right.erase
  | .lambda _ parameter body => .lambda parameter body.erase
  | .app _ function argument => .app function.erase argument.erase
  | .bind _ parameter initializer body => .bind parameter initializer.erase body.erase
  | .branch _ condition yes no => .branch condition.erase yes.erase no.erase
  | .perform _ effect operation operand => .perform effect operation operand.erase
  | .handle _ effect body clauses => .handle effect body.erase clauses.erase
  | .resume _ binder operand => .resume binder operand.erase
  | .discard _ binder => .discard binder
  | .resource _ binder initializer body => .resource binder initializer.erase body.erase
  | .cleanup _ action body => .cleanup action.erase body.erase

def Clauses.erase : Clauses → ScopedExpressions.Clauses
  | .nil => .nil
  | .cons operation parameter binder body rest => .cons operation parameter binder body.erase rest.erase
end

mutual
def Term.instantiate (environment : Environment) : Term → Term
  | .unit h => .unit (h.instantiate environment)
  | .boolean h value => .boolean (h.instantiate environment) value
  | .integer h value => .integer (h.instantiate environment) value
  | .variable h name => .variable (h.instantiate environment) name
  | .resourceRef h name => .resourceRef (h.instantiate environment) (name.instantiate environment)
  | .pair h left right => .pair (h.instantiate environment) (left.instantiate environment) (right.instantiate environment)
  | .lambda h parameter body => .lambda (h.instantiate environment) parameter (body.instantiate environment)
  | .app h function argument => .app (h.instantiate environment) (function.instantiate environment) (argument.instantiate environment)
  | .bind h parameter initializer body =>
      .bind (h.instantiate environment) parameter (initializer.instantiate environment) (body.instantiate environment)
  | .branch h condition yes no =>
      .branch (h.instantiate environment) (condition.instantiate environment) (yes.instantiate environment) (no.instantiate environment)
  | .perform h effect operation operand =>
      .perform (h.instantiate environment) (effect.instantiate environment) operation (operand.instantiate environment)
  | .handle h effect body clauses =>
      .handle (h.instantiate environment) (effect.instantiate environment) (body.instantiate environment) (clauses.instantiate environment)
  | .resume h binder operand => .resume (h.instantiate environment) binder (operand.instantiate environment)
  | .discard h binder => .discard (h.instantiate environment) binder
  | .resource h binder initializer body =>
      .resource (h.instantiate environment) binder (initializer.instantiate environment) (body.instantiate (environment.mask binder))
  | .cleanup h action body => .cleanup (h.instantiate environment) (action.instantiate environment) (body.instantiate environment)

def Clauses.instantiate (environment : Environment) : Clauses → Clauses
  | .nil => .nil
  | .cons operation parameter binder body rest =>
      .cons operation parameter binder (body.instantiate environment) (rest.instantiate environment)
end

mutual
def Term.subst (term : Term) (name : Nat) (value : Term) : Term := match term with
  | .unit h => .unit h
  | .boolean h b => .boolean h b
  | .integer h n => .integer h n
  | .variable h other => if name = other then value else .variable h other
  | .resourceRef h resource => .resourceRef h resource
  | .pair h left right => .pair h (left.subst name value) (right.subst name value)
  | .lambda h parameter body => .lambda h parameter (if name = parameter then body else body.subst name value)
  | .app h function argument => .app h (function.subst name value) (argument.subst name value)
  | .bind h parameter initializer body =>
      .bind h parameter (initializer.subst name value) (if name = parameter then body else body.subst name value)
  | .branch h condition yes no => .branch h (condition.subst name value) (yes.subst name value) (no.subst name value)
  | .perform h effect operation operand => .perform h effect operation (operand.subst name value)
  | .handle h effect body clauses => .handle h effect (body.subst name value) (clauses.subst name value)
  | .resume h binder operand => .resume h binder (operand.subst name value)
  | .discard h binder => .discard h binder
  | .resource h binder initializer body => .resource h binder (initializer.subst name value) (body.subst name value)
  | .cleanup h action body => .cleanup h (action.subst name value) (body.subst name value)

def Clauses.subst (clauses : Clauses) (name : Nat) (value : Term) : Clauses := match clauses with
  | .nil => .nil
  | .cons operation parameter binder body rest =>
      .cons operation parameter binder (if name = parameter then body else body.subst name value) (rest.subst name value)
end

theorem Term.instantiated_hint (term : Term) (environment : Environment) :
    (term.instantiate environment).hint = term.hint.instantiate environment := by
  cases term <;> rfl

mutual
theorem Term.erase_instantiate (term : Term) (environment : Environment) :
    (term.instantiate environment).erase = term.erase.instantiate environment := by
  cases term <;> simp only [Term.instantiate, Term.erase, ScopedExpressions.Code.instantiate,
    Term.erase_instantiate, Clauses.erase_instantiate]

theorem Clauses.erase_instantiate (clauses : Clauses) (environment : Environment) :
    (clauses.instantiate environment).erase = clauses.erase.instantiate environment := by
  cases clauses <;> simp only [Clauses.instantiate, Clauses.erase, ScopedExpressions.Clauses.instantiate,
    Term.erase_instantiate, Clauses.erase_instantiate]
end

mutual
theorem Term.erase_subst (term : Term) (name : Nat) (value : Term) :
    (term.subst name value).erase = term.erase.subst name value.erase := by
  cases term <;> simp only [Term.subst, Term.erase, ScopedExpressions.Code.subst, apply_ite,
    Term.erase_subst, Clauses.erase_subst]
  all_goals split <;> simp_all

theorem Clauses.erase_subst (clauses : Clauses) (name : Nat) (value : Term) :
    (clauses.subst name value).erase = clauses.erase.subst name value.erase := by
  cases clauses <;> simp only [Clauses.subst, Clauses.erase, ScopedExpressions.Clauses.subst, apply_ite,
    Term.erase_subst, Clauses.erase_subst]
  all_goals split <;> simp_all
end

/-- Reuse the existing commutation law for erased code; this does not yet prove
commutation of the hint trees when inserted hints contain free resource names. -/
theorem Term.erased_instantiation_substitution (term value : Term) (name : Nat) (environment : Environment)
    (closed : value.erase.ResourceClosed) :
    ((term.subst name value).instantiate environment).erase =
      ((term.instantiate environment).subst name value).erase := by
  simp only [Term.erase_instantiate, Term.erase_subst]
  exact ScopedExpressions.Code.instantiation_subst term.erase name value.erase environment closed


/-- Saved source contexts retain the other annotated children and the whole
expression's result hint. The focused child supplies its own input hint. -/
inductive Context where
  | pairLeft (hint : ValueType) (right : Term)
  | pairRight (hint : ValueType) (left : Term)
  | appFunction (hint : ValueType) (argument : Term)
  | appArgument (hint : ValueType) (function : Term)
  | bind (hint : ValueType) (parameter : Nat) (body : Term)
  | branch (hint : ValueType) (yes no : Term)
  | perform (hint : ValueType) (effect : Effect) (operation : Nat)
  | resume (hint : ValueType) (binder : Nat)
  | resource (hint : ValueType) (binder : Nat) (body : Term)
  | cleanup (hint : ValueType) (body : Term)
  deriving Repr

def Context.hint : Context → ValueType
  | .pairLeft h _ | .pairRight h _ | .appFunction h _ | .appArgument h _
  | .bind h _ _ | .branch h _ _ | .perform h _ _ | .resume h _
  | .resource h _ _ | .cleanup h _ => h

def Context.plug (context : Context) (child : Term) : Term := match context with
  | .pairLeft h right => .pair h child right
  | .pairRight h left => .pair h left child
  | .appFunction h argument => .app h child argument
  | .appArgument h function => .app h function child
  | .bind h parameter body => .bind h parameter child body
  | .branch h yes no => .branch h child yes no
  | .perform h effect operation => .perform h effect operation child
  | .resume h binder => .resume h binder child
  | .resource h binder body => .resource h binder child body
  | .cleanup h body => .cleanup h child body

def Context.erase : Context → ScopedExecution.Context
  | .pairLeft _ right => .pairLeft right.erase
  | .pairRight _ left => .pairRight left.erase
  | .appFunction _ argument => .appFunction argument.erase
  | .appArgument _ function => .appArgument function.erase
  | .bind _ parameter body => .bind parameter body.erase
  | .branch _ yes no => .branch yes.erase no.erase
  | .perform _ effect operation => .perform effect operation
  | .resume _ binder => .resume binder
  | .resource _ binder body => .resource binder body.erase
  | .cleanup _ body => .cleanup body.erase

theorem Context.erase_plug (context : Context) (child : Term) :
    (context.plug child).erase = context.erase.plug child.erase := by
  cases context <;> rfl

theorem Context.plug_hint (context : Context) (child : Term) :
    (context.plug child).hint = context.hint := by
  cases context <;> rfl

inductive Focus : Term → Term → Context → Prop where
  | pairLeft (notValue : ¬ left.erase.IsValue) : Focus (.pair h left right) left (.pairLeft h right)
  | pairRight (value : left.erase.IsValue) (notValue : ¬ right.erase.IsValue) :
      Focus (.pair h left right) right (.pairRight h left)
  | appFunction (notValue : ¬ function.erase.IsValue) : Focus (.app h function argument) function (.appFunction h argument)
  | appArgument (value : function.erase.IsValue) (notValue : ¬ argument.erase.IsValue) :
      Focus (.app h function argument) argument (.appArgument h function)
  | bind (notValue : ¬ initializer.erase.IsValue) :
      Focus (.bind h parameter initializer body) initializer (.bind h parameter body)
  | branch (notValue : ¬ condition.erase.IsValue) : Focus (.branch h condition yes no) condition (.branch h yes no)
  | perform (notValue : ¬ operand.erase.IsValue) :
      Focus (.perform h effect operation operand) operand (.perform h effect operation)
  | resume (notValue : ¬ operand.erase.IsValue) : Focus (.resume h binder operand) operand (.resume h binder)
  | resource (notValue : ¬ initializer.erase.IsValue) :
      Focus (.resource h binder initializer body) initializer (.resource h binder body)
  | cleanup (notValue : ¬ action.erase.IsValue) : Focus (.cleanup h action body) action (.cleanup h body)

theorem Focus.reconstructs (focus : Focus whole child context) : context.plug child = whole := by
  cases focus <;> rfl

theorem Focus.output_hint (focus : Focus whole child context) : context.hint = whole.hint := by
  cases focus <;> rfl

theorem Focus.erase (focus : Focus whole child context) :
    ScopedExecution.Focus whole.erase child.erase context.erase := by
  cases focus with
  | pairLeft notValue => exact .pairLeft notValue
  | pairRight value notValue => exact .pairRight value notValue
  | appFunction notValue => exact .appFunction notValue
  | appArgument value notValue => exact .appArgument value notValue
  | bind notValue => exact .bind notValue
  | branch notValue => exact .branch notValue
  | perform notValue => exact .perform notValue
  | resume notValue => exact .resume notValue
  | resource notValue => exact .resource notValue
  | cleanup notValue => exact .cleanup notValue

/-- Erasing annotations loses no focus position. In particular, all four
forms whose ports need source choices are represented by the same rules. -/
theorem focus_lift (position : ScopedExecution.Focus whole.erase rawChild rawContext) :
    ∃ child context, Focus whole child context ∧ child.erase = rawChild ∧ context.erase = rawContext := by
  cases whole <;> simp only [Term.erase] at position <;> cases position
  all_goals first
    | exact ⟨_, _, .pairLeft ‹_›, rfl, rfl⟩
    | exact ⟨_, _, .pairRight ‹_› ‹_›, rfl, rfl⟩
    | exact ⟨_, _, .appFunction ‹_›, rfl, rfl⟩
    | exact ⟨_, _, .appArgument ‹_› ‹_›, rfl, rfl⟩
    | exact ⟨_, _, .bind ‹_›, rfl, rfl⟩
    | exact ⟨_, _, .branch ‹_›, rfl, rfl⟩
    | exact ⟨_, _, .perform ‹_›, rfl, rfl⟩
    | exact ⟨_, _, .resume ‹_›, rfl, rfl⟩
    | exact ⟨_, _, .resource ‹_›, rfl, rfl⟩
    | exact ⟨_, _, .cleanup ‹_›, rfl, rfl⟩

/-- Unlike erased code with existential type choices, one annotated term
selects one annotated child and context at its next evaluation position. -/
theorem Focus.unique (first : Focus whole a left) (second : Focus whole b right) :
    a = b ∧ left = right := by
  cases first <;> cases second <;> first | exact ⟨rfl, rfl⟩ | contradiction

theorem Focus.input_hint_unique (first : Focus whole a left) (second : Focus whole b right) :
    a.hint = b.hint := congrArg Term.hint (first.unique second).1

/-- A frame check now reads the selected child's retained hint, rather than
an arbitrary hint supplied independently of the annotated source position. -/
def checkFocusFrame (environment : Environment) (child : Term) (result : ScopedPorts.Port)
    (stack : ScopedExecution.Stack) (plain : ScopedExecution.PlainData) : Bool :=
  SourceFocusHints.checkFrame environment child.hint result stack plain

theorem checked_focus_ports
    (source : SourceFocusHints.checkSource environment child.hint value = true)
    (checked : checkFocusFrame environment child result stack plain = true) :
    ScopedPorts.eraseType plain.input = value.erase.erase.port ∧
    ScopedPorts.eraseType plain.output = SourceScheduledExecution.stackInputPort stack result :=
  SourceFocusHints.source_frame_agreement source checked


/-- Ordinary syntax reductions retain the selected annotated body or branch.
The premises are exactly the old closed-value and binder-readiness checks. -/
inductive Reduction : Term → ScopedExecution.Scope → Term → ScopedExecution.Scope → Prop where
  | bind (closed : ScopedExpressions.ClosedValue initializer.erase)
      (ready : ScopedExpressions.ClosedExcept parameter body.erase) :
      Reduction (.bind h parameter initializer body) scope (body.subst parameter initializer) scope
  | beta (closed : ScopedExpressions.ClosedValue argument.erase)
      (closure : ScopedExpressions.ClosedValue (.lambda parameter body.erase)) :
      Reduction (.app h (.lambda functionHint parameter body) argument) scope (body.subst parameter argument) .none
  | ifTrue : Reduction (.branch h (.boolean conditionHint true) yes no) scope yes scope
  | ifFalse : Reduction (.branch h (.boolean conditionHint false) yes no) scope no scope

theorem Reduction.erase (step : Reduction before scope after nextScope)
    (stack : ScopedExecution.Stack) :
    ScopedPortJoint.OrdinaryStep ⟨before.erase, scope, stack⟩ ⟨after.erase, nextScope, stack⟩ := by
  cases step with
  | bind closed ready =>
      simpa only [Term.erase, Term.erase_subst] using
        (ScopedPortJoint.OrdinaryStep.bind (scope := scope) (tail := stack) closed ready)
  | beta closed closure =>
      simpa only [Term.erase, Term.erase_subst] using
        (ScopedPortJoint.OrdinaryStep.beta (scope := scope) (tail := stack) closed closure)
  | ifTrue => exact .ifTrue
  | ifFalse => exact .ifFalse

theorem Reduction.executes (step : Reduction before scope after nextScope)
    (stack : ScopedExecution.Stack) :
    ScopedExecution.RawStep ⟨before.erase, scope, stack⟩ ⟨after.erase, nextScope, stack⟩ [] [] :=
  ScopedPortJoint.ordinary_step_executes (step.erase stack)

namespace Examples

def unit : Term := .unit .unit
def functionHint (input : ValueType) : ValueType := .function input .unit [] []
def constant (input : ValueType) : Term := .lambda (functionHint input) 2 unit
def initializer (input : ValueType) : Term := .bind (functionHint input) 1 unit (constant input)
def program (input : ValueType) : Term := .bind .unit 0 (initializer input) unit

/-- Both annotations erase to the previously admitted example, but their
focused child data retain the two distinct choices. -/
theorem admitted_program_erasure (input : ValueType) :
    (program input).erase = SourceFocusAnnotationGap.program := rfl

theorem binding_focus (input : ValueType) :
    Focus (program input) (initializer input) (.bind .unit 0 unit) :=
  .bind (by simp [initializer, Term.erase, ScopedExpressions.Code.IsValue])

theorem all_remaining_focus_forms :
    Focus (.app .unit (initializer .unit) unit) (initializer .unit) (.appFunction .unit unit) ∧
    Focus (.app .unit (constant .unit) (.bind .unit 1 unit unit)) (.bind .unit 1 unit unit)
      (.appArgument .unit (constant .unit)) ∧
    Focus (program .integer) (initializer .integer) (.bind .unit 0 unit) ∧
    Focus (.cleanup .unit (initializer .unit) unit) (initializer .unit) (.cleanup .unit unit) := by
  exact ⟨.appFunction (by simp [initializer, Term.erase, ScopedExpressions.Code.IsValue]),
    .appArgument trivial (by simp [Term.erase, ScopedExpressions.Code.IsValue]), binding_focus _,
    .cleanup (by simp [initializer, Term.erase, ScopedExpressions.Code.IsValue])⟩

theorem selected_choices_authenticated :
    SourceFocusHints.checkSource Environment.empty (initializer .unit).hint
      (SourceFocusAnnotationGap.functionType .unit) = true ∧
    SourceFocusHints.checkSource Environment.empty (initializer .integer).hint
      (SourceFocusAnnotationGap.functionType .integer) = true := by decide

theorem source_choice_switch_rejected :
    SourceFocusHints.checkSource Environment.empty (initializer .unit).hint
      (SourceFocusAnnotationGap.functionType .integer) = false := by decide

def frozen : Term := .resourceRef (.reference (.activation 11)) (.activation 11)
def localBody : Term := .bind .unit 0
  (.resourceRef (.reference (.bound 7)) (.bound 7)) unit

/-- Installing an outer environment does not capture a nested resource's
lexical names, including names appearing only in type annotations. -/
theorem nested_resource_masks_hints :
    (Term.resource .unit 7 unit localBody).instantiate (Environment.empty.bind 7 29) =
      .resource .unit 7 unit localBody := rfl

theorem opening_body_realizes_hints :
    localBody.instantiate (Environment.empty.bind 7 29) =
      .bind .unit 0 (.resourceRef (.reference (.activation 29)) (.activation 29)) unit := rfl

/-- The annotated value is copied intact through ordinary substitution;
its old activation is distinct from a later same-name resource binding. -/
theorem substituted_frozen_value_keeps_hint :
    ((Term.variable (.reference (.activation 11)) 3).subst 3 frozen).instantiate
      (Environment.empty.bind 7 29) = frozen := rfl

theorem lambda_binder_shadows_substitution :
    (Term.lambda (functionHint .unit) 3 (.variable .unit 3)).subst 3 unit =
      .lambda (functionHint .unit) 3 (.variable .unit 3) := rfl

theorem clause_parameter_shadows_substitution :
    (Clauses.cons 0 3 9 (.variable .unit 3) .nil).subst 3 unit =
      .cons 0 3 9 (.variable .unit 3) .nil := rfl

theorem bind_retains_constant_hint (input : ValueType) : Reduction (initializer input) scope (constant input) scope := by
  have closed : ScopedExpressions.ClosedValue unit.erase := ⟨trivial, rfl, by intro dependency member; cases member⟩
  have ready : ScopedExpressions.ClosedExcept 1 (constant input).erase := by
    intro name member
    cases member
  exact .bind closed ready

theorem beta_enters_no_ticket_scope :
    Reduction (.app .unit (.lambda (functionHint .unit) 3 (.variable .unit 3)) unit)
      (.ticket 9 19) unit .none :=
  .beta ⟨trivial, rfl, by intro dependency member; cases member⟩
    ⟨trivial, rfl, by intro dependency member; cases member⟩

def openHintValue : Term := .lambda (functionHint (.reference (.bound 7))) 2 unit

/-- Closed erased code can still have a free resource name in its annotation.
Hence full annotated substitution needs closure of metadata as well as code. -/
theorem erased_closure_does_not_freeze_hints :
    openHintValue.erase.ResourceClosed ∧
    (((Term.variable openHintValue.hint 0).subst 0 openHintValue).instantiate (Environment.empty.bind 7 29)).hint ≠
      (((Term.variable openHintValue.hint 0).instantiate (Environment.empty.bind 7 29)).subst 0 openHintValue).hint := by
  exact ⟨rfl, by decide⟩

end Examples

end Ash.OneShot.SourceAnnotatedCode

#print axioms Ash.OneShot.SourceAnnotatedCode.Term.instantiated_hint
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.erase_instantiate
#print axioms Ash.OneShot.SourceAnnotatedCode.Clauses.erase_instantiate
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.erase_subst
#print axioms Ash.OneShot.SourceAnnotatedCode.Clauses.erase_subst
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.erased_instantiation_substitution

#print axioms Ash.OneShot.SourceAnnotatedCode.Context.erase_plug
#print axioms Ash.OneShot.SourceAnnotatedCode.Focus.reconstructs
#print axioms Ash.OneShot.SourceAnnotatedCode.Focus.output_hint
#print axioms Ash.OneShot.SourceAnnotatedCode.Focus.erase
#print axioms Ash.OneShot.SourceAnnotatedCode.focus_lift
#print axioms Ash.OneShot.SourceAnnotatedCode.Focus.unique
#print axioms Ash.OneShot.SourceAnnotatedCode.Focus.input_hint_unique
#print axioms Ash.OneShot.SourceAnnotatedCode.checked_focus_ports

#print axioms Ash.OneShot.SourceAnnotatedCode.Reduction.erase
#print axioms Ash.OneShot.SourceAnnotatedCode.Reduction.executes
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.admitted_program_erasure
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.binding_focus
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.all_remaining_focus_forms
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.selected_choices_authenticated
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.source_choice_switch_rejected
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.nested_resource_masks_hints
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.opening_body_realizes_hints
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.substituted_frozen_value_keeps_hint
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.lambda_binder_shadows_substitution
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.clause_parameter_shadows_substitution
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.bind_retains_constant_hint
#print axioms Ash.OneShot.SourceAnnotatedCode.Context.plug_hint
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.beta_enters_no_ticket_scope
#print axioms Ash.OneShot.SourceAnnotatedCode.Examples.erased_closure_does_not_freeze_hints
