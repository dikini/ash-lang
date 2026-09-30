import SourceAnnotatedCode

/-! Finite lexical closure includes annotations as well as erased code. Locally
bound resource names remain legal under their acquisition scope. Existing
name-instantiation laws supply the metadata transport and erasure connection;
this layer grants no resource access or continuation capability. -/
namespace Ash.OneShot.SourceAnnotatedCode
open Instantiation
open ScopedExpressions (Missing missing_append missing_mask unresolved unresolved_append)
variable {term : Term}

/-- Resource names in function domains, results, latent effects and retained
support all contribute to lexical annotation closure. -/
def hintNames : ValueType → List Nat
  | .unit | .boolean | .integer => []
  | .reference name => name.freeNames
  | .product left right => hintNames left ++ hintNames right
  | .function input output requests retained =>
      hintNames input ++ (hintNames output ++
        (requests.flatMap Effect.freeNames ++ retained.flatMap ResourceName.freeNames))

theorem names_map_identity {names : α → List Nat} {instantiate : α → α}
    (preserves : ∀ value, Missing environment (names value) → instantiate value = value)
    (values : List α) (missing : Missing environment (values.flatMap names)) :
    values.map instantiate = values := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨first, tail⟩ := missing_append missing
      simp only [List.map_cons, preserves head first, ih tail]

theorem hint_instantiation_identity (hint : ValueType) (environment : Environment)
    (missing : Missing environment (hintNames hint)) : hint.instantiate environment = hint := by
  induction hint with
  | unit | boolean | integer => rfl
  | reference name => exact congrArg ValueType.reference (ScopedExpressions.name_instantiation_identity name environment missing)
  | product left right ihLeft ihRight =>
      obtain ⟨leftMissing, rightMissing⟩ := missing_append missing
      simp only [ValueType.instantiate, ihLeft leftMissing, ihRight rightMissing]
  | function input output requests retained ihInput ihOutput =>
      obtain ⟨inputMissing, restMissing⟩ := missing_append missing
      obtain ⟨outputMissing, interfacesMissing⟩ := missing_append restMissing
      obtain ⟨requestMissing, retainedMissing⟩ := missing_append interfacesMissing
      simp only [ValueType.instantiate, ihInput inputMissing, ihOutput outputMissing,
        names_map_identity (fun value checked => ScopedExpressions.effect_instantiation_identity value environment checked)
          requests requestMissing,
        names_map_identity (fun value checked => ScopedExpressions.name_instantiation_identity value environment checked)
          retained retainedMissing]

theorem names_map_free {names : α → List Nat} {instantiate : α → α}
    (preserves : ∀ value, names (instantiate value) = unresolved environment (names value))
    (values : List α) :
    (values.map instantiate).flatMap names = unresolved environment (values.flatMap names) := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp only [List.map_cons, List.flatMap_cons, preserves, ih, unresolved_append]

theorem hint_instantiation_free (hint : ValueType) (environment : Environment) :
    hintNames (hint.instantiate environment) = unresolved environment (hintNames hint) := by
  induction hint with
  | unit | boolean | integer => rfl
  | reference name => exact ScopedExpressions.name_instantiation_free environment name
  | product left right ihLeft ihRight => simp only [ValueType.instantiate, hintNames, ihLeft, ihRight, unresolved_append]
  | function input output requests retained ihInput ihOutput =>
      simp only [ValueType.instantiate, hintNames, ihInput, ihOutput, unresolved_append,
        names_map_free (ScopedExpressions.effect_instantiation_free environment),
        names_map_free (ScopedExpressions.name_instantiation_free environment)]

mutual
def Term.freeNames : Term → List Nat
  | .unit h | .boolean h _ | .integer h _ | .variable h _ | .discard h _ => hintNames h
  | .resourceRef h name => hintNames h ++ name.freeNames
  | .pair h left right | .app h left right | .bind h _ left right | .cleanup h left right =>
      hintNames h ++ (left.freeNames ++ right.freeNames)
  | .lambda h _ body | .resume h _ body => hintNames h ++ body.freeNames
  | .branch h condition yes no => hintNames h ++ (condition.freeNames ++ (yes.freeNames ++ no.freeNames))
  | .perform h effect _ operand => hintNames h ++ (effect.freeNames ++ operand.freeNames)
  | .handle h effect body clauses => hintNames h ++ (effect.freeNames ++ (body.freeNames ++ clauses.freeNames))
  | .resource h binder initializer body =>
      hintNames h ++ (initializer.freeNames ++ body.freeNames.filter (· != binder))

def Clauses.freeNames : Clauses → List Nat
  | .nil => []
  | .cons _ _ _ body rest => body.freeNames ++ rest.freeNames
end

mutual
theorem Term.instantiation_free (term : Term) (environment : Environment) :
    (term.instantiate environment).freeNames = unresolved environment term.freeNames := by
  cases term with
  | unit h | boolean h _ | integer h _ | «variable» h _ | discard h _ => exact hint_instantiation_free h environment
  | resourceRef h name =>
      simp only [Term.instantiate, Term.freeNames, hint_instantiation_free,
        ScopedExpressions.name_instantiation_free, unresolved_append]
  | pair h left right | app h left right | bind h _ left right | cleanup h left right =>
      simp only [Term.instantiate, Term.freeNames, hint_instantiation_free, left.instantiation_free,
        right.instantiation_free, unresolved_append]
  | lambda h _ body | resume h _ body =>
      simp only [Term.instantiate, Term.freeNames, hint_instantiation_free, body.instantiation_free, unresolved_append]
  | branch h condition yes no =>
      simp only [Term.instantiate, Term.freeNames, hint_instantiation_free, condition.instantiation_free,
        yes.instantiation_free, no.instantiation_free, unresolved_append]
  | perform h effect operation operand =>
      simp only [Term.instantiate, Term.freeNames, hint_instantiation_free, ScopedExpressions.effect_instantiation_free,
        operand.instantiation_free, unresolved_append]
  | handle h effect body clauses =>
      simp only [Term.instantiate, Term.freeNames, hint_instantiation_free, ScopedExpressions.effect_instantiation_free,
        body.instantiation_free, clauses.instantiation_free, unresolved_append]
  | resource h binder initializer body =>
      simp only [Term.instantiate, Term.freeNames, hint_instantiation_free, initializer.instantiation_free,
        body.instantiation_free, ScopedExpressions.masked_unresolved, unresolved_append]

theorem Clauses.instantiation_free (clauses : Clauses) (environment : Environment) :
    (clauses.instantiate environment).freeNames = unresolved environment clauses.freeNames := by
  cases clauses with
  | nil => rfl
  | cons operation parameter binder body rest =>
      simp only [Clauses.instantiate, Clauses.freeNames, body.instantiation_free, rest.instantiation_free, unresolved_append]
end

mutual
theorem Term.instantiation_identity (term : Term) (environment : Environment)
    (missing : Missing environment term.freeNames) : term.instantiate environment = term := by
  cases term with
  | unit h | boolean h _ | integer h _ | «variable» h _ | discard h _ =>
      simp only [Term.instantiate, hint_instantiation_identity h environment missing]
  | resourceRef h name =>
      obtain ⟨hintMissing, nameMissing⟩ := missing_append missing
      simp only [Term.instantiate, hint_instantiation_identity h environment hintMissing,
        ScopedExpressions.name_instantiation_identity name environment nameMissing]
  | pair h left right | app h left right | bind h _ left right | cleanup h left right =>
      obtain ⟨hintMissing, restMissing⟩ := missing_append missing
      obtain ⟨leftMissing, rightMissing⟩ := missing_append restMissing
      simp only [Term.instantiate, hint_instantiation_identity h environment hintMissing,
        left.instantiation_identity environment leftMissing, right.instantiation_identity environment rightMissing]
  | lambda h _ body | resume h _ body =>
      obtain ⟨hintMissing, bodyMissing⟩ := missing_append missing
      simp only [Term.instantiate, hint_instantiation_identity h environment hintMissing,
        body.instantiation_identity environment bodyMissing]
  | branch h condition yes no =>
      obtain ⟨hintMissing, restMissing⟩ := missing_append missing
      obtain ⟨conditionMissing, branchesMissing⟩ := missing_append restMissing
      obtain ⟨yesMissing, noMissing⟩ := missing_append branchesMissing
      simp only [Term.instantiate, hint_instantiation_identity h environment hintMissing,
        condition.instantiation_identity environment conditionMissing,
        yes.instantiation_identity environment yesMissing, no.instantiation_identity environment noMissing]
  | perform h effect operation operand =>
      obtain ⟨hintMissing, restMissing⟩ := missing_append missing
      obtain ⟨effectMissing, operandMissing⟩ := missing_append restMissing
      simp only [Term.instantiate, hint_instantiation_identity h environment hintMissing,
        ScopedExpressions.effect_instantiation_identity effect environment effectMissing,
        operand.instantiation_identity environment operandMissing]
  | handle h effect body clauses =>
      obtain ⟨hintMissing, restMissing⟩ := missing_append missing
      obtain ⟨effectMissing, childrenMissing⟩ := missing_append restMissing
      obtain ⟨bodyMissing, clausesMissing⟩ := missing_append childrenMissing
      simp only [Term.instantiate, hint_instantiation_identity h environment hintMissing,
        ScopedExpressions.effect_instantiation_identity effect environment effectMissing,
        body.instantiation_identity environment bodyMissing, clauses.instantiation_identity environment clausesMissing]
  | resource h binder initializer body =>
      obtain ⟨hintMissing, restMissing⟩ := missing_append missing
      obtain ⟨initialMissing, bodyMissing⟩ := missing_append restMissing
      simp only [Term.instantiate, hint_instantiation_identity h environment hintMissing,
        initializer.instantiation_identity environment initialMissing,
        body.instantiation_identity (environment.mask binder) (missing_mask bodyMissing)]

theorem Clauses.instantiation_identity (clauses : Clauses) (environment : Environment)
    (missing : Missing environment clauses.freeNames) : clauses.instantiate environment = clauses := by
  cases clauses with
  | nil => rfl
  | cons operation parameter binder body rest =>
      obtain ⟨bodyMissing, restMissing⟩ := missing_append missing
      simp only [Clauses.instantiate, body.instantiation_identity environment bodyMissing,
        rest.instantiation_identity environment restMissing]
end

def Term.ResourceClosed (term : Term) : Prop := term.freeNames = []
def Term.checkClosed (term : Term) : Bool := decide (term.freeNames = [])

theorem Term.check_closed_iff : term.checkClosed = true ↔ term.ResourceClosed := by
  simp [Term.checkClosed, Term.ResourceClosed]

theorem Term.instantiation_closes_iff (term : Term) (environment : Environment) :
    (term.instantiate environment).ResourceClosed ↔ ScopedExpressions.Covered environment term.freeNames := by
  rw [Term.ResourceClosed, term.instantiation_free]
  exact ScopedExpressions.unresolved_empty_iff environment term.freeNames

theorem Term.closed_instantiation_identity (term : Term) (environment : Environment)
    (closed : term.ResourceClosed) : term.instantiate environment = term :=
  term.instantiation_identity environment (fun _ member => False.elim (by rw [closed] at member; cases member))

/-- Reuse the existing erased-code closure theorem instead of proving a second
structural inclusion theorem for the two free-name enumerations. -/
theorem Term.closed_erasure (closed : term.ResourceClosed) : term.erase.ResourceClosed := by
  let allNames : Environment := fun _ => some 0
  have resolved := (term.erase.instantiation_closes_iff allNames).mpr (fun _ _ => ⟨0, rfl⟩)
  have identity : term.erase.instantiate allNames = term.erase := by
    rw [← term.erase_instantiate, term.closed_instantiation_identity allNames closed]
  exact identity ▸ resolved


mutual
/-- Closed annotated values can move under resource scopes without rebinding
names in either their code or metadata. The whole trees, not just erasures,
commute. Ordinary binders retain the original scoped substitution discipline. -/
theorem Term.instantiation_subst (term : Term) (name : Nat) (value : Term) (environment : Environment)
    (closed : value.ResourceClosed) :
    (term.subst name value).instantiate environment = (term.instantiate environment).subst name value := by
  cases term with
  | unit _ | boolean _ _ | integer _ _ | resourceRef _ _ | discard _ _ => rfl
  | «variable» h other =>
      by_cases same : name = other
      · simp only [Term.subst, if_pos same, value.closed_instantiation_identity environment closed, Term.instantiate]
      · simp only [Term.subst, if_neg same, Term.instantiate]
  | pair h left right | app h left right | cleanup h left right =>
      simp only [Term.subst, Term.instantiate, left.instantiation_subst name value environment closed,
        right.instantiation_subst name value environment closed]
  | lambda h parameter body =>
      by_cases same : name = parameter
      · simp only [Term.subst, Term.instantiate, if_pos same]
      · simp only [Term.subst, Term.instantiate, if_neg same, body.instantiation_subst name value environment closed]
  | bind h parameter initializer body =>
      by_cases same : name = parameter
      · simp only [Term.subst, Term.instantiate, if_pos same, initializer.instantiation_subst name value environment closed]
      · simp only [Term.subst, Term.instantiate, if_neg same, initializer.instantiation_subst name value environment closed,
          body.instantiation_subst name value environment closed]
  | branch h condition yes no =>
      simp only [Term.subst, Term.instantiate, condition.instantiation_subst name value environment closed,
        yes.instantiation_subst name value environment closed, no.instantiation_subst name value environment closed]
  | perform h effect operation operand | resume h operation operand =>
      simp only [Term.subst, Term.instantiate, operand.instantiation_subst name value environment closed]
  | handle h effect body clauses =>
      simp only [Term.subst, Term.instantiate, body.instantiation_subst name value environment closed,
        clauses.instantiation_subst name value environment closed]
  | resource h binder initializer body =>
      simp only [Term.subst, Term.instantiate, initializer.instantiation_subst name value environment closed,
        body.instantiation_subst name value (environment.mask binder) closed]

theorem Clauses.instantiation_subst (clauses : Clauses) (name : Nat) (value : Term) (environment : Environment)
    (closed : value.ResourceClosed) :
    (clauses.subst name value).instantiate environment = (clauses.instantiate environment).subst name value := by
  cases clauses with
  | nil => rfl
  | cons operation parameter binder body rest =>
      by_cases same : name = parameter
      · simp only [Clauses.subst, Clauses.instantiate, if_pos same, rest.instantiation_subst name value environment closed]
      · simp only [Clauses.subst, Clauses.instantiate, if_neg same, body.instantiation_subst name value environment closed,
          rest.instantiation_subst name value environment closed]
end

/-- Acquisition opens the annotated body, not the enclosing declaration that
would mask its binder again. Freshness and live access are separate checks. -/
theorem Term.acquisition_closes_body {hint : ValueType}
    (closed : (Term.resource hint binder initializer body).ResourceClosed)
    (environment : Environment) (identity : Nat) :
    (body.instantiate (environment.bind binder identity)).ResourceClosed := by
  apply (body.instantiation_closes_iff _).mpr
  intro name member
  by_cases same : name = binder
  · exact ⟨identity, by simp [Environment.bind, same]⟩
  · have outside : name ∈ (Term.resource hint binder initializer body).freeNames :=
      List.mem_append_right _ (List.mem_append_right _ (by simp [member, same]))
    rw [closed] at outside
    cases outside

/-- Any later environment leaves the entire closed term fixed. Consequently
its retained root hint cannot change the finite source/frame port check. -/
theorem Term.closed_hint_fixed (closed : term.ResourceClosed) (environment : Environment) :
    term.hint.instantiate environment = term.hint := by
  rw [← term.instantiated_hint, term.closed_instantiation_identity environment closed]

theorem Term.closed_frame_check_fixed (closed : term.ResourceClosed) (environment : Environment) :
    SourceFocusHints.checkFrame environment term.hint result stack plain =
      SourceFocusHints.checkFrame Environment.empty term.hint result stack plain := by
  simp only [SourceFocusHints.checkFrame, SourceFocusHints.inputPort, term.closed_hint_fixed closed]

namespace NameExamples

def localValue : Term := .lambda (.function .unit .unit [] []) 5
  (.resource .unit 7 Examples.unit Examples.localBody)

theorem all_function_metadata_counted :
    hintNames (.function (.reference (.bound 1)) (.reference (.bound 2))
      [.user 91 [.apply (.nominal 0) (.resource (.bound 3))]] [.bound 4]) = [1, 2, 3, 4] := rfl

theorem previous_open_metadata_rejected : Examples.openHintValue.checkClosed = false := by decide

theorem local_resource_value_accepted : localValue.checkClosed = true := by decide

theorem result_hint_is_outside_resource_scope :
    (Term.resource (.reference (.bound 7)) 7 Examples.unit Examples.localBody).checkClosed = false := by decide

theorem initial_scope_is_outside_resource_binder :
    (Term.resource .unit 7
      (.perform .integer (.cell (.bound 7)) 0 (.resourceRef (.reference (.bound 7)) (.bound 7)))
      Examples.localBody).checkClosed = false := by decide

/-- A closed value with its own local resource scope is accepted, then moves
through arbitrary annotated terms and arbitrary later environments. -/
theorem local_value_transport (target : Term) (name : Nat) (environment : Environment) :
    (target.subst name localValue).instantiate environment =
      (target.instantiate environment).subst name localValue :=
  target.instantiation_subst name localValue environment (Term.check_closed_iff.mp local_resource_value_accepted)

theorem opening_local_body_closes_metadata :
    (Examples.localBody.instantiate (Environment.empty.bind 7 29)).ResourceClosed :=
  Term.acquisition_closes_body (by rfl : (Term.resource .unit 7 Examples.unit Examples.localBody).ResourceClosed)
    Environment.empty 29

theorem closed_value_satisfies_old_closure : localValue.erase.ResourceClosed :=
  Term.closed_erasure (Term.check_closed_iff.mp local_resource_value_accepted)

end NameExamples

end Ash.OneShot.SourceAnnotatedCode

#print axioms Ash.OneShot.SourceAnnotatedCode.names_map_identity
#print axioms Ash.OneShot.SourceAnnotatedCode.hint_instantiation_identity
#print axioms Ash.OneShot.SourceAnnotatedCode.names_map_free
#print axioms Ash.OneShot.SourceAnnotatedCode.hint_instantiation_free
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.instantiation_free
#print axioms Ash.OneShot.SourceAnnotatedCode.Clauses.instantiation_free
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.instantiation_identity
#print axioms Ash.OneShot.SourceAnnotatedCode.Clauses.instantiation_identity
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.check_closed_iff
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.instantiation_closes_iff
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.closed_instantiation_identity
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.closed_erasure

#print axioms Ash.OneShot.SourceAnnotatedCode.Term.instantiation_subst
#print axioms Ash.OneShot.SourceAnnotatedCode.Clauses.instantiation_subst
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.acquisition_closes_body
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.closed_hint_fixed
#print axioms Ash.OneShot.SourceAnnotatedCode.Term.closed_frame_check_fixed
#print axioms Ash.OneShot.SourceAnnotatedCode.NameExamples.all_function_metadata_counted
#print axioms Ash.OneShot.SourceAnnotatedCode.NameExamples.previous_open_metadata_rejected
#print axioms Ash.OneShot.SourceAnnotatedCode.NameExamples.local_resource_value_accepted
#print axioms Ash.OneShot.SourceAnnotatedCode.NameExamples.result_hint_is_outside_resource_scope
#print axioms Ash.OneShot.SourceAnnotatedCode.NameExamples.initial_scope_is_outside_resource_binder
#print axioms Ash.OneShot.SourceAnnotatedCode.NameExamples.local_value_transport
#print axioms Ash.OneShot.SourceAnnotatedCode.NameExamples.opening_local_body_closes_metadata
#print axioms Ash.OneShot.SourceAnnotatedCode.NameExamples.closed_value_satisfies_old_closure
