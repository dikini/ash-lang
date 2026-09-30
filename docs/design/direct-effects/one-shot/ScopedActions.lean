import ScopedPrepared

/-!
Least action requirements for the enclosing continuation in the structural usage
judgment. Nested clauses keep their independently checked policy. This does not
infer capture safety, permission to retire nested tickets, or a global Core policy.
-/

namespace Ash.OneShot.ActionRequirements
open Syntax

def none : OneShotRights := ⟨false, false⟩
def resumeOnly : OneShotRights := ⟨true, false⟩
def disposeOnly : OneShotRights := ⟨false, true⟩
def join (left right : OneShotRights) : OneShotRights :=
  ⟨left.resume || right.resume, left.dispose || right.dispose⟩

def Below (needed granted : OneShotRights) : Prop :=
  (needed.resume = true → granted.resume = true) ∧
    (needed.dispose = true → granted.dispose = true)

theorem below_refl (rights : OneShotRights) : Below rights rights := ⟨id, id⟩
theorem none_below (rights : OneShotRights) : Below none rights := by
  constructor <;> intro impossible <;> cases impossible

theorem join_below : Below (join left right) granted ↔ Below left granted ∧ Below right granted := by
  simp only [Below, join, Bool.or_eq_true]
  constructor
  · intro ⟨resume, dispose⟩
    exact ⟨⟨fun h => resume (.inl h), fun h => dispose (.inl h)⟩,
      ⟨fun h => resume (.inr h), fun h => dispose (.inr h)⟩⟩
  · intro ⟨⟨lr, ld⟩, ⟨rr, rd⟩⟩
    exact ⟨fun h => h.elim lr rr, fun h => h.elim ld rd⟩

theorem resume_below : Below resumeOnly granted ↔ granted.resume = true := by
  simp [Below, resumeOnly]

theorem dispose_below : Below disposeOnly granted ↔ granted.dispose = true := by
  simp [Below, disposeOnly]

/-- Both branch arms count. Function bodies and nested clauses are checked in
    separate scopes; their ticket actions do not belong to this enclosing ticket. -/
def required : Expr → OneShotRights
  | .unit | .boolean _ | .integer _ | .variable _ | .resourceRef _ | .lambda _ _ => none
  | .pair left right | .app left right | .bind _ left right
  | .resource _ left right | .cleanup left right => join (required left) (required right)
  | .branch condition yes no => join (required condition) (join (required yes) (required no))
  | .perform _ _ operand => required operand
  | .handle _ body _ => required body
  | .resume _ operand => join resumeOnly (required operand)
  | .discard _ => disposeOnly

def scopeRights : UseScope → OneShotRights
  | .none => none
  | .ticket _ rights => rights

theorem usage_requires_actions (checked : Uses policy scope before expression after) :
    Below (required expression) (scopeRights scope) := by
  induction checked using Uses.rec (motive_2 := fun _ _ => True) with
  | unit | boolean | integer | «variable» | resourceRef | lambda => exact none_below _
  | pair _ _ left right | app _ _ left right | bind _ _ left right
  | resource _ _ left right | cleanup _ _ left right => exact join_below.mpr ⟨left, right⟩
  | branch _ _ _ condition yes no => exact join_below.mpr ⟨condition, join_below.mpr ⟨yes, no⟩⟩
  | perform _ operand | handle _ _ operand clauses => exact operand
  | resume allowed _ operand => exact join_below.mpr ⟨resume_below.mpr allowed, operand⟩
  | discard allowed => exact dispose_below.mpr allowed
  | nil | cons => trivial

inductive SameBinder : UseScope → UseScope → Prop where
  | none : SameBinder .none .none
  | ticket : SameBinder (.ticket binder old) (.ticket binder new)

/-- Change only the enclosing ticket's permissions, preserving its binder, usage
    states, and all independently checked nested clause permissions. -/
theorem usage_repermission (checked : Uses policy scope before expression after) :
    ∀ destination, SameBinder scope destination → Below (required expression) (scopeRights destination) →
      Uses policy destination before expression after := by
  induction checked using Uses.rec (motive_2 := fun _ _ => True) with
  | unit => intros; exact .unit
  | boolean => intros; exact .boolean
  | integer => intros; exact .integer
  | «variable» => intros; exact .variable
  | resourceRef => intros; exact .resourceRef
  | lambda body _ => intros; exact .lambda body
  | pair _ _ left right =>
    intro destination same bound
    exact .pair (left destination same (join_below.mp bound).1) (right destination same (join_below.mp bound).2)
  | app _ _ left right =>
    intro destination same bound
    exact .app (left destination same (join_below.mp bound).1) (right destination same (join_below.mp bound).2)
  | bind _ _ left right =>
    intro destination same bound
    exact .bind (left destination same (join_below.mp bound).1) (right destination same (join_below.mp bound).2)
  | resource _ _ left right =>
    intro destination same bound
    exact .resource (left destination same (join_below.mp bound).1) (right destination same (join_below.mp bound).2)
  | cleanup _ _ left right =>
    intro destination same bound
    exact .cleanup (left destination same (join_below.mp bound).1) (right destination same (join_below.mp bound).2)
  | branch _ _ _ condition yes no =>
    intro destination same bound
    obtain ⟨c, yn⟩ := join_below.mp bound
    obtain ⟨y, n⟩ := join_below.mp yn
    exact .branch (condition destination same c) (yes destination same y) (no destination same n)
  | perform _ operand =>
    intro destination same bound
    exact .perform (operand destination same bound)
  | handle _ clauses body _ =>
    intro destination same bound
    exact .handle (body destination same bound) clauses
  | resume _ _ operand =>
    intro destination same bound
    cases same with
    | ticket =>
      obtain ⟨permission, argument⟩ := join_below.mp bound
      exact .resume (resume_below.mp permission) (operand _ .ticket argument)
  | discard _ =>
    intro destination same bound
    cases same with
    | ticket => exact .discard (dispose_below.mp bound)
  | nil | cons => trivial

/-- Least permission bound among derivations with the same policy, binder and
    usage states. A prior derivation supplies scope and consumption validity. -/
theorem least_enclosing_actions
    (checked : Uses policy (.ticket binder granted) before expression after) :
    Uses policy (.ticket binder (required expression)) before expression after ∧
      ∀ alternative, Uses policy (.ticket binder alternative) before expression after →
        Below (required expression) alternative :=
  ⟨usage_repermission checked _ .ticket (below_refl _), fun _ other => usage_requires_actions other⟩

theorem value_requires_no_enclosing_actions (value : expression.IsValue) : required expression = none := by
  cases expression with
  | unit | boolean | integer | resourceRef | lambda => rfl
  | pair left right =>
    simp only [required, value_requires_no_enclosing_actions value.1,
      value_requires_no_enclosing_actions value.2]
    rfl
  | «variable» | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases value
termination_by sizeOf expression

/-- Value substitution cannot add actions on the enclosing ticket. Nested
    clauses inside a substituted function still require their own policy checks. -/
theorem substitution_required_actions (expression : Expr) (name : Nat) (value : replacement.IsValue) :
    required (expression.subst name replacement) = required expression := by
  cases expression with
  | unit | boolean | integer | resourceRef | lambda | discard => rfl
  | «variable» other =>
    simp only [Expr.subst]
    split
    · exact value_requires_no_enclosing_actions value
    · rfl
  | pair left right | app left right | resource _ left right | cleanup left right =>
    simp only [Expr.subst, required, substitution_required_actions left name value,
      substitution_required_actions right name value]
  | bind parameter initializer body =>
    simp only [Expr.subst, required, substitution_required_actions initializer name value]
    split <;> simp only [substitution_required_actions body name value]
  | branch condition yes no =>
    simp only [Expr.subst, required, substitution_required_actions condition name value,
      substitution_required_actions yes name value, substitution_required_actions no name value]
  | perform _ _ operand | resume _ operand | handle _ operand _ =>
    simp only [Expr.subst, required, substitution_required_actions operand name value]
termination_by sizeOf expression

end Ash.OneShot.ActionRequirements

namespace Ash.OneShot.ScopedExpressions
open Syntax (OneShotRights)
open ActionRequirements

def Code.requiredActions (code : Code) : OneShotRights := required code.usageShape

theorem scoped_usage_requires_actions (checked : Uses policy scope before code after) :
    Below code.requiredActions (scopeRights scope) := usage_requires_actions checked

theorem scoped_usage_repermission (checked : Uses policy scope before code after)
    (same : SameBinder scope destination) (bound : Below code.requiredActions (scopeRights destination)) :
    Uses policy destination before code after := usage_repermission checked destination same bound

theorem scoped_least_enclosing_actions
    (checked : Uses policy (.ticket binder granted) before code after) :
    Uses policy (.ticket binder code.requiredActions) before code after ∧
      ∀ alternative, Uses policy (.ticket binder alternative) before code after →
        Below code.requiredActions alternative := least_enclosing_actions checked

@[simp] theorem Code.instantiation_required_actions (code : Code) (environment : Instantiation.Environment) :
    (code.instantiate environment).requiredActions = code.requiredActions := by
  simp only [Code.requiredActions, Code.instantiation_usage_shape]

theorem Code.substitution_required_actions (code : Code) (name : Nat) (value : replacement.IsValue) :
    (code.subst name replacement).requiredActions = code.requiredActions := by
  simp only [Code.requiredActions, Code.substitution_usage_shape,
    ActionRequirements.substitution_required_actions _ name (value_usage_shape value)]

namespace ActionExamples

def resumeClause : Code := .resume 9 .unit
def discardClause : Code := .discard 9
def mixedClause : Code := .branch (.boolean true) resumeClause discardClause
def nestedClause : Code := .bind 0
  (.handle (Instantiation.freezeEffect (.user 2 [])) .unit (.cons 0 1 11 (.discard 11) .nil))
  resumeClause

theorem resume_requirement : resumeClause.requiredActions = resumeOnly := rfl
theorem discard_requirement : discardClause.requiredActions = disposeOnly := rfl
theorem mixed_requirement : mixedClause.requiredActions = ⟨true, true⟩ := rfl
theorem nested_requirement : nestedClause.requiredActions = resumeOnly := rfl

theorem mixed_clause_checked : Uses (fun _ => none) (.ticket 9 mixedClause.requiredActions)
    .available mixedClause .consumed := .branch .boolean (.resume rfl .unit) (.discard rfl)

theorem mixed_clause_needs_both (checked : Uses policy (.ticket 9 rights) .available mixedClause .consumed) :
    rights.resume = true ∧ rights.dispose = true := by
  have bound := scoped_usage_requires_actions checked
  exact ⟨bound.1 rfl, bound.2 rfl⟩

def nestedPolicy : Syntax.TicketPolicy := fun _ => disposeOnly

theorem nested_clause_checked : Uses nestedPolicy (.ticket 9 nestedClause.requiredActions)
    .available nestedClause .consumed :=
  .bind (.handle .unit (.cons (.discard rfl) .nil)) (.resume rfl .unit)

theorem insufficient_nested_policy :
    ¬ Uses (fun _ => resumeOnly) (.ticket 9 nestedClause.requiredActions) .available nestedClause .consumed := by
  intro checked
  cases checked with
  | bind first _ =>
    cases first with
    | handle _ clauses =>
      cases clauses with
      | cons body _ =>
        cases body with
        | discard impossible => cases impossible

/-- The computed flag bound does not check the ticket's lexical identity. -/
theorem wrong_binder_still_rejected :
    ¬ Uses policy (.ticket 8 resumeClause.requiredActions) .available resumeClause .consumed := by
  intro checked
  cases checked

theorem double_completion_still_rejected :
    ¬ Uses policy (.ticket 9 resumeOnly) .available (.bind 0 resumeClause resumeClause) .consumed := by
  intro checked
  cases checked with
  | bind first second =>
    cases first with
    | resume _ operand =>
      cases second with
      | resume _ argument => cases argument

theorem function_capture_still_rejected :
    (.lambda 0 resumeClause : Code).requiredActions = ActionRequirements.none ∧
      ¬ Uses policy (.ticket 9 resumeOnly) .available (.lambda 0 resumeClause) .available := by
  refine ⟨rfl, ?_⟩
  intro checked
  cases checked with
  | lambda body => cases body

def sharedBinderBody : Code := .bind 0
  (.handle (Instantiation.freezeEffect (.user 2 [])) .unit (.cons 0 1 9 (.discard 9) .nil)) resumeClause
def sharedBinderClauses : Clauses := .cons 0 1 9 sharedBinderBody .nil

theorem shared_binder_outer_requirement : sharedBinderBody.requiredActions = resumeOnly := rfl

/-- The current administrative policy identifies reused binder numerals. A
    source mapping must distinguish occurrences to avoid these excess grants. -/
theorem shared_binder_policy_needs_both (checked : ClausesUse policy sharedBinderClauses) :
    (policy 9).resume = true ∧ (policy 9).dispose = true := by
  cases checked with
  | cons body _ =>
    have resume := (scoped_usage_requires_actions (code := sharedBinderBody) body).1 rfl
    cases body with
    | bind first _ =>
      cases first with
      | handle _ clauses =>
        cases clauses with
        | cons nested _ =>
          cases nested with
          | discard allowed => exact ⟨resume, allowed⟩

theorem shared_binder_both_checked : ClausesUse (fun _ => ⟨true, true⟩) sharedBinderClauses :=
  .cons (.bind (.handle .unit (.cons (.discard rfl) .nil)) (.resume rfl .unit)) .nil

def derivedPolicy : Syntax.TicketPolicy := fun _ => resumeClause.requiredActions

theorem derived_policy_matches_example : derivedPolicy = ScopedPrepared.Examples.policy false := rfl

theorem example_has_derived_clause : ScopedPrepared.Examples.handler.clauses =
    .cons 0 1 9 resumeClause .nil := rfl

/-- For this single-clause example, the source-derived action bound selects the
    policy under which actual capture of the running callback preserves Ready. -/
theorem derived_resume_contract_preserves_ready :
    ScopedPrepared.Ready ScopedPrepared.Examples.signature derivedPolicy
        ScopedPrepared.Examples.emptyRegistry [] ScopedPrepared.Examples.source .unit [] ∧
      ScopedExecution.NamedAccessSteps [] ScopedPrepared.Examples.source ScopedPrepared.Examples.before ∧
      ∃ next after, ScopedExecution.NamedAccessStep [] ScopedPrepared.Examples.before after ∧
        ScopedPrepared.Ready ScopedPrepared.Examples.signature derivedPolicy next [] after .unit [] :=
  ⟨ScopedPrepared.Examples.source_ready false, ScopedPrepared.Examples.source_reaches_running_request,
    ScopedPrepared.Examples.resume_only_capture_preserves_ready⟩

end ActionExamples

end Ash.OneShot.ScopedExpressions

#print axioms Ash.OneShot.ActionRequirements.below_refl
#print axioms Ash.OneShot.ActionRequirements.none_below
#print axioms Ash.OneShot.ActionRequirements.join_below
#print axioms Ash.OneShot.ActionRequirements.resume_below
#print axioms Ash.OneShot.ActionRequirements.dispose_below
#print axioms Ash.OneShot.ActionRequirements.usage_requires_actions
#print axioms Ash.OneShot.ActionRequirements.usage_repermission
#print axioms Ash.OneShot.ActionRequirements.least_enclosing_actions
#print axioms Ash.OneShot.ActionRequirements.value_requires_no_enclosing_actions
#print axioms Ash.OneShot.ActionRequirements.substitution_required_actions
#print axioms Ash.OneShot.ScopedExpressions.scoped_usage_requires_actions
#print axioms Ash.OneShot.ScopedExpressions.scoped_usage_repermission
#print axioms Ash.OneShot.ScopedExpressions.scoped_least_enclosing_actions
#print axioms Ash.OneShot.ScopedExpressions.Code.instantiation_required_actions
#print axioms Ash.OneShot.ScopedExpressions.Code.substitution_required_actions
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.resume_requirement
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.discard_requirement
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.mixed_requirement
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.nested_requirement
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.mixed_clause_checked
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.mixed_clause_needs_both
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.nested_clause_checked
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.insufficient_nested_policy
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.wrong_binder_still_rejected
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.double_completion_still_rejected
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.function_capture_still_rejected
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.shared_binder_outer_requirement
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.shared_binder_policy_needs_both
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.shared_binder_both_checked
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.derived_policy_matches_example
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.example_has_derived_clause
#print axioms Ash.OneShot.ScopedExpressions.ActionExamples.derived_resume_contract_preserves_ready
