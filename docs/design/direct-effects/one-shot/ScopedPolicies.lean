import ScopedActions

/-!
Whole-expression action policy synthesis for the structural usage judgment.
The finite profile includes clauses inside functions and other clauses. Reused
keys join requirements; exact per-clause contracts require coherent identities.
No capture-safety or Core extraction theorem is assumed or claimed.
-/

namespace Ash.OneShot.ActionPolicies
open Syntax ActionRequirements

abbrev Profile := List (Nat × OneShotRights)

mutual
def entries : Expr → Profile
  | .unit | .boolean _ | .integer _ | .variable _ | .resourceRef _ | .discard _ => []
  | .pair left right | .app left right | .bind _ left right
  | .resource _ left right | .cleanup left right => entries left ++ entries right
  | .lambda _ body | .perform _ _ body | .resume _ body => entries body
  | .branch condition yes no => entries condition ++ (entries yes ++ entries no)
  | .handle _ body clauses => entries body ++ clauseEntries clauses

def clauseEntries : Clauses → Profile
  | .nil => []
  | .cons _ _ binder body rest => (binder, required body) :: (entries body ++ clauseEntries rest)
end

def Covers (policy : TicketPolicy) (profile : Profile) : Prop :=
  ∀ entry ∈ profile, Below entry.2 (policy entry.1)

theorem covers_nil (policy : TicketPolicy) : Covers policy [] := by
  intro _ impossible; cases impossible

theorem covers_append : Covers policy (left ++ right) ↔ Covers policy left ∧ Covers policy right := by
  simp only [Covers, List.mem_append]
  constructor
  · intro checked; exact ⟨fun e h => checked e (.inl h), fun e h => checked e (.inr h)⟩
  · intro ⟨left, right⟩ e h; exact h.elim (left e) (right e)

theorem covers_cons : Covers policy (entry :: rest) ↔ Below entry.2 (policy entry.1) ∧ Covers policy rest := by
  constructor
  · intro checked; exact ⟨checked _ (by simp), fun e h => checked e (by simp [h])⟩
  · intro ⟨head, tail⟩ e member
    cases List.mem_cons.mp member with
    | inl same => subst e; exact head
    | inr h => exact tail e h

theorem usage_covers_profile (checked : Uses policy scope before expression after) :
    Covers policy (entries expression) := by
  induction checked using Uses.rec (motive_2 := fun clauses _ => Covers policy (clauseEntries clauses)) with
  | unit | boolean | integer | «variable» | resourceRef | discard => exact covers_nil _
  | pair _ _ left right | app _ _ left right | bind _ _ left right
  | resource _ _ left right | cleanup _ _ left right | handle _ _ left right =>
    exact covers_append.mpr ⟨left, right⟩
  | branch _ _ _ condition yes no => exact covers_append.mpr ⟨condition, covers_append.mpr ⟨yes, no⟩⟩
  | lambda _ body | perform _ body | resume _ _ body => exact body
  | nil => exact covers_nil _
  | cons body _ inside rest =>
    exact covers_cons.mpr ⟨usage_requires_actions body, covers_append.mpr ⟨inside, rest⟩⟩

/-- Every nested clause is rechecked under the new policy. Enclosing permissions
    and usage states remain fixed; the existing derivation supplies validity. -/
theorem usage_change_policy (checked : Uses policy scope before expression after) :
    ∀ next, Covers next (entries expression) → Uses next scope before expression after := by
  induction checked using Uses.rec
      (motive_2 := fun clauses _ => ∀ next, Covers next (clauseEntries clauses) → ClausesUse next clauses) with
  | unit => intros; exact .unit
  | boolean => intros; exact .boolean
  | integer => intros; exact .integer
  | «variable» => intros; exact .variable
  | resourceRef => intros; exact .resourceRef
  | discard allowed => intros; exact .discard allowed
  | pair _ _ left right =>
    intro next bound; obtain ⟨l, r⟩ := covers_append.mp bound
    exact .pair (left next l) (right next r)
  | app _ _ left right =>
    intro next bound; obtain ⟨l, r⟩ := covers_append.mp bound
    exact .app (left next l) (right next r)
  | bind _ _ left right =>
    intro next bound; obtain ⟨l, r⟩ := covers_append.mp bound
    exact .bind (left next l) (right next r)
  | resource _ _ left right =>
    intro next bound; obtain ⟨l, r⟩ := covers_append.mp bound
    exact .resource (left next l) (right next r)
  | cleanup _ _ left right =>
    intro next bound; obtain ⟨l, r⟩ := covers_append.mp bound
    exact .cleanup (left next l) (right next r)
  | handle _ _ left right =>
    intro next bound; obtain ⟨l, r⟩ := covers_append.mp bound
    exact .handle (left next l) (right next r)
  | branch _ _ _ condition yes no =>
    intro next bound; obtain ⟨c, yn⟩ := covers_append.mp bound
    obtain ⟨y, n⟩ := covers_append.mp yn
    exact .branch (condition next c) (yes next y) (no next n)
  | lambda _ body => intro next bound; exact .lambda (body next bound)
  | perform _ body => intro next bound; exact .perform (body next bound)
  | resume allowed _ body => intro next bound; exact .resume allowed (body next bound)
  | nil => intros; exact .nil
  | cons _ _ body rest next bound =>
    obtain ⟨own, nested⟩ := covers_cons.mp bound
    obtain ⟨inside, outside⟩ := covers_append.mp nested
    exact .cons (usage_repermission (body next inside) _ .ticket own) (rest next outside)

def infer : Profile → TicketPolicy
  | [] => fun _ => ActionRequirements.none
  | (key, rights) :: rest => fun binder =>
    if key = binder then join rights (infer rest binder) else infer rest binder

theorem infer_bound (profile : Profile) (binder : Nat) :
    Below (infer profile binder) granted ↔
      ∀ rights, (binder, rights) ∈ profile → Below rights granted := by
  induction profile with
  | nil => simp [infer, none_below]
  | cons entry rest ih =>
    obtain ⟨key, rights⟩ := entry
    by_cases same : key = binder
    · subst key
      simp only [infer, ↓reduceIte, join_below, ih, List.mem_cons, Prod.mk.injEq, true_and]
      constructor
      · intro ⟨head, tail⟩ r member
        cases member with
        | inl eq => subst r; exact head
        | inr h => exact tail r h
      · intro all
        exact ⟨all rights (.inl rfl), fun r h => all r (.inr h)⟩
    · have different : binder ≠ key := Ne.symm same
      simp only [infer, same, ↓reduceIte, ih, List.mem_cons, Prod.mk.injEq, different, false_and, false_or]

theorem inferred_covers (profile : Profile) : Covers (infer profile) profile := by
  intro entry member
  exact (infer_bound profile entry.1).mp (below_refl _) entry.2 member

theorem inferred_least (covered : Covers policy profile) : ∀ binder, Below (infer profile binder) (policy binder) := by
  intro binder
  exact (infer_bound profile binder).mpr (fun rights member => covered _ member)

theorem synthesized_usage (checked : Uses policy scope before expression after) :
    Uses (infer (entries expression)) scope before expression after :=
  usage_change_policy checked _ (inferred_covers _)

theorem least_whole_policy (checked : Uses policy scope before expression after) :
    Uses (infer (entries expression)) scope before expression after ∧
      ∀ alternative, Uses alternative scope before expression after →
        ∀ binder, Below (infer (entries expression) binder) (alternative binder) :=
  ⟨synthesized_usage checked, fun _ other => inferred_least (usage_covers_profile other)⟩

theorem below_antisymm (forward : Below left right) (backward : Below right left) : left = right := by
  obtain ⟨lr, ld⟩ := left
  obtain ⟨rr, rd⟩ := right
  cases lr <;> cases ld <;> cases rr <;> cases rd <;> simp_all [Below]

/-- Repeated occurrences are harmless when their local requirements agree.
    This permits copies of the same function body without assuming unique syntax. -/
def Coherent (profile : Profile) : Prop :=
  ∀ binder left right, (binder, left) ∈ profile → (binder, right) ∈ profile → left = right

theorem inferred_exact (coherent : Coherent profile) (member : (binder, rights) ∈ profile) :
    infer profile binder = rights := by
  apply below_antisymm
  · apply (infer_bound profile binder).mpr
    intro other present
    rw [coherent binder other rights present member]
    exact below_refl _
  · exact inferred_covers profile _ member

theorem distinct_keys_coherent (distinct : (profile.map Prod.fst).Nodup) : Coherent profile := by
  induction profile with
  | nil => intro _ _ _ impossible; cases impossible
  | cons entry rest ih =>
    obtain ⟨key, own⟩ := entry
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    intro binder left right lm rm
    cases List.mem_cons.mp lm with
    | inl same =>
      cases same
      cases List.mem_cons.mp rm with
      | inl same => exact (Prod.mk.inj same).2.symm
      | inr member => exact False.elim (fresh (List.mem_map.mpr ⟨_, member, rfl⟩))
    | inr member =>
      cases List.mem_cons.mp rm with
      | inl same =>
        cases same
        exact False.elim (fresh (List.mem_map.mpr ⟨_, member, rfl⟩))
      | inr other => exact ih tail binder left right member other

theorem coherent_subset (coherent : Coherent whole) (included : profile ⊆ whole) : Coherent profile :=
  fun binder left right lm rm => coherent binder left right (included lm) (included rm)

theorem shared_substitution_bound
    {newLeft newRight oldLeft oldRight shared : Profile}
    (left : newLeft ⊆ oldLeft ++ shared) (right : newRight ⊆ oldRight ++ shared) :
    newLeft ++ newRight ⊆ (oldLeft ++ oldRight) ++ shared := by
  intro entry member
  cases List.mem_append.mp member with
  | inl h =>
    cases List.mem_append.mp (left h) with
    | inl old => exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl old)))
    | inr retained => exact List.mem_append.mpr (.inr retained)
  | inr h =>
    cases List.mem_append.mp (right h) with
    | inl old => exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr old)))
    | inr retained => exact List.mem_append.mpr (.inr retained)

mutual
theorem substitution_profile_bound (expression : Expr) (name : Nat) (value : replacement.IsValue) :
    entries (expression.subst name replacement) ⊆ entries expression ++ entries replacement := by
  cases expression with
  | unit | boolean | integer | resourceRef | discard => exact List.nil_subset _
  | «variable» other =>
    simp only [Expr.subst]
    split
    · exact List.Subset.refl _
    · exact List.nil_subset _
  | pair left right | app left right | resource _ left right | cleanup left right =>
    exact shared_substitution_bound (substitution_profile_bound left name value)
      (substitution_profile_bound right name value)
  | lambda parameter body =>
    simp only [Expr.subst, entries]
    split
    · exact List.subset_append_left _ _
    · exact substitution_profile_bound body name value
  | bind parameter initializer body =>
    simp only [Expr.subst, entries]
    split
    · exact shared_substitution_bound (substitution_profile_bound initializer name value) (List.subset_append_left _ _)
    · exact shared_substitution_bound (substitution_profile_bound initializer name value)
        (substitution_profile_bound body name value)
  | branch condition yes no =>
    exact shared_substitution_bound (substitution_profile_bound condition name value)
      (shared_substitution_bound (substitution_profile_bound yes name value) (substitution_profile_bound no name value))
  | perform _ _ body | resume _ body => exact substitution_profile_bound body name value
  | handle _ body clauses =>
    exact shared_substitution_bound (substitution_profile_bound body name value)
      (substitution_clause_profile_bound clauses name value)
termination_by sizeOf expression

theorem substitution_clause_profile_bound (clauses : Clauses) (name : Nat) (value : replacement.IsValue) :
    clauseEntries (clauses.subst name replacement) ⊆ clauseEntries clauses ++ entries replacement := by
  cases clauses with
  | nil => exact List.nil_subset _
  | cons operation parameter binder body rest =>
    simp only [Clauses.subst, clauseEntries]
    split
    · intro entry member
      cases List.mem_cons.mp member with
      | inl same => subst entry; exact List.mem_append.mpr (.inl (by simp))
      | inr nested =>
        have included := shared_substitution_bound (List.subset_append_left _ _)
          (substitution_clause_profile_bound rest name value) nested
        cases List.mem_append.mp included with
        | inl old => exact List.mem_append.mpr (.inl (List.mem_cons_of_mem _ old))
        | inr retained => exact List.mem_append.mpr (.inr retained)
    · rw [substitution_required_actions body name value]
      intro entry member
      cases List.mem_cons.mp member with
      | inl same => subst entry; exact List.mem_append.mpr (.inl (by simp))
      | inr nested =>
        have included := shared_substitution_bound (substitution_profile_bound body name value)
          (substitution_clause_profile_bound rest name value) nested
        cases List.mem_append.mp included with
        | inl old => exact List.mem_append.mpr (.inl (List.mem_cons_of_mem _ old))
        | inr retained => exact List.mem_append.mpr (.inr retained)
termination_by sizeOf clauses
end

theorem substitution_preserves_profile_coherence
    (coherent : Coherent (entries expression ++ entries replacement)) (value : replacement.IsValue) :
    Coherent (entries (expression.subst name replacement)) :=
  coherent_subset coherent (substitution_profile_bound expression name value)

end Ash.OneShot.ActionPolicies

namespace Ash.OneShot.ScopedExpressions
open ActionPolicies ActionRequirements

def Code.actionProfile (code : Code) : Profile := entries code.usageShape
def Code.inferredPolicy (code : Code) : Syntax.TicketPolicy := infer code.actionProfile

theorem scoped_synthesized_usage (checked : Uses policy scope before code after) :
    Uses code.inferredPolicy scope before code after := synthesized_usage checked

theorem scoped_least_whole_policy (checked : Uses policy scope before code after) :
    Uses code.inferredPolicy scope before code after ∧
      ∀ alternative, Uses alternative scope before code after →
        ∀ binder, Below (code.inferredPolicy binder) (alternative binder) := least_whole_policy checked

theorem scoped_inferred_exact {code : Code} (coherent : Coherent code.actionProfile)
    (member : (binder, rights) ∈ code.actionProfile) : code.inferredPolicy binder = rights :=
  inferred_exact coherent member

@[simp] theorem Code.instantiation_action_profile (code : Code) (environment : Instantiation.Environment) :
    (code.instantiate environment).actionProfile = code.actionProfile := by
  simp only [Code.actionProfile, Code.instantiation_usage_shape]

@[simp] theorem Code.instantiation_inferred_policy (code : Code) (environment : Instantiation.Environment) :
    (code.instantiate environment).inferredPolicy = code.inferredPolicy := by
  simp only [Code.inferredPolicy, Code.instantiation_action_profile]

theorem Code.substitution_action_profile_bound (code : Code) (name : Nat) (value : replacement.IsValue) :
    (code.subst name replacement).actionProfile ⊆ code.actionProfile ++ replacement.actionProfile := by
  simp only [Code.actionProfile, Code.substitution_usage_shape]
  exact substitution_profile_bound code.usageShape name (value_usage_shape value)

theorem Code.substitution_profile_coherence
    {code replacement : Code}
    (coherent : Coherent (code.actionProfile ++ replacement.actionProfile)) (value : replacement.IsValue) :
    Coherent (code.subst name replacement).actionProfile :=
  coherent_subset coherent (Code.substitution_action_profile_bound code name value)

theorem initial_ready_with_synthesized_policy
    (typed : ScopedTyping.Typed signature [] Typing.TypeEnv.empty .none outgoing code result)
    (used : Uses policy .none .available code .available)
    (support : Syntax.resourceDependencies code.dependencies = []) :
    ScopedPrepared.Ready signature code.inferredPolicy (fun _ => Option.none) []
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ result outgoing :=
  ScopedPrepared.initial_ready typed (scoped_synthesized_usage used) support

namespace PolicyExamples
open ActionExamples

def distinctSource : Code := .handle (Instantiation.freezeEffect (.user 1 [])) .unit
  (.cons 0 1 9 nestedClause .nil)

theorem distinct_source_profile : distinctSource.actionProfile = [(9, resumeOnly), (11, disposeOnly)] := rfl

theorem distinct_source_contracts : distinctSource.inferredPolicy 9 = resumeOnly ∧
    distinctSource.inferredPolicy 11 = disposeOnly ∧ distinctSource.inferredPolicy 12 = ActionRequirements.none :=
  ⟨rfl, rfl, rfl⟩

theorem distinct_source_coherent : Coherent distinctSource.actionProfile :=
  distinct_keys_coherent (by decide)

theorem distinct_source_checked : Uses distinctSource.inferredPolicy .none .available distinctSource .available :=
  .handle .unit (.cons (.bind (.handle .unit (.cons (.discard rfl) .nil)) (.resume rfl .unit)) .nil)

def repeatedFunction : Code := .lambda 0 distinctSource
def copiedFunctions : Code := (Code.pair (.variable 5) (.variable 5)).subst 5 repeatedFunction

theorem copied_profile_coherent : Coherent copiedFunctions.actionProfile := by
  apply Code.substitution_profile_coherence (code := .pair (.variable 5) (.variable 5))
    (replacement := repeatedFunction) (name := 5)
  · exact distinct_source_coherent
  · trivial

theorem copied_profile_not_unique : ¬ (copiedFunctions.actionProfile.map Prod.fst).Nodup := by decide

theorem copied_policy_exact : copiedFunctions.inferredPolicy 9 = resumeOnly ∧
    copiedFunctions.inferredPolicy 11 = disposeOnly := ⟨rfl, rfl⟩

theorem copied_functions_checked : Uses copiedFunctions.inferredPolicy .none .available copiedFunctions .available :=
  scoped_synthesized_usage (code := copiedFunctions)
    (.pair (.lambda distinct_source_checked) (.lambda distinct_source_checked))

def collidingSource : Code := .handle (Instantiation.freezeEffect (.user 1 [])) .unit sharedBinderClauses

theorem collision_joins_authority : collidingSource.inferredPolicy 9 = ⟨true, true⟩ := rfl

theorem collision_not_coherent : ¬ Coherent collidingSource.actionProfile := by
  intro coherent
  have impossible := coherent 9 resumeOnly disposeOnly (by decide) (by decide)
  cases impossible

abbrev runningSource := ScopedPrepared.Examples.source.execution.configuration.expression

theorem running_source_profile : runningSource.actionProfile = [(9, resumeOnly)] := rfl

theorem running_source_checked : Uses runningSource.inferredPolicy .none .available runningSource .available :=
  .handle (.cleanup (.lambda (.perform .unit)) .unit) (.cons (.resume rfl .unit) .nil)

theorem running_source_ready : ScopedPrepared.Ready ScopedPrepared.Examples.signature runningSource.inferredPolicy
    ScopedPrepared.Examples.emptyRegistry [] ScopedPrepared.Examples.source .unit [] := by
  exact ScopedPrepared.initial_ready
    (.handle (.cleanup ScopedPrepared.Examples.callback_typed .unit (List.Subset.refl _))
      ScopedPrepared.Examples.clauses_typed ScopedPrepared.Examples.handler_coverage (by decide) (List.nil_subset _))
    running_source_checked rfl

theorem running_policy_forbids_dispose (binder : Nat) : (runningSource.inferredPolicy binder).dispose = false := by
  change (infer [(9, resumeOnly)] binder).dispose = false
  simp only [infer]
  split <;> rfl

theorem running_before_ready : ScopedPrepared.Ready ScopedPrepared.Examples.signature runningSource.inferredPolicy
    ScopedPrepared.Examples.emptyRegistry [] ScopedPrepared.Examples.before .unit [] := by
  have control : ScopedExecution.StackUsage runningSource.inferredPolicy ScopedPrepared.Examples.emptyRegistry.usage
      ScopedPrepared.Examples.cap [] [] :=
    .push (.running ⟨_, .none⟩ (.lambda (.perform .unit)) .unit) (List.nil_subset _)
      (.push (.handler ⟨_, .none⟩ (.cons (.resume rfl .unit) .nil)) (List.nil_subset _) .nil)
  have old := ScopedPrepared.Examples.before_ready false
  exact ⟨{ old.joint with usage :=
    ⟨[], [], .idle .none (.perform .unit), control, List.nil_subset _, .refl [], by decide⟩ }, old.closing⟩

/-- The policy comes from the entire source expression. Actual capture uses the
    resulting registry permissions; no arbitrary policy remains in this example. -/
theorem running_capture_with_synthesized_policy :
    ScopedPrepared.Ready ScopedPrepared.Examples.signature runningSource.inferredPolicy
      ScopedPrepared.Examples.emptyRegistry [] ScopedPrepared.Examples.source .unit [] ∧
    ScopedExecution.NamedAccessSteps [] ScopedPrepared.Examples.source ScopedPrepared.Examples.before ∧
      ∃ next after, ScopedExecution.NamedAccessStep [] ScopedPrepared.Examples.before after ∧
        ScopedPrepared.Ready ScopedPrepared.Examples.signature runningSource.inferredPolicy next [] after .unit [] := by
  obtain ⟨parameter, binder, body, output, residual, step, _, obligation⟩ :=
    ScopedPrepared.capture_constructs_ready_obligation ScopedPrepared.Examples.actual_cut running_before_ready
      trivial (owner := 3) (by decide) ScopedPrepared.Examples.before_access_checks
  refine ⟨running_source_ready, ScopedPrepared.Examples.source_reaches_running_request, _, _, step, obligation ?_⟩
  intro denied
  rw [running_policy_forbids_dispose] at denied
  cases denied

end PolicyExamples

end Ash.OneShot.ScopedExpressions

#print axioms Ash.OneShot.ActionPolicies.covers_nil
#print axioms Ash.OneShot.ActionPolicies.covers_append
#print axioms Ash.OneShot.ActionPolicies.covers_cons
#print axioms Ash.OneShot.ActionPolicies.usage_covers_profile
#print axioms Ash.OneShot.ActionPolicies.usage_change_policy
#print axioms Ash.OneShot.ActionPolicies.infer_bound
#print axioms Ash.OneShot.ActionPolicies.inferred_covers
#print axioms Ash.OneShot.ActionPolicies.inferred_least
#print axioms Ash.OneShot.ActionPolicies.synthesized_usage
#print axioms Ash.OneShot.ActionPolicies.least_whole_policy
#print axioms Ash.OneShot.ActionPolicies.below_antisymm
#print axioms Ash.OneShot.ActionPolicies.inferred_exact
#print axioms Ash.OneShot.ActionPolicies.distinct_keys_coherent
#print axioms Ash.OneShot.ActionPolicies.coherent_subset
#print axioms Ash.OneShot.ActionPolicies.shared_substitution_bound
#print axioms Ash.OneShot.ActionPolicies.substitution_profile_bound
#print axioms Ash.OneShot.ActionPolicies.substitution_clause_profile_bound
#print axioms Ash.OneShot.ActionPolicies.substitution_preserves_profile_coherence
#print axioms Ash.OneShot.ScopedExpressions.scoped_synthesized_usage
#print axioms Ash.OneShot.ScopedExpressions.scoped_least_whole_policy
#print axioms Ash.OneShot.ScopedExpressions.scoped_inferred_exact
#print axioms Ash.OneShot.ScopedExpressions.Code.instantiation_action_profile
#print axioms Ash.OneShot.ScopedExpressions.Code.instantiation_inferred_policy
#print axioms Ash.OneShot.ScopedExpressions.Code.substitution_action_profile_bound
#print axioms Ash.OneShot.ScopedExpressions.Code.substitution_profile_coherence
#print axioms Ash.OneShot.ScopedExpressions.initial_ready_with_synthesized_policy
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.distinct_source_profile
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.distinct_source_contracts
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.distinct_source_coherent
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.distinct_source_checked
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.copied_profile_coherent
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.copied_profile_not_unique
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.copied_policy_exact
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.copied_functions_checked
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.collision_joins_authority
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.collision_not_coherent
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.running_source_profile
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.running_source_checked
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.running_source_ready
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.running_policy_forbids_dispose
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.running_before_ready
#print axioms Ash.OneShot.ScopedExpressions.PolicyExamples.running_capture_with_synthesized_policy
