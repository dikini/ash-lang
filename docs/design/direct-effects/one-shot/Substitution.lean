import Typing

/-!
Environment relevance and typed substitution for the annotated administrative
fragment. These results connect expression typing to local reduction; they do
not by themselves establish reachable capture admission or machine progress.
-/

namespace Ash.OneShot.Typing
open Syntax Execution

/-- Environments need agree only on ordinary variables retained by syntax. -/
def AgreeOn (source destination : TypeEnv) (dependencies : List Dependency) : Prop :=
  ∀ name, Dependency.variable name ∈ dependencies → source name = destination name

theorem agree_left (agree : AgreeOn source destination (left ++ right)) : AgreeOn source destination left :=
  fun _ member => agree _ (List.mem_append_left _ member)

theorem agree_right (agree : AgreeOn source destination (left ++ right)) : AgreeOn source destination right :=
  fun _ member => agree _ (List.mem_append_right _ member)

theorem agree_extend (agree : AgreeOn source destination (without (.variable parameter) dependencies)) :
    AgreeOn (source.extend parameter input) (destination.extend parameter input) dependencies := by
  intro name retained
  by_cases same : name = parameter
  · simp [TypeEnv.extend, same]
  · simp only [TypeEnv.extend, if_neg same]
    exact agree name (mem_without.mpr ⟨retained, by simpa using same⟩)

theorem agree_without_resource
    (agree : AgreeOn source destination (without (.resource identity) dependencies)) :
    AgreeOn source destination dependencies :=
  fun name retained => agree name (mem_without.mpr ⟨retained, by simp⟩)

theorem agree_without_ticket
    (agree : AgreeOn source destination (without (.ticket binder) dependencies)) :
    AgreeOn source destination dependencies :=
  fun name retained => agree name (mem_without.mpr ⟨retained, by simp⟩)

theorem retained_support_congr {dependencies : List Dependency}
    (agree : AgreeOn source destination dependencies) :
    retainedSupport source dependencies = retainedSupport destination dependencies := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      have tailEq := ih (fun name member => agree name (List.mem_cons_of_mem _ member))
      have headEq : retainedSupport source [dependency] = retainedSupport destination [dependency] := by
        cases dependency with
        | resource | ticket => rfl
        | «variable» name =>
            simp only [retainedSupport, List.flatMap_cons, List.flatMap_nil, List.append_nil,
              agree name List.mem_cons_self]
      simpa only [retainedSupport, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
        (congrArg (fun xs => xs ++ retainedSupport source rest) headEq).trans
          (congrArg (fun xs => retainedSupport destination [dependency] ++ xs) tailEq)

mutual
theorem typed_environment_congr
    (typed : Typed signature source ticket allowed expression type)
    (agree : AgreeOn source destination expression.dependencies) :
    Typed signature destination ticket allowed expression type := by
  cases typed with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» found => exact .variable ((agree _ List.mem_cons_self).symm.trans found)
  | reference => exact .reference
  | pair left right =>
      exact .pair (typed_environment_congr left (agree_left agree))
        (typed_environment_congr right (agree_right agree))
  | lambda body retained =>
      exact .lambda (typed_environment_congr body (agree_extend agree))
        (by
          have same := retained_support_congr agree
          simp only [Expr.dependencies] at same
          rw [← same]
          exact retained)
  | app function argument effects =>
      exact .app (typed_environment_congr function (agree_left agree))
        (typed_environment_congr argument (agree_right agree)) effects
  | bind initializer suffix =>
      exact .bind (typed_environment_congr initializer (agree_left agree))
        (typed_environment_congr suffix (agree_extend (agree_right agree)))
  | branch condition yes no =>
      exact .branch (typed_environment_congr condition (agree_left (agree_left agree)))
        (typed_environment_congr yes (agree_right (agree_left agree)))
        (typed_environment_congr no (agree_right agree))
  | perform operation available operand =>
      exact .perform operation available (typed_environment_congr operand (agree_right agree))
  | handle body clauses coverage unique effects =>
      exact .handle (typed_environment_congr body (agree_right (agree_left agree)))
        (clauses_environment_congr clauses (agree_right agree)) coverage unique effects
  | resume operand effects =>
      exact .resume (typed_environment_congr operand
        (fun name member => agree name (List.mem_cons_of_mem _ member))) effects
  | discard effects => exact .discard effects
  | resource initializer body noEscape noEffectEscape effects =>
      exact .resource (typed_environment_congr initializer (agree_left agree))
        (typed_environment_congr body (agree_without_resource (agree_right agree))) noEscape noEffectEscape effects
  | cleanup action body effects =>
      exact .cleanup (typed_environment_congr action (agree_left agree))
        (typed_environment_congr body (agree_right agree)) effects
termination_by sizeOf expression

theorem clauses_environment_congr
    (typed : ClausesTyped signature source effectInst answer residual clauses)
    (agree : AgreeOn source destination clauses.dependencies) :
    ClausesTyped signature destination effectInst answer residual clauses := by
  cases typed with
  | nil => exact .nil
  | cons operation body rest =>
      exact .cons operation
        (typed_environment_congr body (agree_extend (agree_without_ticket (agree_left agree))))
        (clauses_environment_congr rest (agree_right agree))
termination_by sizeOf clauses
end

theorem closed_value_environment_transport
    (typed : Typed signature source ticket allowed value type) (closed : ClosedValue value)
    (destination : TypeEnv) : Typed signature destination ticket allowed value type :=
  typed_environment_congr typed (fun _ retained => False.elim (closedValue_no_variable closed retained))

@[simp] theorem TypeEnv.extend_shadow (environment : TypeEnv) (name : Nat) (first second : Ty) :
    (environment.extend name first).extend name second = environment.extend name second := by
  funext other
  by_cases same : other = name <;> simp [TypeEnv.extend, same]

theorem TypeEnv.extend_commute (environment : TypeEnv) (first second : Nat) (a b : Ty)
    (different : first ≠ second) :
    (environment.extend first a).extend second b = (environment.extend second b).extend first a := by
  funext other
  by_cases one : other = first <;> by_cases two : other = second <;> simp_all [TypeEnv.extend]

mutual
theorem subst_absent (expression : Expr) (name : Nat) (value : Expr)
    (absent : Dependency.variable name ∉ expression.dependencies) :
    expression.subst name value = expression := by
  cases expression with
  | unit | boolean | integer | resourceRef | discard => rfl
  | «variable» other =>
      have different : name ≠ other := by simpa [Expr.dependencies] using absent
      simp [Expr.subst, different]
  | pair left right | app left right | cleanup left right =>
      have leftAbsent := fun member => absent (List.mem_append_left _ member)
      have rightAbsent := fun member => absent (List.mem_append_right _ member)
      simp only [Expr.subst, subst_absent left name value leftAbsent, subst_absent right name value rightAbsent]
  | lambda parameter body =>
      by_cases same : name = parameter
      · simp [Expr.subst, same]
      · have bodyAbsent : Dependency.variable name ∉ body.dependencies :=
          fun member => absent (mem_without.mpr ⟨member, by simpa using same⟩)
        simp only [Expr.subst, if_neg same, subst_absent body name value bodyAbsent]
  | bind parameter initializer body =>
      have initAbsent := fun member => absent (List.mem_append_left _ member)
      by_cases same : name = parameter
      · simp only [Expr.subst, if_pos same, subst_absent initializer name value initAbsent]
      · have bodyAbsent : Dependency.variable name ∉ body.dependencies := fun member =>
          absent (List.mem_append_right _ (mem_without.mpr ⟨member, by simpa using same⟩))
        simp only [Expr.subst, if_neg same, subst_absent initializer name value initAbsent,
          subst_absent body name value bodyAbsent]
  | branch condition yes no =>
      have conditionAbsent := fun member => absent (List.mem_append_left _ (List.mem_append_left _ member))
      have yesAbsent := fun member => absent (List.mem_append_left _ (List.mem_append_right _ member))
      have noAbsent := fun member => absent (List.mem_append_right _ member)
      simp only [Expr.subst, subst_absent condition name value conditionAbsent,
        subst_absent yes name value yesAbsent, subst_absent no name value noAbsent]
  | perform effectInst operation operand =>
      simp only [Expr.subst, subst_absent operand name value
        (fun member => absent (List.mem_append_right _ member))]
  | handle effectInst body clauses =>
      simp only [Expr.subst, subst_absent body name value
        (fun member => absent (List.mem_append_left _ (List.mem_append_right _ member))),
        clauses_subst_absent clauses name value (fun member => absent (List.mem_append_right _ member))]
  | resume ticket operand =>
      simp only [Expr.subst, subst_absent operand name value
        (fun member => absent (List.mem_cons_of_mem _ member))]
  | resource identity initializer body =>
      simp only [Expr.subst, subst_absent initializer name value
        (fun member => absent (List.mem_append_left _ member)),
        subst_absent body name value
        (fun member => absent (List.mem_append_right _ (mem_without.mpr ⟨member, by simp⟩)))]
termination_by sizeOf expression

theorem clauses_subst_absent (clauses : Clauses) (name : Nat) (value : Expr)
    (absent : Dependency.variable name ∉ clauses.dependencies) :
    clauses.subst name value = clauses := by
  cases clauses with
  | nil => rfl
  | cons operation parameter binder body rest =>
      have restAbsent := fun member => absent (List.mem_append_right _ member)
      by_cases same : name = parameter
      · simp only [Clauses.subst, if_pos same, clauses_subst_absent rest name value restAbsent]
      · have bodyAbsent : Dependency.variable name ∉ body.dependencies := fun member =>
          absent (List.mem_append_left _ (mem_without.mpr
            ⟨mem_without.mpr ⟨member, by simpa using same⟩, by simp⟩))
        simp only [Clauses.subst, if_neg same, subst_absent body name value bodyAbsent,
          clauses_subst_absent rest name value restAbsent]
termination_by sizeOf clauses
end

/-- Substitution converts a lexical value's support into actual syntax support.
    An unused variable contributes no inserted support. -/
theorem substitution_support_bound (expression : Expr) (name : Nat)
    (typed : Typed signature environment ticket allowed value input) (closed : ClosedValue value) :
    retainedSupport environment (expression.subst name value).dependencies ⊆
      retainedSupport (environment.extend name input) expression.dependencies := by
  by_cases occurs : Dependency.variable name ∈ expression.dependencies
  · intro identity retained
    obtain ⟨dependency, present, inHead⟩ := List.mem_flatMap.mp retained
    rcases List.mem_append.mp (substitution_bound_for_closed_value expression name closed present) with original | inserted
    · obtain ⟨old, different⟩ := mem_without.mp original
      apply List.mem_flatMap.mpr
      refine ⟨dependency, old, ?_⟩
      cases dependency with
      | resource | ticket => exact inHead
      | «variable» other =>
          have distinct : other ≠ name := by simpa using different
          simpa only [TypeEnv.extend, if_neg distinct] using inHead
    · cases dependency with
      | «variable» other => exact False.elim (closedValue_no_variable closed inserted)
      | ticket binder => exact False.elim (closedValue_no_ticket closed inserted)
      | resource resource =>
          have same : identity = resource := by simpa using inHead
          subst identity
          have bound := typed_value_support typed closed.1 (mem_resourceDependencies.mpr inserted)
          exact List.mem_flatMap.mpr ⟨.variable name, occurs, by
            simpa [TypeEnv.extend] using bound⟩
  · rw [subst_absent expression name value occurs]
    have agreement : AgreeOn environment (environment.extend name input) expression.dependencies := by
      intro other retained
      have different : other ≠ name := by
        intro same
        subst other
        exact occurs retained
      simp [TypeEnv.extend, different]
    rw [retained_support_congr agreement]
    exact fun _ retained => retained

@[simp] theorem clause_keys_substitution (clauses : Clauses) (name : Nat) (value : Expr) :
    clauseKeys (clauses.subst name value) = clauseKeys clauses := by
  cases clauses with
  | nil => rfl
  | cons operation parameter binder body rest =>
      exact congrArg (List.cons operation) (clause_keys_substitution rest name value)
termination_by sizeOf clauses

mutual
/-- Closed substitution preserves the exact annotated type, including closure
    support lists. Operational resource-name hygiene remains independent. -/
theorem typed_substitution
    (typed : Typed signature (environment.extend name input) ticket allowed expression type)
    (replacement : Typed signature environment .none [] value input) (closed : ClosedValue value) :
    Typed signature environment ticket allowed (expression.subst name value) type := by
  cases typed with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference
  | «variable» found =>
      simp only [Expr.subst]
      split
      · rename_i same
        subst name
        simp only [TypeEnv.extend] at found
        cases found
        exact typed_value_transport replacement closed.1 _ _
      · rename_i different
        exact .variable (by simpa [TypeEnv.extend, Ne.symm different] using found)
  | pair left right =>
      exact .pair (typed_substitution left replacement closed) (typed_substitution right replacement closed)
  | lambda body captured =>
      rename_i latent bodyExpr output parameter retained inputParam
      by_cases same : name = parameter
      · subst parameter
        simp [Expr.subst]
        apply Typed.lambda
        · simpa only [TypeEnv.extend_shadow] using body
        · have agreement : AgreeOn environment (environment.extend name input)
              (without (.variable name) bodyExpr.dependencies) := by
            intro other present
            have different : other ≠ name := by simpa using (mem_without.mp present).2
            simp [TypeEnv.extend, different]
          rw [retained_support_congr agreement]
          exact captured
      · simp only [Expr.subst, if_neg same]
        apply Typed.lambda
        · have rearranged := body
          rw [TypeEnv.extend_commute environment name parameter input inputParam same] at rearranged
          exact typed_substitution rearranged
            (closed_value_environment_transport replacement closed (environment.extend parameter inputParam)) closed
        · have bound := substitution_support_bound (.lambda parameter bodyExpr) name replacement closed
          simp only [Expr.subst, if_neg same, Expr.dependencies] at bound
          exact fun _ retained => captured (bound retained)
  | app function argument effects =>
      exact .app (typed_substitution function replacement closed) (typed_substitution argument replacement closed) effects
  | bind initializer suffix =>
      rename_i initializerExpr inputTy parameter suffixExpr
      apply Typed.bind (typed_substitution initializer replacement closed)
      by_cases same : name = parameter
      · subst parameter
        simpa only [ite_true, TypeEnv.extend_shadow] using suffix
      · simp only [if_neg same]
        have rearranged := suffix
        rw [TypeEnv.extend_commute environment name parameter input inputTy same] at rearranged
        exact typed_substitution rearranged
          (closed_value_environment_transport replacement closed (environment.extend parameter inputTy)) closed
  | branch condition yes no =>
      exact .branch (typed_substitution condition replacement closed)
        (typed_substitution yes replacement closed) (typed_substitution no replacement closed)
  | perform operation available operand => exact .perform operation available (typed_substitution operand replacement closed)
  | handle body clauses coverage unique effects =>
      exact .handle (typed_substitution body replacement closed) (clauses_typed_substitution clauses replacement closed)
        (by simpa only [Covers, clause_keys_substitution] using coverage)
        (by simpa only [clause_keys_substitution] using unique) effects
  | resume operand effects => exact .resume (typed_substitution operand replacement closed) effects
  | discard effects => exact .discard effects
  | resource initializer body noEscape noEffectEscape effects =>
      exact .resource (typed_substitution initializer replacement closed) (typed_substitution body replacement closed)
        noEscape noEffectEscape effects
  | cleanup action body effects =>
      exact .cleanup (typed_substitution action replacement closed) (typed_substitution body replacement closed) effects
termination_by sizeOf expression

theorem clauses_typed_substitution
    (typed : ClausesTyped signature (environment.extend name input) effectInst answer residual clauses)
    (replacement : Typed signature environment .none [] value input) (closed : ClosedValue value) :
    ClausesTyped signature environment effectInst answer residual (clauses.subst name value) := by
  cases typed with
  | nil => exact .nil
  | cons operation body rest =>
      rename_i operationKey operandType resultType binder bodyExpr restClauses parameter
      apply ClausesTyped.cons operation
      · by_cases same : name = parameter
        · subst parameter
          simpa only [ite_true, TypeEnv.extend_shadow] using body
        · simp only [if_neg same]
          have rearranged := body
          rw [TypeEnv.extend_commute environment name parameter input operandType same] at rearranged
          exact typed_substitution rearranged
            (closed_value_environment_transport replacement closed (environment.extend parameter operandType)) closed
      · exact clauses_typed_substitution rest replacement closed
termination_by sizeOf clauses
end

/-- Widen only the immediate effect bound; latent contracts and type
    annotations retain their original values. -/
theorem typed_effect_weaken (typed : Typed signature environment ticket allowed expression type)
    (bound : allowed ⊆ larger) : Typed signature environment ticket larger expression type := by
  induction typed using Typed.rec (motive_2 := fun _ _ _ _ _ _ => True) generalizing larger with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» found => exact .variable found
  | reference => exact .reference
  | pair left right ihLeft ihRight => exact .pair (ihLeft bound) (ihRight bound)
  | lambda body retained ih => exact .lambda body retained
  | app function argument effects ihFunction ihArgument =>
      exact .app (ihFunction bound) (ihArgument bound) (fun _ used => bound (effects used))
  | bind initializer suffix ihInitializer ihSuffix => exact .bind (ihInitializer bound) (ihSuffix bound)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch (ihCondition bound) (ihYes bound) (ihNo bound)
  | perform operation available operand ih => exact .perform operation (bound available) (ih bound)
  | handle body clauses coverage unique effects ihBody ihClauses =>
      exact .handle body clauses coverage unique (fun _ used => bound (effects used))
  | resume operand effects ih => exact .resume (ih bound) (fun _ used => bound (effects used))
  | discard effects => exact .discard (fun _ used => bound (effects used))
  | resource initializer body noEscape noEffectEscape effects ihInitializer ihBody =>
      exact .resource (ihInitializer bound) body noEscape noEffectEscape (fun _ used => bound (effects used))
  | cleanup action body effects ihAction ihBody =>
      exact .cleanup (ihAction bound) (ihBody bound) (fun _ used => bound (effects used))
  | nil | cons => trivial

/-- Code checked without an enclosing ticket does not acquire uses of one
    merely because a surrounding expression carries it. -/
theorem typed_none_ticket_transport
    (typed : Typed signature environment .none allowed expression type) (destination : TicketType) :
    Typed signature environment destination allowed expression type := by
  cases typed with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» found => exact .variable found
  | reference => exact .reference
  | pair left right => exact .pair (typed_none_ticket_transport left destination) (typed_none_ticket_transport right destination)
  | lambda body retained => exact .lambda body retained
  | app function argument effects =>
      exact .app (typed_none_ticket_transport function destination) (typed_none_ticket_transport argument destination) effects
  | bind initializer suffix =>
      exact .bind (typed_none_ticket_transport initializer destination) (typed_none_ticket_transport suffix destination)
  | branch condition yes no =>
      exact .branch (typed_none_ticket_transport condition destination)
        (typed_none_ticket_transport yes destination) (typed_none_ticket_transport no destination)
  | perform operation available operand => exact .perform operation available (typed_none_ticket_transport operand destination)
  | handle body clauses coverage unique effects =>
      exact .handle (typed_none_ticket_transport body destination) clauses coverage unique effects
  | resource initializer body noEscape noEffectEscape effects =>
      exact .resource (typed_none_ticket_transport initializer destination)
        (typed_none_ticket_transport body destination) noEscape noEffectEscape effects
  | cleanup action body effects =>
      exact .cleanup (typed_none_ticket_transport action destination) (typed_none_ticket_transport body destination) effects
termination_by sizeOf expression

/-- Preservation for the independent local reduction relation: substitution,
    branch selection, and its strict contexts. Dispatch/control transitions
    still require the full machine typing and admission invariant. -/
theorem local_step_preserves_types (step : LocalStep before after)
    (typed : Typed signature environment ticket allowed before type) :
    Typed signature environment ticket allowed after type := by
  induction step generalizing environment ticket allowed type with
  | bind parameter value suffix closed environmentReady fresh => cases typed with
      | bind initializer suffix =>
          exact typed_substitution suffix (typed_value_transport initializer closed.1 .none []) closed
  | beta parameter body value closed closureReady fresh => cases typed with
      | app function argument effects => cases function with
          | lambda body retained =>
              exact typed_effect_weaken (typed_none_ticket_transport
                (typed_substitution body (typed_value_transport argument closed.1 .none []) closed) ticket) effects
  | ifTrue yes no => cases typed with
      | branch condition yes no => exact yes
  | ifFalse yes no => cases typed with
      | branch condition yes no => exact no
  | pairLeft step right ih => cases typed with
      | pair left right => exact .pair (ih left) right
  | pairRight left closed step ih => cases typed with
      | pair left right => exact .pair left (ih right)
  | appFunction step argument ih => cases typed with
      | app function argument effects => exact .app (ih function) argument effects
  | appArgument function closed step ih => cases typed with
      | app function argument effects => exact .app function (ih argument) effects
  | bindInitializer parameter step suffix ih => cases typed with
      | bind initializer suffix => exact .bind (ih initializer) suffix
  | branchCondition step yes no ih => cases typed with
      | branch condition yes no => exact .branch (ih condition) yes no
  | performOperand effectInst operation step ih => cases typed with
      | perform operation available operand => exact .perform operation available (ih operand)
  | resumeOperand binder step ih => cases typed with
      | resume operand effects => exact .resume (ih operand) effects
  | handlerBody effectInst step clauses ih => cases typed with
      | handle body clauses coverage unique effects => exact .handle (ih body) clauses coverage unique effects
  | resourceInitializer identity step body ih => cases typed with
      | resource initializer body noEscape noEffectEscape effects =>
          exact .resource (ih initializer) body noEscape noEffectEscape effects
  | cleanupInitializer step body ih => cases typed with
      | cleanup action body effects => exact .cleanup (ih action) body effects

/-- The exact clause selected by execution remains typed after installing its
    closed operand. The new dynamic ticket identity is a separate scope map. -/
theorem selected_clause_substitution_typed
    (selected : ClauseAt operation clauses parameter binder body)
    (clausesTyped : ClausesTyped signature environment effectInst answer residual clauses)
    (known : signature effectInst operation = some (input, output))
    (operandTyped : Typed signature environment ticket allowed operand input)
    (closed : ClosedValue operand) :
    Typed signature environment (.bound binder output answer residual residual) residual
      (body.subst parameter operand) answer := by
  obtain ⟨clauseInput, clauseOutput, clauseSignature, bodyTyped⟩ := selected_clause_typed selected clausesTyped
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans clauseSignature))
  exact typed_substitution bodyTyped (typed_value_transport operandTyped closed.1 .none []) closed

/-- Local reduction preserves the independently checked type/effect bound,
    usage protocol, and available resource support together. This theorem
    concerns LocalStep, not effect dispatch or continuation recomposition. -/
theorem local_step_preserves_joint (step : LocalStep before after)
    (typed : Typed signature environment ticket allowed before type)
    (usage : Uses policy useScope incoming before outgoing)
    (support : resourceDependencies before.dependencies ⊆ available) :
    Typed signature environment ticket allowed after type ∧
      Uses policy useScope incoming after outgoing ∧
      resourceDependencies after.dependencies ⊆ available :=
  ⟨local_step_preserves_types step typed, local_step_preserves_usage step usage,
    expression_access_mono (local_step_dependencies step) support⟩

namespace Examples

/-- The same closure support annotation survives replacement of an ordinary
    captured variable by its closed resource handle. -/
theorem bind_retained_reference_typed :
    Typed cellOnly TypeEnv.empty .none []
      (.lambda 0 (.bind 1 (.resourceRef 4) .unit)) (.function .unit .unit [] [4]) := by
  have before : Typed cellOnly TypeEnv.empty .none []
      (.bind 9 (.resourceRef 4) (.lambda 0 (.bind 1 (.variable 9) .unit))) (.function .unit .unit [] [4]) :=
    .bind .reference lexical_capture_typed
  have step : LocalStep (.bind 9 (.resourceRef 4) (.lambda 0 (.bind 1 (.variable 9) .unit)))
      (.lambda 0 (.bind 1 (.resourceRef 4) .unit)) :=
    .bind 9 (.resourceRef 4) _ (Execution.Examples.closed_reference 4)
      (by simp [ClosedExcept, Expr.dependencies, without])
      (by simp [ResourceFresh, Expr.dependencies, Expr.resourceBinders])
  exact local_step_preserves_types step before

/-- A shadowed variable contributes no resource dependency to the result. -/
theorem shadowed_binding_returns_identity :
    Typed cellOnly TypeEnv.empty .none [] (.lambda 9 (.variable 9)) (.function .integer .integer [] []) := by
  have suffix : Typed cellOnly (TypeEnv.empty.extend 9 (.reference 4)) .none []
      (.lambda 9 (.variable 9)) (.function .integer .integer [] []) := by
    apply Typed.lambda
    · exact .variable (by simp [TypeEnv.extend])
    · simp [retainedSupport, without, Expr.dependencies]
  exact typed_substitution suffix (Typed.reference (identity := 4)) (Execution.Examples.closed_reference 4)

/-- This source-shaped scope can return an identity closure because the local
    handle is shadowed and absent from the closure's support. -/
theorem scope_returns_shadowed_identity :
    Typed cellOnly TypeEnv.empty .none []
      (.resource 4 (.integer 0) (.bind 9 (.resourceRef 4) (.lambda 9 (.variable 9))))
      (.function .integer .integer [] []) := by
  apply Typed.resource (residual := []) .integer
  · apply Typed.bind (input := .reference 4) .reference
    apply Typed.lambda
    · exact .variable (by simp [TypeEnv.extend])
    · simp [retainedSupport, without, Expr.dependencies]
  · simp [Ty.resources]
  · simp
  · simp

/-- Type preservation does not prove fresh resource instantiation. -/
theorem typed_substitution_still_needs_resource_hygiene :
    Typed cellOnly TypeEnv.empty .none []
      ((Expr.resource 4 (.integer 0) (.bind 1 (.variable 9) .unit)).subst 9 (.resourceRef 4)) .unit ∧
      ¬ ResourceFresh (.resourceRef 4) (.resource 4 (.integer 0) (.bind 1 (.variable 9) .unit)) := by
  constructor
  · have body : Typed cellOnly (TypeEnv.empty.extend 9 (.reference 4)) .none []
        (.resource 4 (.integer 0) (.bind 1 (.variable 9) .unit)) .unit := by
      apply Typed.resource (residual := []) .integer
      · exact .bind (input := .reference 4) (.variable (by simp [TypeEnv.extend])) .unit
      · simp [Ty.resources]
      · simp
      · simp
    exact typed_substitution body Typed.reference (Execution.Examples.closed_reference 4)
  · simp [ResourceFresh, Expr.dependencies, Expr.resourceBinders]

def unitRequestSignature : Signature := fun effectInst operation =>
  if effectInst = .user 1 [] ∧ operation = 0 then some (.unit, .unit) else none

theorem cleanup_clause_instantiation_typed :
    Typed unitRequestSignature TypeEnv.empty (.bound 9 .unit .integer [] []) [] (.resume 9 .unit) .integer := by
  have clauses : ClausesTyped unitRequestSignature TypeEnv.empty (.user 1 []) .integer []
      Execution.Examples.clauses := by
    apply ClausesTyped.cons (input := .unit) (output := .unit)
    · simp [unitRequestSignature]
    · exact .resume .unit (fun _ used => used)
    · exact .nil
  exact selected_clause_substitution_typed (parameter := 1) (input := .unit) (output := .unit)
    ClauseAt.hit clauses (by simp [unitRequestSignature])
    (Typed.unit (ticket := .none) (allowed := [])) Execution.Examples.closed_unit

end Examples

end Ash.OneShot.Typing

#print axioms Ash.OneShot.Typing.typed_environment_congr
#print axioms Ash.OneShot.Typing.closed_value_environment_transport

#print axioms Ash.OneShot.Typing.substitution_support_bound

#print axioms Ash.OneShot.Typing.typed_substitution
#print axioms Ash.OneShot.Typing.clauses_typed_substitution

#print axioms Ash.OneShot.Typing.local_step_preserves_types
#print axioms Ash.OneShot.Typing.selected_clause_substitution_typed

#print axioms Ash.OneShot.Typing.Examples.bind_retained_reference_typed
#print axioms Ash.OneShot.Typing.Examples.shadowed_binding_returns_identity
#print axioms Ash.OneShot.Typing.Examples.typed_substitution_still_needs_resource_hygiene
#print axioms Ash.OneShot.Typing.Examples.cleanup_clause_instantiation_typed

#print axioms Ash.OneShot.Typing.local_step_preserves_joint
