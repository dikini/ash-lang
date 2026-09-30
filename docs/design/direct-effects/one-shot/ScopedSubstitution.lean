import ScopedTyping

/-!
Typed ordinary substitution for scoped expressions. Generative resource bodies
are opened before recursive checking; closed replacement values retain their
older activation atoms. This is an ingredient of machine preservation, not a
source-admission or full progress theorem.
-/

namespace Ash.OneShot.ScopedExpressions
open Instantiation Syntax

mutual
def Code.nodes : Code → Nat
  | .unit | .boolean _ | .integer _ | .variable _ | .resourceRef _ | .discard _ => 1
  | .pair left right | .app left right | .bind _ left right | .resource _ left right | .cleanup left right =>
      left.nodes + right.nodes + 1
  | .lambda _ body | .perform _ _ body | .resume _ body => body.nodes + 1
  | .branch condition yes no => condition.nodes + yes.nodes + no.nodes + 1
  | .handle _ body clauses => body.nodes + clauses.nodes + 1

def Clauses.nodes : Clauses → Nat
  | .nil => 1
  | .cons _ _ _ body rest => body.nodes + rest.nodes + 1
end

mutual
@[simp] theorem Code.instantiation_nodes (code : Code) (environment : Environment) :
    (code.instantiate environment).nodes = code.nodes := by
  cases code with
  | unit | boolean | integer | «variable» | resourceRef | discard => rfl
  | pair left right | app left right | bind _ left right | resource _ left right | cleanup left right =>
      simp only [Code.instantiate, Code.nodes, left.instantiation_nodes, right.instantiation_nodes]
  | lambda _ body | perform _ _ body | resume _ body =>
      simp only [Code.instantiate, Code.nodes, body.instantiation_nodes]
  | branch condition yes no =>
      simp only [Code.instantiate, Code.nodes, condition.instantiation_nodes, yes.instantiation_nodes, no.instantiation_nodes]
  | handle _ body clauses =>
      simp only [Code.instantiate, Code.nodes, body.instantiation_nodes, clauses.instantiation_nodes]

@[simp] theorem Clauses.instantiation_nodes (clauses : Clauses) (environment : Environment) :
    (clauses.instantiate environment).nodes = clauses.nodes := by
  cases clauses with
  | nil => rfl
  | cons _ _ _ body rest =>
      simp only [Clauses.instantiate, Clauses.nodes, body.instantiation_nodes, rest.instantiation_nodes]
end

end Ash.OneShot.ScopedExpressions

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (TypeEnv Signature TicketType retainedSupport AgreeOn agree_left agree_right agree_extend
  agree_without_ticket retained_support_congr)

theorem closedValue_no_variable (h : ScopedExpressions.ClosedValue value) : Dependency.variable name ∉ value.dependencies :=
  fun present => h.2.2 _ present

theorem closedValue_no_ticket (h : ScopedExpressions.ClosedValue value) : Dependency.ticket name ∉ value.dependencies :=
  fun present => h.2.2 _ present

theorem opened_body_environment_agree {body : Code} {binder identity : Nat}
    (agree : AgreeOn source destination body.dependencies) :
    AgreeOn source destination (body.instantiate (Environment.empty.bind binder identity)).dependencies := by
  intro name member
  rcases List.mem_append.mp (acquisition_dependency_bound binder identity body member) with old | fresh
  · exact agree name old
  · simp at fresh

mutual
theorem typed_environment_congr
    (typed : Typed signature world source ticket allowed expression type)
    (agree : AgreeOn source destination expression.dependencies) :
    Typed signature world destination ticket allowed expression type := by
  cases typed with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» found formed => exact .variable ((agree _ List.mem_cons_self).symm.trans found) formed
  | reference issued => exact .reference issued
  | pair left right =>
      exact .pair (typed_environment_congr left (agree_left agree))
        (typed_environment_congr right (agree_right agree))
  | lambda body retained formed =>
      exact .lambda (typed_environment_congr body (agree_extend agree))
        (by
          have same := retained_support_congr agree
          simp only [Code.dependencies] at same
          rw [← same]
          exact retained) formed
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
  | perform operation available operand formed =>
      exact .perform operation available (typed_environment_congr operand (agree_right agree)) formed
  | handle body clauses coverage unique effects =>
      exact .handle (typed_environment_congr body (agree_right (agree_left agree)))
        (clauses_environment_congr clauses (agree_right agree)) coverage unique effects
  | resume operand effects formed =>
      exact .resume (typed_environment_congr operand
        (fun name member => agree name (List.mem_cons_of_mem _ member))) effects formed
  | discard effects => exact .discard effects
  | resource initializer body noEscape noEffectEscape effects =>
      exact .resource (typed_environment_congr initializer (agree_left agree))
        (fun identity fresh => typed_environment_congr (body identity fresh)
          (opened_body_environment_agree (agree_right agree))) noEscape noEffectEscape effects
  | cleanup action body effects =>
      exact .cleanup (typed_environment_congr action (agree_left agree))
        (typed_environment_congr body (agree_right agree)) effects
termination_by expression.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes, Code.instantiation_nodes]; all_goals omega

theorem clauses_environment_congr
    (typed : ClausesTyped signature world source effectInst answer residual clauses)
    (agree : AgreeOn source destination clauses.dependencies) :
    ClausesTyped signature world destination effectInst answer residual clauses := by
  cases typed with
  | nil => exact .nil
  | cons operation body rest =>
      exact .cons operation
        (typed_environment_congr body (agree_extend (agree_without_ticket (agree_left agree))))
        (clauses_environment_congr rest (agree_right agree))
termination_by clauses.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Clauses.nodes]; all_goals omega
end

theorem closed_value_environment_transport
    (typed : Typed signature world source ticket allowed value type) (closed : ScopedExpressions.ClosedValue value)
    (destination : TypeEnv) : Typed signature world destination ticket allowed value type :=
  typed_environment_congr typed (fun _ retained => False.elim (closedValue_no_variable closed retained))


mutual
theorem subst_absent (expression : Code) (name : Nat) (value : Code)
    (absent : Dependency.variable name ∉ expression.dependencies) :
    expression.subst name value = expression := by
  cases expression with
  | unit | boolean | integer | resourceRef | discard => rfl
  | «variable» other =>
      have different : name ≠ other := by simpa [Code.dependencies] using absent
      simp [Code.subst, different]
  | pair left right | app left right | cleanup left right =>
      have leftAbsent := fun member => absent (List.mem_append_left _ member)
      have rightAbsent := fun member => absent (List.mem_append_right _ member)
      simp only [Code.subst, subst_absent left name value leftAbsent, subst_absent right name value rightAbsent]
  | lambda parameter body =>
      by_cases same : name = parameter
      · simp [Code.subst, same]
      · have bodyAbsent : Dependency.variable name ∉ body.dependencies :=
          fun member => absent (mem_without.mpr ⟨member, by simpa using same⟩)
        simp only [Code.subst, if_neg same, subst_absent body name value bodyAbsent]
  | bind parameter initializer body =>
      have initAbsent := fun member => absent (List.mem_append_left _ member)
      by_cases same : name = parameter
      · simp only [Code.subst, if_pos same, subst_absent initializer name value initAbsent]
      · have bodyAbsent : Dependency.variable name ∉ body.dependencies := fun member =>
          absent (List.mem_append_right _ (mem_without.mpr ⟨member, by simpa using same⟩))
        simp only [Code.subst, if_neg same, subst_absent initializer name value initAbsent,
          subst_absent body name value bodyAbsent]
  | branch condition yes no =>
      have conditionAbsent := fun member => absent (List.mem_append_left _ (List.mem_append_left _ member))
      have yesAbsent := fun member => absent (List.mem_append_left _ (List.mem_append_right _ member))
      have noAbsent := fun member => absent (List.mem_append_right _ member)
      simp only [Code.subst, subst_absent condition name value conditionAbsent,
        subst_absent yes name value yesAbsent, subst_absent no name value noAbsent]
  | perform effectInst operation operand =>
      simp only [Code.subst, subst_absent operand name value
        (fun member => absent (List.mem_append_right _ member))]
  | handle effectInst body clauses =>
      simp only [Code.subst, subst_absent body name value
        (fun member => absent (List.mem_append_left _ (List.mem_append_right _ member))),
        clauses_subst_absent clauses name value (fun member => absent (List.mem_append_right _ member))]
  | resume ticket operand =>
      simp only [Code.subst, subst_absent operand name value
        (fun member => absent (List.mem_cons_of_mem _ member))]
  | resource identity initializer body =>
      simp only [Code.subst, subst_absent initializer name value
        (fun member => absent (List.mem_append_left _ member)),
        subst_absent body name value
        (fun member => absent (List.mem_append_right _ member))]
termination_by sizeOf expression

theorem clauses_subst_absent (clauses : ScopedExpressions.Clauses) (name : Nat) (value : Code)
    (absent : Dependency.variable name ∉ clauses.dependencies) :
    clauses.subst name value = clauses := by
  cases clauses with
  | nil => rfl
  | cons operation parameter binder body rest =>
      have restAbsent := fun member => absent (List.mem_append_right _ member)
      by_cases same : name = parameter
      · simp only [ScopedExpressions.Clauses.subst, if_pos same, clauses_subst_absent rest name value restAbsent]
      · have bodyAbsent : Dependency.variable name ∉ body.dependencies := fun member =>
          absent (List.mem_append_left _ (mem_without.mpr
            ⟨mem_without.mpr ⟨member, by simpa using same⟩, by simp⟩))
        simp only [ScopedExpressions.Clauses.subst, if_neg same, subst_absent body name value bodyAbsent,
          clauses_subst_absent rest name value restAbsent]
termination_by sizeOf clauses
end

end Ash.OneShot.ScopedTyping

namespace Ash.OneShot.ScopedExpressions
open Syntax Instantiation

theorem effect_has_no_variable (effect : Effect) (name : Nat) :
    Dependency.variable name ∉ (effectAtoms effect).map Dependency.resource := by
  intro present
  obtain ⟨resource, inside, equal⟩ := List.mem_map.mp present
  cases equal

mutual
theorem Code.subst_removes_variable (expression : Code) (name : Nat) (value : Code)
    (absent : Dependency.variable name ∉ value.dependencies) :
    Dependency.variable name ∉ (expression.subst name value).dependencies := by
  cases expression with
  | unit | boolean _ | integer _ | discard _ =>
      simp [Code.subst, Code.dependencies]
  | resourceRef ref => cases ref <;> simp [Code.subst, Code.dependencies]
  | «variable» other =>
      by_cases same : name = other
      · simpa only [Code.subst, if_pos same] using absent
      · simp [Code.subst, same, Code.dependencies]
  | pair left right | app left right | cleanup left right =>
      exact not_in_append ⟨left.subst_removes_variable name value absent,
        right.subst_removes_variable name value absent⟩
  | lambda parameter body =>
      by_cases same : name = parameter
      · simp [Code.subst, same, Code.dependencies]
      · simpa only [Code.subst, if_neg same, Code.dependencies] using
          without_preserves_absence (body.subst_removes_variable name value absent) (.variable parameter)
  | bind parameter initializer body =>
      have hi := initializer.subst_removes_variable name value absent
      by_cases same : name = parameter
      · simpa [Code.subst, same, Code.dependencies] using hi
      · simpa only [Code.subst, if_neg same, Code.dependencies] using
          not_in_append ⟨hi,
            without_preserves_absence (body.subst_removes_variable name value absent) (.variable parameter)⟩
  | branch condition yes no =>
      exact not_in_append
        ⟨not_in_append ⟨condition.subst_removes_variable name value absent,
          yes.subst_removes_variable name value absent⟩, no.subst_removes_variable name value absent⟩
  | perform effectInst operation operand =>
      exact not_in_append ⟨effect_has_no_variable effectInst name,
        operand.subst_removes_variable name value absent⟩
  | handle effectInst body clauses =>
      exact not_in_append
        ⟨not_in_append ⟨effect_has_no_variable effectInst name,
          body.subst_removes_variable name value absent⟩, clauses.subst_removes_variable name value absent⟩
  | resume ticket operand =>
      simpa [Code.subst, Code.dependencies] using operand.subst_removes_variable name value absent
  | resource resource initializer body =>
      exact not_in_append ⟨initializer.subst_removes_variable name value absent,
        body.subst_removes_variable name value absent⟩

theorem Clauses.subst_removes_variable (clauses : ScopedExpressions.Clauses) (name : Nat) (value : Code)
    (absent : Dependency.variable name ∉ value.dependencies) :
    Dependency.variable name ∉ (clauses.subst name value).dependencies := by
  cases clauses with
  | nil => simp [ScopedExpressions.Clauses.subst, ScopedExpressions.Clauses.dependencies]
  | cons operation parameter ticket body rest =>
      have hr := rest.subst_removes_variable name value absent
      by_cases same : name = parameter
      · simpa [ScopedExpressions.Clauses.subst, same, ScopedExpressions.Clauses.dependencies] using hr
      · simpa only [ScopedExpressions.Clauses.subst, if_neg same, ScopedExpressions.Clauses.dependencies] using
          not_in_append
            ⟨without_preserves_absence
              (without_preserves_absence (body.subst_removes_variable name value absent)
                (.variable parameter)) (.ticket ticket), hr⟩
end

end Ash.OneShot.ScopedExpressions

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (TypeEnv Signature TicketType retainedSupport AgreeOn retained_support_congr)

theorem substitution_bound_for_closed_value (expression : Code) (name : Nat)
    (closed : ScopedExpressions.ClosedValue value) :
    (expression.subst name value).dependencies ⊆
      without (.variable name) expression.dependencies ++ value.dependencies := by
  intro dependency retained
  rcases List.mem_append.mp (expression.subst_dependencies name value retained) with old | inserted
  · have different : dependency ≠ .variable name := by
      intro same
      subst dependency
      exact expression.subst_removes_variable name value (closedValue_no_variable closed) retained
    exact List.mem_append_left _ (mem_without.mpr ⟨old, different⟩)
  · exact List.mem_append_right _ inserted

/-- Immediate effect bounds and the enclosing ticket can change for a value;
    its function body's independently checked contracts remain unchanged. -/
theorem typed_value_transport (typed : Typed signature world environment ticket allowed value type)
    (isValue : value.IsValue) (destination : TicketType) (effects : List Instance) :
    Typed signature world environment destination effects value type := by
  cases typed with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» => cases isValue
  | reference issued => exact .reference issued
  | pair left right =>
      exact .pair (typed_value_transport left isValue.1 destination effects)
        (typed_value_transport right isValue.2 destination effects)
  | lambda body retained formed => exact .lambda body retained formed
  | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases isValue
termination_by sizeOf value

/-- Substitution converts a lexical value's support into actual syntax support.
    An unused variable contributes no inserted support. -/
theorem substitution_support_bound (expression : Code) (name : Nat)
    (typed : Typed signature world environment ticket allowed value input) (closed : ScopedExpressions.ClosedValue value) :
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

@[simp] theorem clause_keys_substitution (clauses : ScopedExpressions.Clauses) (name : Nat) (value : Code) :
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
    (typed : Typed signature world (environment.extend name input) ticket allowed expression type)
    (replacement : Typed signature world environment .none [] value input) (closed : ScopedExpressions.ClosedValue value) :
    Typed signature world environment ticket allowed (expression.subst name value) type := by
  cases typed with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» found formed =>
      simp only [Code.subst]
      split
      · rename_i same
        subst name
        simp only [TypeEnv.extend] at found
        cases found
        exact typed_value_transport replacement closed.1 _ _
      · rename_i different
        exact .variable (by simpa [TypeEnv.extend, Ne.symm different] using found) formed
  | pair left right =>
      exact .pair (typed_substitution left replacement closed) (typed_substitution right replacement closed)
  | lambda body captured formed =>
      rename_i latent bodyExpr output parameter retained inputParam
      by_cases same : name = parameter
      · subst parameter
        simp [Code.subst]
        apply Typed.lambda
        · simpa only [TypeEnv.extend_shadow] using body
        · have agreement : AgreeOn environment (environment.extend name input)
              (without (.variable name) bodyExpr.dependencies) := by
            intro other present
            have different : other ≠ name := by simpa using (mem_without.mp present).2
            simp [TypeEnv.extend, different]
          rw [retained_support_congr agreement]
          exact captured
        · exact formed
      · simp only [Code.subst, if_neg same]
        apply Typed.lambda
        · have rearranged := body
          rw [TypeEnv.extend_commute environment name parameter input inputParam same] at rearranged
          exact typed_substitution rearranged
            (closed_value_environment_transport replacement closed (environment.extend parameter inputParam)) closed
        · have bound := substitution_support_bound (.lambda parameter bodyExpr) name replacement closed
          simp only [Code.subst, if_neg same, Code.dependencies] at bound
          exact fun _ retained => captured (bound retained)
        · exact formed
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
  | perform operation available operand formed => exact .perform operation available (typed_substitution operand replacement closed) formed
  | handle body clauses coverage unique effects =>
      exact .handle (typed_substitution body replacement closed) (clauses_typed_substitution clauses replacement closed)
        (by simpa only [Covers, clause_keys_substitution] using coverage)
        (by simpa only [clause_keys_substitution] using unique) effects
  | resume operand effects formed => exact .resume (typed_substitution operand replacement closed) effects formed
  | discard effects => exact .discard effects
  | resource initializer body noEscape noEffectEscape effects =>
      refine .resource (typed_substitution initializer replacement closed) ?_ noEscape noEffectEscape effects
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact typed_substitution (body identity fresh)
        (typed_world_weaken replacement _ (fun _ member => List.mem_append_left _ member)) closed
  | cleanup action body effects =>
      exact .cleanup (typed_substitution action replacement closed) (typed_substitution body replacement closed) effects
termination_by expression.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes, Code.instantiation_nodes]; all_goals omega

theorem clauses_typed_substitution
    (typed : ClausesTyped signature world (environment.extend name input) effectInst answer residual clauses)
    (replacement : Typed signature world environment .none [] value input) (closed : ScopedExpressions.ClosedValue value) :
    ClausesTyped signature world environment effectInst answer residual (clauses.subst name value) := by
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
termination_by clauses.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Clauses.nodes]; all_goals omega
end



/-- Widen only the immediate effect bound; latent contracts and type
    annotations retain their original values. -/
theorem typed_effect_weaken (typed : Typed signature world environment ticket allowed expression type)
    (bound : allowed ⊆ larger) : Typed signature world environment ticket larger expression type := by
  induction typed using Typed.rec (motive_2 := fun _ _ _ _ _ _ _ => True) generalizing larger with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» found formed => exact .variable found formed
  | reference issued => exact .reference issued
  | pair left right ihLeft ihRight => exact .pair (ihLeft bound) (ihRight bound)
  | lambda body retained formed ih => exact .lambda body retained formed
  | app function argument effects ihFunction ihArgument =>
      exact .app (ihFunction bound) (ihArgument bound) (fun _ used => bound (effects used))
  | bind initializer suffix ihInitializer ihSuffix => exact .bind (ihInitializer bound) (ihSuffix bound)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch (ihCondition bound) (ihYes bound) (ihNo bound)
  | perform operation available operand formed ih => exact .perform operation (bound available) (ih bound) formed
  | handle body clauses coverage unique effects ihBody ihClauses =>
      exact .handle body clauses coverage unique (fun _ used => bound (effects used))
  | resume operand effects formed ih => exact .resume (ih bound) (fun _ used => bound (effects used)) formed
  | discard effects => exact .discard (fun _ used => bound (effects used))
  | resource initializer body noEscape noEffectEscape effects ihInitializer ihBody =>
      exact .resource (ihInitializer bound) body noEscape noEffectEscape (fun _ used => bound (effects used))
  | cleanup action body effects ihAction ihBody =>
      exact .cleanup (ihAction bound) (ihBody bound) (fun _ used => bound (effects used))
  | nil | cons => trivial

/-- Code checked without an enclosing ticket does not acquire uses of one
    merely because a surrounding expression carries it. -/
theorem typed_none_ticket_transport
    (typed : Typed signature world environment .none allowed expression type) (destination : TicketType) :
    Typed signature world environment destination allowed expression type := by
  cases typed with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» found formed => exact .variable found formed
  | reference issued => exact .reference issued
  | pair left right => exact .pair (typed_none_ticket_transport left destination) (typed_none_ticket_transport right destination)
  | lambda body retained formed => exact .lambda body retained formed
  | app function argument effects =>
      exact .app (typed_none_ticket_transport function destination) (typed_none_ticket_transport argument destination) effects
  | bind initializer suffix =>
      exact .bind (typed_none_ticket_transport initializer destination) (typed_none_ticket_transport suffix destination)
  | branch condition yes no =>
      exact .branch (typed_none_ticket_transport condition destination)
        (typed_none_ticket_transport yes destination) (typed_none_ticket_transport no destination)
  | perform operation available operand formed => exact .perform operation available (typed_none_ticket_transport operand destination) formed
  | handle body clauses coverage unique effects =>
      exact .handle (typed_none_ticket_transport body destination) clauses coverage unique effects
  | resource initializer body noEscape noEffectEscape effects =>
      exact .resource (typed_none_ticket_transport initializer destination)
        (fun identity fresh => typed_none_ticket_transport (body identity fresh) destination) noEscape noEffectEscape effects
  | cleanup action body effects =>
      exact .cleanup (typed_none_ticket_transport action destination) (typed_none_ticket_transport body destination) effects
termination_by expression.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes, Code.instantiation_nodes]; all_goals omega



/-- The actual selected clause supplies the operand and continuation ports. -/
theorem selected_clause_typed
    (selected : ScopedExecution.ClauseAt operation clauses parameter binder body)
    (typed : ClausesTyped signature world environment effect answer residual clauses) :
    ∃ input output, signature effect operation = some (input, output) ∧
      Typed signature world (environment.extend parameter input)
        (.bound binder output answer residual residual) residual body answer := by
  induction selected with
  | hit => cases typed with
      | cons operation body rest => exact ⟨_, _, operation, body⟩
  | pass different next ih => cases typed with
      | cons operation body rest => exact ih rest

theorem selected_clause_substitution_typed
    (selected : ScopedExecution.ClauseAt operation clauses parameter binder body)
    (clausesTyped : ClausesTyped signature world environment effect answer residual clauses)
    (known : signature effect operation = some (input, output))
    (operandTyped : Typed signature world environment ticket allowed operand input)
    (closed : ScopedExpressions.ClosedValue operand) :
    Typed signature world environment (.bound binder output answer residual residual) residual
      (body.subst parameter operand) answer := by
  obtain ⟨clauseInput, clauseOutput, clauseSignature, bodyTyped⟩ := selected_clause_typed selected clausesTyped
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans clauseSignature))
  exact typed_substitution bodyTyped (typed_value_transport operandTyped closed.1 .none []) closed

theorem typed_bind_reduction
    (typed : Typed signature world environment ticket allowed (.bind parameter value suffix) type)
    (closed : ScopedExpressions.ClosedValue value) :
    Typed signature world environment ticket allowed (suffix.subst parameter value) type := by
  cases typed with
  | bind initializer suffix =>
      exact typed_substitution suffix (typed_value_transport initializer closed.1 .none []) closed

/-- Beta evaluation resets the active lexical ticket scope, as RawStep.beta
    specifies. Its lambda body already checked under the empty ticket scope. -/
theorem typed_beta_reduction
    (typed : Typed signature world environment ticket allowed (.app (.lambda parameter body) value) type)
    (closed : ScopedExpressions.ClosedValue value) :
    Typed signature world environment .none allowed (body.subst parameter value) type := by
  cases typed with
  | app function argument effects => cases function with
      | lambda body captured formed =>
          exact typed_effect_weaken (typed_substitution body (typed_value_transport argument closed.1 .none []) closed) effects

/-- These are actual scoped machine steps. Their syntactic readiness premises
    remain explicit; this theorem does not claim complete source admission. -/
theorem typed_bind_step
    (typed : Typed signature world environment ticket allowed (.bind parameter value suffix) type)
    (closed : ScopedExpressions.ClosedValue value) (ready : ScopedExpressions.ClosedExcept parameter suffix)
    (scope : Scope) (tail : Stack) :
    RawStep ⟨.bind parameter value suffix, scope, tail⟩ ⟨suffix.subst parameter value, scope, tail⟩ [] [] ∧
      Typed signature world environment ticket allowed (suffix.subst parameter value) type :=
  ⟨.bind parameter value suffix scope tail closed ready, typed_bind_reduction typed closed⟩

theorem typed_beta_step
    (typed : Typed signature world environment ticket allowed (.app (.lambda parameter body) value) type)
    (closed : ScopedExpressions.ClosedValue value) (ready : ScopedExpressions.ClosedValue (.lambda parameter body))
    (scope : Scope) (tail : Stack) :
    RawStep ⟨.app (.lambda parameter body) value, scope, tail⟩ ⟨body.subst parameter value, .none, tail⟩ [] [] ∧
      Typed signature world environment .none allowed (body.subst parameter value) type :=
  ⟨.beta parameter body value scope tail closed ready, typed_beta_reduction typed closed⟩

namespace SubstitutionExamples

theorem older_reference_closed : ScopedExpressions.ClosedValue (.resourceRef (.activation 4)) :=
  ⟨trivial, rfl, by intro dependency member; obtain rfl := List.mem_singleton.mp member; trivial⟩

/-- Source binder 4 does not bind activation atom 4 in a substituted value. -/
theorem same_numbered_site_preserves_older_reference :
    Typed signature [4] TypeEnv.empty .none []
      ((Code.resource 4 (.integer 0) (.variable 9)).subst 9 (.resourceRef (.activation 4))) (.reference 4) ∧
      ∀ identity, (((Code.resource 4 (.integer 0) (.variable 9)).subst 9 (.resourceRef (.activation 4))).instantiate
        (Environment.empty.bind 4 identity)) = .resource 4 (.integer 0) (.resourceRef (.activation 4)) := by
  have original : Typed signature [4] (TypeEnv.empty.extend 9 (.reference 4)) .none []
      (.resource 4 (.integer 0) (.variable 9)) (.reference 4) := by
    refine .resource .integer (residual := []) ?_ (List.Subset.refl _) (List.nil_subset _) (List.nil_subset _)
    intro identity fresh
    exact .variable rfl (fun _ member => List.mem_append_left _ member)
  exact ⟨typed_substitution original (.reference List.mem_cons_self) older_reference_closed, fun _ => rfl⟩

theorem repeated_function_beta_is_typed :
    RawStep ⟨ScopedExecution.Examples.call, .none, .nil⟩ ⟨ScopedExecution.Examples.acquisition, .none, .nil⟩ [] [] ∧
      Typed signature [] TypeEnv.empty .none [] ScopedExecution.Examples.acquisition .unit :=
  typed_beta_step (ticket := .none) (.app (TypingExamples.repeated_function_template_typed []) .unit (List.nil_subset _))
    ScopedExecution.Examples.unit_closed ScopedExecution.Examples.function_closed .none .nil

theorem substitution_preserves_closure_support :
    Typed signature [4] TypeEnv.empty .none [] (.lambda 0 (.resourceRef (.activation 4)))
      (.function .unit (.reference 4) [] [4]) := by
  have original : Typed signature [4] (TypeEnv.empty.extend 9 (.reference 4)) .none []
      (.lambda 0 (.variable 9)) (.function .unit (.reference 4) [] [4]) := by
    refine .lambda (.variable (by simp [TypeEnv.extend]) (List.Subset.refl _)) ?_ ?_
    · simp [Code.dependencies, without, retainedSupport, TypeEnv.extend, Ty.resources]
    · simp [InWorld, Ty.resources]
  exact typed_substitution original (.reference List.mem_cons_self) older_reference_closed

end SubstitutionExamples

end Ash.OneShot.ScopedTyping

#print axioms Ash.OneShot.ScopedTyping.typed_environment_congr
#print axioms Ash.OneShot.ScopedTyping.substitution_support_bound
#print axioms Ash.OneShot.ScopedTyping.typed_substitution
#print axioms Ash.OneShot.ScopedTyping.clauses_typed_substitution
#print axioms Ash.OneShot.ScopedTyping.typed_effect_weaken
#print axioms Ash.OneShot.ScopedTyping.typed_none_ticket_transport
#print axioms Ash.OneShot.ScopedTyping.selected_clause_substitution_typed
#print axioms Ash.OneShot.ScopedTyping.typed_bind_step
#print axioms Ash.OneShot.ScopedTyping.typed_beta_step
#print axioms Ash.OneShot.ScopedTyping.SubstitutionExamples.same_numbered_site_preserves_older_reference
#print axioms Ash.OneShot.ScopedTyping.SubstitutionExamples.repeated_function_beta_is_typed
#print axioms Ash.OneShot.ScopedTyping.SubstitutionExamples.substitution_preserves_closure_support
