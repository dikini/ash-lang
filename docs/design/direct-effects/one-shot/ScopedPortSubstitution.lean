import ScopedPortTyping

/-!
Closed ordinary substitution for declared port typing, independently of stored
resource support. Generative openings retain the same operation signature.
The support theorem from ScopedPortTyping is joined explicitly at parameter
binding; neither theorem alone establishes source escape or disposal safety.
-/

namespace Ash.OneShot.ScopedPorts
open Instantiation ScopedExpressions ScopedExecution
open Syntax (Dependency without mem_without)
open ScopedTyping (World clauseKeys clause_keys_substitution)

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
theorem agree_without_ticket (agree : AgreeOn source destination (without (.ticket binder) dependencies)) :
    AgreeOn source destination dependencies :=
  fun name retained => agree name (mem_without.mpr ⟨retained, by simp⟩)

theorem opened_body_environment_agree {body : Code} {binder identity : Nat}
    (agree : AgreeOn source destination body.dependencies) :
    AgreeOn source destination (body.instantiate (Environment.empty.bind binder identity)).dependencies := by
  intro name member
  rcases List.mem_append.mp (acquisition_dependency_bound binder identity body member) with old | fresh
  · exact agree name old
  · simp at fresh

theorem in_world_mono (formed : InWorld world type) (larger : world ⊆ next) : InWorld next type :=
  List.Subset.trans formed larger

@[simp] theorem TypeEnv.extend_shadow (environment : TypeEnv) (name : Nat) (first second : Port) :
    (environment.extend name first).extend name second = environment.extend name second := by
  funext other
  by_cases same : other = name <;> simp [TypeEnv.extend, same]

theorem TypeEnv.extend_commute (environment : TypeEnv) (first second : Nat) (a b : Port)
    (different : first ≠ second) :
    (environment.extend first a).extend second b = (environment.extend second b).extend first a := by
  funext other
  by_cases atFirst : other = first
  · subst other
    simp [TypeEnv.extend, different]
  · by_cases atSecond : other = second <;> simp [TypeEnv.extend, atFirst, atSecond, Ne.symm different]

theorem typed_world_weaken (typed : Typed signature world environment ticket allowed code type) :
    ∀ next, world ⊆ next → Typed signature next environment ticket allowed code type := by
  induction typed using Typed.rec
    (motive_2 := fun world environment effect answer residual clauses _ =>
      ∀ next, world ⊆ next → ClausesTyped signature next environment effect answer residual clauses) with
  | unit => intro next larger; exact .unit
  | boolean => intro next larger; exact .boolean
  | integer => intro next larger; exact .integer
  | «variable» known formed => intro next larger; exact .variable known (in_world_mono formed larger)
  | reference issued => intro next larger; exact .reference (larger issued)
  | pair _ _ left right => intro next larger; exact .pair (left next larger) (right next larger)
  | lambda _ formed body => intro next larger; exact .lambda (body next larger) (in_world_mono formed larger)
  | app _ _ effects function argument => intro next larger; exact .app (function next larger) (argument next larger) effects
  | bind _ _ initializer suffix => intro next larger; exact .bind (initializer next larger) (suffix next larger)
  | branch _ _ _ condition yes no => intro next larger; exact .branch (condition next larger) (yes next larger) (no next larger)
  | perform operation available _ formed operand =>
      intro next larger; exact .perform operation available (operand next larger) (in_world_mono formed larger)
  | handle _ _ coverage unique effects body clauses =>
      intro next larger; exact .handle (body next larger) (clauses next larger) coverage unique effects
  | resume _ effects formed operand => intro next larger; exact .resume (operand next larger) effects (in_world_mono formed larger)
  | discard effects => intro next larger; exact .discard effects
  | resource _ _ resultBound effectsBound effects initializer body =>
      intro next larger
      refine .resource (initializer next larger) ?_ (in_world_mono resultBound larger) (List.Subset.trans effectsBound larger) effects
      intro identity fresh
      exact body identity (fun old => fresh (larger old)) (next ++ [identity]) (by
        intro key present
        rcases List.mem_append.mp present with old | current
        · exact List.mem_append_left _ (larger old)
        · exact List.mem_append_right _ current)
  | cleanup _ _ effects action body => intro next larger; exact .cleanup (action next larger) (body next larger) effects
  | nil => exact .nil
  | cons operation _ _ body rest =>
      rename_i next larger
      exact .cons operation (body next larger) (rest next larger)

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
  | lambda body formed =>
      exact .lambda (typed_environment_congr body (agree_extend agree)) formed
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
  typed_environment_congr typed (fun _ retained => False.elim (ScopedTyping.closedValue_no_variable closed retained))
theorem typed_value_transport (typed : Typed signature world environment ticket allowed value type)
    (isValue : value.IsValue) (destination : Ticket) (effects : List Instance) :
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
  | lambda body formed => exact .lambda body formed
  | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases isValue
termination_by sizeOf value

mutual
/-- Closed substitution preserves declared ports through the complete scoped grammar.
    Resource support is transported by the separate Support judgment. -/
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
  | lambda body formed =>
      rename_i latent bodyExpr output inputParam parameter
      by_cases same : name = parameter
      · subst parameter
        simp [Code.subst]
        exact .lambda (by simpa only [TypeEnv.extend_shadow] using body) formed
      · simp only [Code.subst, if_neg same]
        apply Typed.lambda
        · have rearranged := body
          rw [TypeEnv.extend_commute environment name parameter input inputParam same] at rearranged
          exact typed_substitution rearranged
            (closed_value_environment_transport replacement closed (environment.extend parameter inputParam)) closed
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




theorem typed_effect_weaken (typed : Typed signature world environment ticket allowed expression type)
    (bound : allowed ⊆ larger) : Typed signature world environment ticket larger expression type := by
  induction typed using Typed.rec (motive_2 := fun _ _ _ _ _ _ _ => True) generalizing larger with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» found formed => exact .variable found formed
  | reference issued => exact .reference issued
  | pair left right ihLeft ihRight => exact .pair (ihLeft bound) (ihRight bound)
  | lambda body formed ih => exact .lambda body formed
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
      | lambda body formed =>
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

/-- Type and support evidence use the same inserted value and source body.
    This applies to ordinary binding and to the selected handler parameter. -/
theorem parameter_binding_preserves_ports_and_support
    (bodyTyped : Typed signature world (TypeEnv.empty.extend parameter input) ticket allowed body output)
    (valueTyped : Typed signature world TypeEnv.empty .none [] value input)
    (closed : ClosedValue value)
    (valueSupport : Syntax.resourceDependencies value.dependencies ⊆ resources)
    (bodySupport : Support.evaluate (Support.extend Support.empty parameter resources) body.dependencies ⊆ available) :
    Typed signature world TypeEnv.empty ticket allowed (body.subst parameter value) output ∧
    Syntax.resourceDependencies (body.subst parameter value).dependencies ⊆ available :=
  ⟨typed_substitution bodyTyped valueTyped closed,
    Support.parameter_binding_preserves_support closed valueSupport bodySupport⟩

/-- The selected clause's type derivation and independently checked parameter
    support establish both properties of its actual substituted body. -/
theorem selected_clause_binding_preserves_ports_and_support
    (selected : ClauseAt operation clauses parameter binder body)
    (clausesTyped : ClausesTyped signature world TypeEnv.empty effect answer residual clauses)
    (known : signature effect operation = some (input, output))
    (operandTyped : Typed signature world TypeEnv.empty ticket allowed operand input)
    (closed : ClosedValue operand)
    (operandSupport : Syntax.resourceDependencies operand.dependencies ⊆ resources)
    (bodySupport : Support.evaluate (Support.extend Support.empty parameter resources) body.dependencies ⊆ available) :
    Typed signature world TypeEnv.empty (.bound binder output answer residual residual) residual
      (body.subst parameter operand) answer ∧
    Syntax.resourceDependencies (body.subst parameter operand).dependencies ⊆ available :=
  ⟨selected_clause_substitution_typed selected clausesTyped known operandTyped closed,
    Support.parameter_binding_preserves_support closed operandSupport bodySupport⟩

namespace SubstitutionExamples
open ScopedSignatureGap.Examples
open Ash.OneShot.ScopedPorts.Examples (signature callbackPort payload_typed)

def factoryBody : Code := .lambda 6 (.app (.variable 5) .unit)

theorem factory_typed :
    Typed signature [0] (TypeEnv.empty.extend 5 callbackPort) .none [] factoryBody callbackPort := by
  apply Typed.lambda
  · exact .app (.variable (by simp [TypeEnv.extend, callbackPort]) (List.nil_subset _)) .unit (List.nil_subset _)
  · exact List.nil_subset _

/-- A returned wrapper retains the payload's resource with the same declared
    arrow port. Both outputs use the actual substitution, not a type support list. -/
theorem higher_order_parameter_transport :
    Typed signature [0] TypeEnv.empty .none [] (factoryBody.subst 5 (payload (.activation 0))) callbackPort ∧
    Syntax.resourceDependencies (factoryBody.subst 5 (payload (.activation 0))).dependencies ⊆ [0] := by
  apply parameter_binding_preserves_ports_and_support (resources := [0]) factory_typed
    (payload_typed (by simp)) payload_closed
  · simp [payload, Code.dependencies, Syntax.without, Syntax.resourceDependencies]
  · simp [factoryBody, Code.dependencies, Syntax.without, Support.evaluate, Support.extend]

theorem higher_order_result_still_retains :
    Syntax.resourceDependencies (factoryBody.subst 5 (payload (.activation 0))).dependencies = [0] ∧
    callbackPort.resources = [] := by
  simp [factoryBody, Code.subst, payload, Code.dependencies, Syntax.without, Syntax.resourceDependencies,
    callbackPort, Port.resources]

end SubstitutionExamples

end Ash.OneShot.ScopedPorts

#print axioms Ash.OneShot.ScopedPorts.opened_body_environment_agree
#print axioms Ash.OneShot.ScopedPorts.TypeEnv.extend_shadow
#print axioms Ash.OneShot.ScopedPorts.TypeEnv.extend_commute
#print axioms Ash.OneShot.ScopedPorts.typed_world_weaken
#print axioms Ash.OneShot.ScopedPorts.typed_environment_congr
#print axioms Ash.OneShot.ScopedPorts.clauses_environment_congr
#print axioms Ash.OneShot.ScopedPorts.closed_value_environment_transport
#print axioms Ash.OneShot.ScopedPorts.typed_value_transport
#print axioms Ash.OneShot.ScopedPorts.typed_substitution
#print axioms Ash.OneShot.ScopedPorts.clauses_typed_substitution
#print axioms Ash.OneShot.ScopedPorts.parameter_binding_preserves_ports_and_support
#print axioms Ash.OneShot.ScopedPorts.typed_effect_weaken
#print axioms Ash.OneShot.ScopedPorts.selected_clause_typed
#print axioms Ash.OneShot.ScopedPorts.selected_clause_substitution_typed
#print axioms Ash.OneShot.ScopedPorts.typed_bind_reduction
#print axioms Ash.OneShot.ScopedPorts.typed_beta_reduction
#print axioms Ash.OneShot.ScopedPorts.typed_bind_step
#print axioms Ash.OneShot.ScopedPorts.typed_beta_step
#print axioms Ash.OneShot.ScopedPorts.selected_clause_binding_preserves_ports_and_support
#print axioms Ash.OneShot.ScopedPorts.SubstitutionExamples.factory_typed
#print axioms Ash.OneShot.ScopedPorts.SubstitutionExamples.higher_order_parameter_transport
#print axioms Ash.OneShot.ScopedPorts.SubstitutionExamples.higher_order_result_still_retains
