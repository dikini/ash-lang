import CallableBodies

/-!
Structural contracts retain callable domains/results through the same expression
syntax. Only physical capture checking projects a contract to storage. Opaque
storage leaves are values and do not confer callable behavior. Independent
ports/effects, usage and runtime-control integration remain separate checks.
-/

namespace Ash.OneShot.CallableContracts
open Instantiation ScopedExpressions ScopedExecution
open Syntax (Dependency without mem_without resourceDependencies mem_resourceDependencies)
open DeclarationResults (signature)

inductive Contract where
  | storage : List Nat → Contract
  | pair : Contract → Contract → Contract
  | function : List Nat → Contract → Contract → Contract
  deriving DecidableEq, Repr

def Contract.storageOf : Contract → List Nat
  | .storage resources => resources
  | .pair left right => left.storageOf ++ right.storageOf
  | .function captures _ _ => captures

abbrev Environment := Nat → Option Contract

def Environment.empty : Environment := fun _ => none
def Environment.extend (environment : Environment) (name : Nat) (contract : Contract) : Environment :=
  fun other => if other = name then some contract else environment other

inductive CaptureAtom (environment : Environment) (bound : List Nat) : Dependency → Prop where
  | resource (included : identity ∈ bound) : CaptureAtom environment bound (.resource identity)
  | «variable» (known : environment name = some contract) (included : contract.storageOf ⊆ bound) :
      CaptureAtom environment bound (.variable name)

inductive Captures (environment : Environment) (bound : List Nat) : List Dependency → Prop where
  | nil : Captures environment bound []
  | cons (head : CaptureAtom environment bound dependency) (tail : Captures environment bound rest) :
      Captures environment bound (dependency :: rest)

inductive Ticket where
  | none
  | bound : Nat → Contract → Contract → Ticket
  deriving DecidableEq, Repr

mutual
inductive Derives (declarations : DeclarationRegistry) : Environment → List Nat → Ticket → Code → Contract → Prop where
  | leaf (value : code.IsValue) (closed : code.ResourceClosed) (captured : Captures environment bound code.dependencies) :
      Derives declarations environment world ticket code (.storage bound)
  | «variable» (known : environment name = some contract) :
      Derives declarations environment world ticket (.variable name) contract
  | pair (leftChecked : Derives declarations environment world ticket left a)
      (rightChecked : Derives declarations environment world ticket right b) :
      Derives declarations environment world ticket (.pair left right) (.pair a b)
  | lambda (bodyChecked : Derives declarations (environment.extend parameter input) world .none body output)
      (captured : Captures environment captures (Code.lambda parameter body).dependencies) :
      Derives declarations environment world ticket (.lambda parameter body) (.function captures input output)
  | app (functionChecked : Derives declarations environment world ticket function (.function captures input output))
      (argumentChecked : Derives declarations environment world ticket argument input) :
      Derives declarations environment world ticket (.app function argument) output
  | bind (initializerChecked : Derives declarations environment world ticket initializer input)
      (bodyChecked : Derives declarations (environment.extend parameter input) world ticket body output) :
      Derives declarations environment world ticket (.bind parameter initializer body) output
  | branch (conditionChecked : Derives declarations environment world ticket condition conditionContract)
      (yesChecked : Derives declarations environment world ticket yes result)
      (noChecked : Derives declarations environment world ticket no result) :
      Derives declarations environment world ticket (.branch condition yes no) result
  | perform (operandChecked : Derives declarations environment world ticket operand operandContract)
      (known : signature declarations requested operation = some (input, output))
      (finite : ClauseResults.PortBound output bound) :
      Derives declarations environment world ticket (.perform (freezeEffect requested) operation operand) (.storage bound)
  | handle (bodyChecked : Derives declarations environment world ticket body answer)
      (clausesChecked : ClausesDerive declarations environment world requested answer clauses)
      (closed : (Code.handle (freezeEffect requested) body clauses).ResourceClosed) :
      Derives declarations environment world ticket (.handle (freezeEffect requested) body clauses) answer
  | resume (operandChecked : Derives declarations environment world (.bound binder input answer) operand input) :
      Derives declarations environment world (.bound binder input answer) (.resume binder operand) answer
  | resource (initializerChecked : Derives declarations environment world ticket initializer input)
      (closed : (Code.resource binder initializer body).ResourceClosed)
      (bodyChecked : ∀ identity, identity ∉ world → Derives declarations environment (world ++ [identity]) ticket
        (body.instantiate (Instantiation.Environment.empty.bind binder identity)) output)
      (outward : output.storageOf ⊆ world) :
      Derives declarations environment world ticket (.resource binder initializer body) output

inductive ClausesDerive (declarations : DeclarationRegistry) :
    Environment → List Nat → Instance → Contract → Clauses → Prop where
  | nil : ClausesDerive declarations environment world requested answer .nil
  | cons (known : signature declarations requested operation = some (inputPort, outputPort))
      (input : ClauseResults.PortBound inputPort argumentBound) (output : ClauseResults.PortBound outputPort resumeBound)
      (bodyChecked : Derives declarations (environment.extend parameter (.storage argumentBound)) world
        (.bound binder (.storage resumeBound) answer) body answer)
      (restChecked : ClausesDerive declarations environment world requested answer rest) :
      ClausesDerive declarations environment world requested answer (.cons operation parameter binder body rest)
end

theorem captures_iff : Captures environment bound dependencies ↔
    ∀ dependency ∈ dependencies, CaptureAtom environment bound dependency := by
  constructor
  · intro checked
    induction checked with
    | nil => intro dependency member; cases member
    | cons head tail ih =>
        intro dependency member
        rcases List.mem_cons.mp member with rfl | later
        · exact head
        · exact ih dependency later
  · intro atoms
    induction dependencies with
    | nil => exact .nil
    | cons head tail ih =>
        exact .cons (atoms _ List.mem_cons_self)
          (ih (fun dependency member => atoms dependency (List.mem_cons_of_mem _ member)))

theorem captured_resources
    (checked : Captures environment bound dependencies) : resourceDependencies dependencies ⊆ bound := by
  intro identity member
  have atom := captures_iff.mp checked (.resource identity) (mem_resourceDependencies.mp member)
  cases atom with
  | resource included => exact included

theorem value_support
    (checked : Derives declarations environment world ticket value contract)
    (isValue : value.IsValue) : resourceDependencies value.dependencies ⊆ contract.storageOf := by
  cases checked with
  | leaf value closed captured => exact captured_resources captured
  | «variable» => cases isValue
  | pair left right =>
      simpa only [Code.dependencies, resource_dependencies_append, Contract.storageOf] using
        append_subset (value_support left isValue.1) (value_support right isValue.2)
  | lambda body captured => exact captured_resources captured
  | app | bind | branch | perform | handle | resume | resource => cases isValue
termination_by sizeOf value

theorem resource_closed
    (checked : Derives declarations environment world ticket code contract) : code.ResourceClosed := by
  induction checked using Derives.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | leaf value closed captured => exact closed
  | «variable» => rfl
  | pair left right ihLeft ihRight | app left right ihLeft ihRight | bind left right ihLeft ihRight =>
      exact List.append_eq_nil_iff.mpr ⟨ihLeft, ihRight⟩
  | lambda body captured ih => exact ih
  | branch condition yes no ihCondition ihYes ihNo =>
      exact List.append_eq_nil_iff.mpr ⟨List.append_eq_nil_iff.mpr ⟨ihCondition, ihYes⟩, ihNo⟩
  | perform operand known finite ih =>
      simpa [Code.ResourceClosed, Code.freeNames, ScopedTyping.frozen_effect_no_free_names] using ih
  | handle body clauses closed ihBody ihClauses | resource initializer closed body outward ihInit ihBody => exact closed
  | resume operand ih => exact ih
  | nil | cons => trivial

def AgreeOn (source destination : Environment) (dependencies : List Dependency) : Prop :=
  ∀ name, Dependency.variable name ∈ dependencies → source name = destination name

theorem agree_left (agree : AgreeOn source destination (left ++ right)) : AgreeOn source destination left :=
  fun _ member => agree _ (List.mem_append_left _ member)

theorem agree_right (agree : AgreeOn source destination (left ++ right)) : AgreeOn source destination right :=
  fun _ member => agree _ (List.mem_append_right _ member)

theorem agree_extend (agree : AgreeOn source destination (without (.variable parameter) dependencies)) :
    AgreeOn (source.extend parameter input) (destination.extend parameter input) dependencies := by
  intro name retained
  by_cases same : name = parameter
  · simp [Environment.extend, same]
  · simp only [Environment.extend, if_neg same]
    exact agree name (mem_without.mpr ⟨retained, by simpa using same⟩)

theorem agree_without_ticket (agree : AgreeOn source destination (without (.ticket binder) dependencies)) :
    AgreeOn source destination dependencies :=
  fun name retained => agree name (mem_without.mpr ⟨retained, by simp⟩)

theorem opened_environment_agree {body : Code} {binder identity : Nat}
    (agree : AgreeOn source destination body.dependencies) :
    AgreeOn source destination (body.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies := by
  intro name member
  rcases List.mem_append.mp (acquisition_dependency_bound binder identity body member) with old | fresh
  · exact agree name old
  · simp at fresh

theorem captures_environment
    (checked : Captures source bound dependencies) (agree : AgreeOn source destination dependencies) :
    Captures destination bound dependencies := by
  apply captures_iff.mpr
  intro dependency member
  cases captures_iff.mp checked dependency member with
  | resource included => exact .resource included
  | «variable» known included => exact .variable ((agree _ member).symm.trans known) included

theorem world_mono (checked : Derives declarations environment world ticket code contract) :
    ∀ nextWorld, world ⊆ nextWorld → Derives declarations environment nextWorld ticket code contract := by
  induction checked using Derives.rec
    (motive_2 := fun environment world requested answer clauses _ =>
      ∀ nextWorld, world ⊆ nextWorld → ClausesDerive declarations environment nextWorld requested answer clauses) with
  | leaf value closed captured => intro next larger; exact .leaf value closed captured
  | «variable» known => intro next larger; exact .variable known
  | pair left right ihLeft ihRight => intro next larger; exact .pair (ihLeft next larger) (ihRight next larger)
  | lambda body captured ih => intro next larger; exact .lambda (ih next larger) captured
  | app function argument ihFunction ihArgument => intro next larger; exact .app (ihFunction next larger) (ihArgument next larger)
  | bind initializer body ihInit ihBody => intro next larger; exact .bind (ihInit next larger) (ihBody next larger)
  | branch condition yes no ihCondition ihYes ihNo =>
      intro next larger; exact .branch (ihCondition next larger) (ihYes next larger) (ihNo next larger)
  | perform operand known finite ih => intro next larger; exact .perform (ih next larger) known finite
  | handle body clauses closed ihBody ihClauses => intro next larger; exact .handle (ihBody next larger) (ihClauses next larger) closed
  | resume operand ih => intro next larger; exact .resume (ih next larger)
  | resource initializer closed body outward ihInit ihBody =>
      intro next larger
      refine .resource (ihInit next larger) closed ?_ (outward.trans larger)
      intro identity fresh
      exact ihBody identity (fun old => fresh (larger old)) (next ++ [identity]) (by
        intro key present
        rcases List.mem_append.mp present with old | current
        · exact List.mem_append_left _ (larger old)
        · exact List.mem_append_right _ current)
  | nil => exact .nil
  | cons known input output body rest ihBody ihRest =>
      rename_i next larger
      exact .cons known input output (ihBody next larger) (ihRest next larger)

mutual
theorem environment_congr
    (checked : Derives declarations source world ticket code contract)
    (agree : AgreeOn source destination code.dependencies) :
    Derives declarations destination world ticket code contract := by
  cases checked with
  | leaf value closed captured => exact .leaf value closed (captures_environment captured agree)
  | «variable» known => exact .variable ((agree _ List.mem_cons_self).symm.trans known)
  | pair left right => exact .pair (environment_congr left (agree_left agree)) (environment_congr right (agree_right agree))
  | lambda body captured => exact .lambda (environment_congr body (agree_extend agree)) (captures_environment captured agree)
  | app function argument => exact .app (environment_congr function (agree_left agree)) (environment_congr argument (agree_right agree))
  | bind initializer body =>
      exact .bind (environment_congr initializer (agree_left agree))
        (environment_congr body (agree_extend (agree_right agree)))
  | branch condition yes no =>
      exact .branch (environment_congr condition (agree_left (agree_left agree)))
        (environment_congr yes (agree_right (agree_left agree))) (environment_congr no (agree_right agree))
  | perform operand known finite => exact .perform (environment_congr operand (agree_right agree)) known finite
  | handle body clauses closed =>
      exact .handle (environment_congr body (agree_right (agree_left agree)))
        (clauses_environment_congr clauses (agree_right agree)) closed
  | resume operand => exact .resume (environment_congr operand (fun name member => agree name (List.mem_cons_of_mem _ member)))
  | resource initializer closed body outward =>
      exact .resource (environment_congr initializer (agree_left agree)) closed
        (fun identity fresh => environment_congr (body identity fresh) (opened_environment_agree (agree_right agree))) outward
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes, Code.instantiation_nodes]; all_goals omega

theorem clauses_environment_congr
    (checked : ClausesDerive declarations source world requested answer clauses)
    (agree : AgreeOn source destination clauses.dependencies) :
    ClausesDerive declarations destination world requested answer clauses := by
  cases checked with
  | nil => exact .nil
  | cons known input output body rest =>
      exact .cons known input output
        (environment_congr body (agree_extend (agree_without_ticket (agree_left agree))))
        (clauses_environment_congr rest (agree_right agree))
termination_by clauses.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Clauses.nodes]; all_goals omega
end

theorem closed_value_environment
    (checked : Derives declarations source world ticket value contract) (closed : ClosedValue value)
    (destination : Environment) : Derives declarations destination world ticket value contract :=
  environment_congr checked (fun _ retained => False.elim (ScopedTyping.closedValue_no_variable closed retained))

theorem value_ticket_transport
    (checked : Derives declarations environment world ticket value contract) (isValue : value.IsValue)
    (destination : Ticket) : Derives declarations environment world destination value contract := by
  cases checked with
  | leaf value closed captured => exact .leaf value closed captured
  | «variable» => cases isValue
  | pair left right => exact .pair (value_ticket_transport left isValue.1 destination) (value_ticket_transport right isValue.2 destination)
  | lambda body captured => exact .lambda body captured
  | app | bind | branch | perform | handle | resume | resource => cases isValue
termination_by sizeOf value

theorem captures_closed (closed : ClosedValue value)
    (bounded : resourceDependencies value.dependencies ⊆ bound) : Captures environment bound value.dependencies := by
  apply captures_iff.mpr
  intro dependency member
  cases dependency with
  | resource identity => exact .resource (bounded (mem_resourceDependencies.mpr member))
  | «variable» name | ticket name => exact False.elim (closed.2.2 _ member)

theorem captures_expand
    (checked : Captures (environment.extend name input) bound dependencies)
    (closed : ClosedValue value) (bounded : resourceDependencies value.dependencies ⊆ input.storageOf) :
    Captures environment bound (ResultSummaries.expandDependencies name value.dependencies dependencies) := by
  apply captures_iff.mpr
  intro dependency member
  obtain ⟨original, occurs, expanded⟩ := List.mem_flatMap.mp member
  have atom := captures_iff.mp checked original occurs
  by_cases same : original = .variable name
  · subst original
    simp only [↓reduceIte] at expanded
    cases atom with
    | «variable» known included =>
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact captures_iff.mp (captures_closed closed (bounded.trans included)) _ expanded
  · have sameDependency : dependency = original := by simpa only [if_neg same, List.mem_singleton] using expanded
    subst dependency
    cases atom with
    | resource included => exact .resource included
    | @«variable» other contract known included =>
        have different : other ≠ name := fun equal => same (congrArg Dependency.variable equal)
        exact .variable (by simpa only [Environment.extend, if_neg different] using known) included

theorem captures_substitution {code : Code}
    (checked : Captures (environment.extend name input) bound code.dependencies)
    (closed : ClosedValue value) (bounded : resourceDependencies value.dependencies ⊆ input.storageOf) :
    Captures environment bound (code.subst name value).dependencies := by
  rw [ResultSummaries.code_substitution_dependencies code name closed]
  exact captures_expand checked closed bounded

@[simp] theorem Environment.extend_shadow (environment : Environment) (name : Nat) (first second : Contract) :
    (environment.extend name first).extend name second = environment.extend name second := by
  funext other
  by_cases same : other = name <;> simp [Environment.extend, same]

theorem Environment.extend_commute (environment : Environment) (first second : Nat) (a b : Contract)
    (different : first ≠ second) :
    (environment.extend first a).extend second b = (environment.extend second b).extend first a := by
  funext other
  by_cases atFirst : other = first
  · subst other; simp [Environment.extend, different]
  · by_cases atSecond : other = second <;> simp [Environment.extend, atFirst, atSecond, Ne.symm different]

mutual
theorem substitution
    (checked : Derives declarations (environment.extend name input) world ticket code result)
    (replacement : Derives declarations environment world .none value input) (closed : ClosedValue value) :
    Derives declarations environment world ticket (code.subst name value) result := by
  cases checked with
  | leaf isValue codeClosed captured =>
      exact .leaf (GenerativeResults.value_substitution_shape isValue)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1)
        (captures_substitution captured closed (value_support replacement closed.1))
  | «variable» known =>
      simp only [Code.subst]
      split
      · rename_i same
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact value_ticket_transport replacement closed.1 _
      · rename_i different
        exact .variable (by simpa [Environment.extend, Ne.symm different] using known)
  | pair left right => exact .pair (substitution left replacement closed) (substitution right replacement closed)
  | lambda body captured =>
      rename_i bodyCode output capturesBound parameter domain
      have capturesAfter := captures_substitution captured closed (value_support replacement closed.1)
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte] at capturesAfter ⊢
        exact .lambda (by simpa only [Environment.extend_shadow] using body) capturesAfter
      · simp only [Code.subst, if_neg same] at capturesAfter ⊢
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input _ same] at rearranged
        exact .lambda (substitution rearranged
          (closed_value_environment replacement closed (environment.extend parameter _)) closed) capturesAfter
  | app function argument => exact .app (substitution function replacement closed) (substitution argument replacement closed)
  | bind initializer body =>
      rename_i initializerCode domain parameter bodyCode
      apply Derives.bind (substitution initializer replacement closed)
      by_cases same : name = parameter
      · subst parameter
        simpa only [ite_true, Environment.extend_shadow] using body
      · simp only [if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact substitution rearranged (closed_value_environment replacement closed (environment.extend parameter domain)) closed
  | branch condition yes no =>
      exact .branch (substitution condition replacement closed) (substitution yes replacement closed) (substitution no replacement closed)
  | perform operand known finite => exact .perform (substitution operand replacement closed) known finite
  | handle body clauses codeClosed =>
      exact .handle (substitution body replacement closed) (clauses_substitution clauses replacement closed)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1)
  | resume operand => exact .resume (substitution operand replacement closed)
  | resource initializer codeClosed body outward =>
      refine .resource (substitution initializer replacement closed)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1) ?_ outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact substitution (body identity fresh)
        (world_mono replacement _ (fun _ member => List.mem_append_left _ member)) closed
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes, Code.instantiation_nodes]; all_goals omega

theorem clauses_substitution
    (checked : ClausesDerive declarations (environment.extend name input) world requested answer clauses)
    (replacement : Derives declarations environment world .none value input) (closed : ClosedValue value) :
    ClausesDerive declarations environment world requested answer (clauses.subst name value) := by
  cases checked with
  | nil => exact .nil
  | cons known inputFinite outputFinite body rest =>
      rename_i operation inputPort outputPort argumentBound resumeBound binder bodyCode restClauses parameter
      apply ClausesDerive.cons known inputFinite outputFinite
      · by_cases same : name = parameter
        · subst parameter
          simpa only [ite_true, Environment.extend_shadow] using body
        · simp only [if_neg same]
          have rearranged := body
          rw [Environment.extend_commute environment name parameter input (.storage argumentBound) same] at rearranged
          exact substitution rearranged
            (closed_value_environment replacement closed (environment.extend parameter (.storage argumentBound))) closed
      · exact clauses_substitution rest replacement closed
termination_by clauses.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Clauses.nodes]; all_goals omega
end

theorem function_value
    (checked : Derives declarations environment world ticket value (.function captures input output))
    (isValue : value.IsValue) :
    ∃ parameter body, value = .lambda parameter body ∧
      Derives declarations (environment.extend parameter input) world .none body output ∧
      Captures environment captures value.dependencies := by
  cases checked with
  | «variable» => cases isValue
  | lambda body captured => exact ⟨_, _, rfl, body, captured⟩
  | app | bind | branch | handle | resume | resource => cases isValue

theorem beta_result
    (checked : Derives declarations environment world ticket (.app (.lambda parameter body) argument) result)
    (closed : ClosedValue argument) :
    Derives declarations environment world .none (body.subst parameter argument) result := by
  cases checked with
  | leaf shape => cases shape
  | app function argumentChecked =>
      cases function with
      | lambda bodyChecked captured => exact substitution bodyChecked (value_ticket_transport argumentChecked closed.1 .none) closed

theorem bind_result
    (checked : Derives declarations environment world ticket (.bind parameter value body) result)
    (closed : ClosedValue value) :
    Derives declarations environment world ticket (body.subst parameter value) result := by
  cases checked with
  | leaf shape => cases shape
  | bind initializer bodyChecked => exact substitution bodyChecked (value_ticket_transport initializer closed.1 .none) closed

theorem beta_step
    (checked : Derives declarations environment world ticket (.app (.lambda parameter body) argument) result)
    (argumentClosed : ClosedValue argument) (functionClosed : ClosedValue (.lambda parameter body)) :
    RawStep ⟨.app (.lambda parameter body) argument, scope, tail⟩ ⟨body.subst parameter argument, .none, tail⟩ [] [] ∧
      Derives declarations environment world .none (body.subst parameter argument) result :=
  ⟨.beta _ _ _ _ _ argumentClosed functionClosed, beta_result checked argumentClosed⟩

theorem bind_step
    (checked : Derives declarations environment world ticket (.bind parameter value body) result)
    (closed : ClosedValue value) (ready : ClosedExcept parameter body) :
    RawStep ⟨.bind parameter value body, scope, tail⟩ ⟨body.subst parameter value, scope, tail⟩ [] [] ∧
      Derives declarations environment world ticket (body.subst parameter value) result :=
  ⟨.bind _ _ _ _ _ closed ready, bind_result checked closed⟩

namespace Examples

def declarations : DeclarationRegistry := fun _ => none
def scalar : Contract := .storage []
def identityContract : Contract := .function [] scalar scalar
def identity : Code := .lambda 0 (.variable 0)
def applyTo17 : Code := .lambda 1 (.app (.variable 1) (.integer 17))
def higherOrder : Code := .app applyTo17 identity
def boundCall : Code := .bind 3 identity (.app (.variable 3) (.integer 17))
def factory : Code := .lambda 0 (.lambda 1 (.variable 0))

theorem identity_checked : Derives declarations Environment.empty [] .none identity identityContract :=
  .lambda (.variable rfl) .nil

theorem higher_order_checked : Derives declarations Environment.empty [] .none higherOrder scalar :=
  .app (captures := []) (.lambda (.app (.variable rfl) (.leaf trivial rfl .nil)) .nil) identity_checked

theorem bound_call_checked : Derives declarations Environment.empty [] .none boundCall scalar :=
  .bind identity_checked (.app (.variable rfl) (.leaf trivial rfl .nil))

theorem factory_checked :
    Derives declarations Environment.empty [7] .none factory
      (.function [] (.storage [7]) (.function [7] scalar (.storage [7]))) :=
  .lambda (.lambda (.variable rfl) (.cons (.variable rfl (List.Subset.refl _)) .nil)) .nil

theorem opaque_binding_cannot_be_called (argument : Code) (result : Contract) :
    ¬ Derives declarations (Environment.empty.extend 3 scalar) [] .none (.app (.variable 3) argument) result := by
  intro checked
  cases checked with
  | leaf shape => cases shape
  | app function argumentChecked => cases function with
      | «variable» known => cases known

theorem bound_call_preserves_function :
    RawStep ⟨boundCall, .none, .nil⟩ ⟨.app identity (.integer 17), .none, .nil⟩ [] [] ∧
      Derives declarations Environment.empty [] .none (.app identity (.integer 17)) scalar := by
  have closed : ClosedValue identity := by
    simp [identity, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, without]
  have ready : ClosedExcept 3 (.app (.variable 3) (.integer 17)) := by
    intro name member
    simpa [Code.dependencies] using member
  simpa [boundCall, Code.subst] using bind_step bound_call_checked closed ready (scope := .none) (tail := .nil)

theorem higher_order_beta_preserves :
    RawStep ⟨higherOrder, .none, .nil⟩ ⟨.app identity (.integer 17), .none, .nil⟩ [] [] ∧
      Derives declarations Environment.empty [] .none (.app identity (.integer 17)) scalar := by
  have argumentClosed : ClosedValue identity := by
    simp [identity, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, without]
  have functionClosed : ClosedValue applyTo17 := by
    simp [applyTo17, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, without]
  simpa [higherOrder, applyTo17, Code.subst] using beta_step higher_order_checked argumentClosed functionClosed
    (scope := .none) (tail := .nil)

end Examples

end Ash.OneShot.CallableContracts

#print axioms Ash.OneShot.CallableContracts.captures_iff
#print axioms Ash.OneShot.CallableContracts.captured_resources
#print axioms Ash.OneShot.CallableContracts.value_support
#print axioms Ash.OneShot.CallableContracts.resource_closed

#print axioms Ash.OneShot.CallableContracts.agree_left

#print axioms Ash.OneShot.CallableContracts.agree_right

#print axioms Ash.OneShot.CallableContracts.agree_extend

#print axioms Ash.OneShot.CallableContracts.agree_without_ticket

#print axioms Ash.OneShot.CallableContracts.opened_environment_agree

#print axioms Ash.OneShot.CallableContracts.captures_environment

#print axioms Ash.OneShot.CallableContracts.world_mono

#print axioms Ash.OneShot.CallableContracts.environment_congr

#print axioms Ash.OneShot.CallableContracts.clauses_environment_congr

#print axioms Ash.OneShot.CallableContracts.closed_value_environment

#print axioms Ash.OneShot.CallableContracts.value_ticket_transport

#print axioms Ash.OneShot.CallableContracts.captures_closed

#print axioms Ash.OneShot.CallableContracts.captures_expand

#print axioms Ash.OneShot.CallableContracts.captures_substitution

#print axioms Ash.OneShot.CallableContracts.Environment.extend_shadow

#print axioms Ash.OneShot.CallableContracts.Environment.extend_commute

#print axioms Ash.OneShot.CallableContracts.substitution

#print axioms Ash.OneShot.CallableContracts.clauses_substitution

#print axioms Ash.OneShot.CallableContracts.function_value

#print axioms Ash.OneShot.CallableContracts.beta_result

#print axioms Ash.OneShot.CallableContracts.bind_result

#print axioms Ash.OneShot.CallableContracts.beta_step

#print axioms Ash.OneShot.CallableContracts.bind_step

#print axioms Ash.OneShot.CallableContracts.Examples.identity_checked

#print axioms Ash.OneShot.CallableContracts.Examples.higher_order_checked

#print axioms Ash.OneShot.CallableContracts.Examples.bound_call_checked

#print axioms Ash.OneShot.CallableContracts.Examples.factory_checked

#print axioms Ash.OneShot.CallableContracts.Examples.opaque_binding_cannot_be_called

#print axioms Ash.OneShot.CallableContracts.Examples.bound_call_preserves_function

#print axioms Ash.OneShot.CallableContracts.Examples.higher_order_beta_preserves
