import CallableRuns

/-!
Full result contracts extended with disposal and scoped cleanup on the same
Code grammar. These are result judgments: independent ticket permissions,
closing readiness, interpreter availability and ownership remain obligations.
-/

namespace Ash.OneShot.CompletionContracts
open Instantiation ScopedExpressions ScopedExecution
open Syntax (Dependency without mem_without resourceDependencies mem_resourceDependencies)
open DeclarationResults (signature)
open CallableContracts

abbrev Contract := CallableContracts.Contract
abbrev Environment := CallableContracts.Environment
abbrev Ticket := CallableContracts.Ticket

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
  | discard : Derives declarations environment world (.bound binder input answer) (.discard binder) (.storage [])
  | cleanup
      (callbackChecked : Derives declarations environment world ticket callback (.function captures (.storage []) (.storage [])))
      (bodyChecked : Derives declarations environment world ticket body output) :
      Derives declarations environment world ticket (.cleanup callback body) output
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
  | app | bind | branch | perform | handle | resume | resource | discard | cleanup => cases isValue
termination_by sizeOf value

theorem resource_closed
    (checked : Derives declarations environment world ticket code contract) : code.ResourceClosed := by
  induction checked using Derives.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | leaf value closed captured => exact closed
  | «variable» | discard => rfl
  | pair left right ihLeft ihRight | app left right ihLeft ihRight | bind left right ihLeft ihRight | cleanup left right ihLeft ihRight =>
      exact List.append_eq_nil_iff.mpr ⟨ihLeft, ihRight⟩
  | lambda body captured ih => exact ih
  | branch condition yes no ihCondition ihYes ihNo =>
      exact List.append_eq_nil_iff.mpr ⟨List.append_eq_nil_iff.mpr ⟨ihCondition, ihYes⟩, ihNo⟩
  | perform operand known finite ih =>
      simpa [Code.ResourceClosed, Code.freeNames, ScopedTyping.frozen_effect_no_free_names] using ih
  | handle body clauses closed ihBody ihClauses | resource initializer closed body outward ihInit ihBody => exact closed
  | resume operand ih => exact ih
  | nil | cons => trivial

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
  | discard => intro next larger; exact .discard
  | cleanup callback body ihCallback ihBody => intro next larger; exact .cleanup (ihCallback next larger) (ihBody next larger)
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
  | discard => exact .discard
  | cleanup callback body =>
      exact .cleanup (environment_congr callback (agree_left agree)) (environment_congr body (agree_right agree))
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
  | app | bind | branch | perform | handle | resume | resource | discard | cleanup => cases isValue
termination_by sizeOf value

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
  | discard => exact .discard
  | cleanup callback body => exact .cleanup (substitution callback replacement closed) (substitution body replacement closed)
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
  | app | bind | branch | handle | resume | resource | cleanup => cases isValue

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

theorem callable_derivation_included
    (checked : CallableContracts.Derives declarations environment world ticket code contract) :
    Derives declarations environment world ticket code contract := by
  induction checked using CallableContracts.Derives.rec
    (motive_2 := fun environment world requested answer clauses _ =>
      ClausesDerive declarations environment world requested answer clauses) with
  | leaf value closed captured => exact .leaf value closed captured
  | «variable» known => exact .variable known
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | lambda body captured ih => exact .lambda ih captured
  | app function argument ihFunction ihArgument => exact .app ihFunction ihArgument
  | bind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform operand known finite ih => exact .perform ih known finite
  | handle body clauses closed ihBody ihClauses => exact .handle ihBody ihClauses closed
  | resume operand ih => exact .resume ih
  | resource initializer closed body outward ihInit ihBody => exact .resource ihInit closed ihBody outward
  | nil => exact .nil
  | cons known input output body rest ihBody ihRest => exact .cons known input output ihBody ihRest

theorem callable_clauses_included
    (checked : CallableContracts.ClausesDerive declarations environment world requested answer clauses) :
    ClausesDerive declarations environment world requested answer clauses := by
  induction checked using CallableContracts.ClausesDerive.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | leaf | «variable» | pair | lambda | app | bind | branch | perform | handle | resume | resource => trivial
  | nil => exact .nil
  | cons known input output body rest ihBody ihRest =>
      exact .cons known input output (callable_derivation_included body) ihRest

theorem cleanup_contract
    (checked : Derives declarations environment world ticket (.cleanup callback body) output) :
    ∃ captures, Derives declarations environment world ticket callback (.function captures (.storage []) (.storage [])) ∧
      Derives declarations environment world ticket body output := by
  cases checked with
  | leaf value => cases value
  | cleanup callback body => exact ⟨_, callback, body⟩

theorem discard_contract
    (checked : Derives declarations environment world ticket (.discard binder) output) :
    output = .storage [] ∧ ∃ input answer, ticket = .bound binder input answer := by
  cases checked with
  | leaf value => cases value
  | discard => exact ⟨rfl, _, _, rfl⟩

namespace Examples
open CallableContracts.Examples (declarations scalar identity identityContract)

def callback : Code := .lambda 1 .unit
def program : Code := .cleanup callback identity

theorem callback_contract (environment : Environment) (world : List Nat) (ticket : Ticket) :
    Derives declarations environment world ticket callback (.function [] scalar scalar) :=
  .lambda (.leaf trivial rfl .nil) .nil

theorem callable_cleanup : Derives declarations Environment.empty [] .none program identityContract :=
  .cleanup (callback_contract _ _ _) (callable_derivation_included CallableContracts.Examples.identity_checked)

theorem disposal_then_callable : Derives declarations Environment.empty [] (.bound 10 scalar identityContract)
    (.bind 4 (.discard 10) identity) identityContract :=
  .bind .discard (.lambda (.variable rfl) .nil)

theorem disposal_needs_bound_ticket :
    ¬ Derives declarations Environment.empty [] .none (.discard 10) scalar := by
  intro checked
  obtain ⟨same, input, answer, impossible⟩ := discard_contract checked
  cases impossible

theorem storage_callback_is_insufficient :
    ¬ Derives declarations (Environment.empty.extend 1 scalar) [] .none
      (.cleanup (.variable 1) identity) identityContract := by
  intro checked
  obtain ⟨captures, callback, body⟩ := cleanup_contract checked
  cases callback with
  | «variable» known => cases known

theorem scalar_result_is_not_unit_typing :
    Derives declarations Environment.empty [] .none (.lambda 1 (.integer 17)) (.function [] scalar scalar) ∧
      ¬ ScopedPorts.Typed (signature declarations) [] ScopedPorts.TypeEnv.empty .none []
        (.lambda 1 (.integer 17)) (.function .unit .unit []) := by
  constructor
  · exact .lambda (.leaf trivial rfl .nil) .nil
  · intro typed
    cases typed with
    | lambda body captured => cases body

end Examples

end Ash.OneShot.CompletionContracts

#print axioms Ash.OneShot.CompletionContracts.value_support
#print axioms Ash.OneShot.CompletionContracts.resource_closed
#print axioms Ash.OneShot.CompletionContracts.world_mono
#print axioms Ash.OneShot.CompletionContracts.environment_congr
#print axioms Ash.OneShot.CompletionContracts.clauses_environment_congr
#print axioms Ash.OneShot.CompletionContracts.closed_value_environment
#print axioms Ash.OneShot.CompletionContracts.value_ticket_transport
#print axioms Ash.OneShot.CompletionContracts.substitution
#print axioms Ash.OneShot.CompletionContracts.clauses_substitution
#print axioms Ash.OneShot.CompletionContracts.function_value
#print axioms Ash.OneShot.CompletionContracts.beta_result
#print axioms Ash.OneShot.CompletionContracts.bind_result
#print axioms Ash.OneShot.CompletionContracts.beta_step
#print axioms Ash.OneShot.CompletionContracts.bind_step
#print axioms Ash.OneShot.CompletionContracts.callable_derivation_included
#print axioms Ash.OneShot.CompletionContracts.callable_clauses_included
#print axioms Ash.OneShot.CompletionContracts.cleanup_contract
#print axioms Ash.OneShot.CompletionContracts.discard_contract
#print axioms Ash.OneShot.CompletionContracts.Examples.callback_contract
#print axioms Ash.OneShot.CompletionContracts.Examples.callable_cleanup
#print axioms Ash.OneShot.CompletionContracts.Examples.disposal_then_callable
#print axioms Ash.OneShot.CompletionContracts.Examples.disposal_needs_bound_ticket
#print axioms Ash.OneShot.CompletionContracts.Examples.storage_callback_is_insufficient

#print axioms Ash.OneShot.CompletionContracts.Examples.scalar_result_is_not_unit_typing
