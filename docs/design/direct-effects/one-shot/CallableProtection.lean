import ProtectionContracts

/-!
Source-derived protection demands for the callable computation component of
ScopedExpressions.Code. Function contracts retain exact latent footprints;
closed-value substitution and actual beta/bind steps preserve them. Fresh
resource bodies expose their outward footprint after local cell interpretation.
Handler and ticket source rules still require integration. This is
independent of ordinary port typing and physical resource-support contracts.
-/

namespace Ash.OneShot.CallableProtection
open ScopedExpressions ScopedExecution ProtectionContracts
open Instantiation (freezeEffect)
open Syntax (Dependency without mem_without)

inductive Contract where
  /-- A non-callable protection shape, not the ordinary Unit port type. -/
  | scalar
  | pair : Contract → Contract → Contract
  | function : Contract → Contract → Footprint → Contract
  deriving DecidableEq, Repr

abbrev Environment := Nat → Option Contract
abbrev Operations := Instance → Nat → Option (Contract × Contract)

def Environment.empty : Environment := fun _ => none
def Environment.extend (environment : Environment) (name : Nat) (contract : Contract) : Environment :=
  fun other => if other = name then some contract else environment other

/-- The builtin handles exactly its own cell requests. All other demands keep
    their order and protection mode. -/
def outsideCell (identity : Nat) (row : Footprint) : Footprint :=
  row.filter (fun request => request.effect != .cell identity)

/-- Function bodies expose latent demands; evaluating a function value does not
    execute them. Operations carry qualified input/result contracts supplied by
    declarations, whose implementation correctness remains independent. -/
inductive Summarizes (operations : Operations) : Environment → Code → Contract → Footprint → Prop where
  | unit : Summarizes operations environment .unit .scalar []
  | boolean : Summarizes operations environment (.boolean value) .scalar []
  | integer : Summarizes operations environment (.integer value) .scalar []
  | reference : Summarizes operations environment (.resourceRef resource) .scalar []
  | «variable» (known : environment name = some contract) :
      Summarizes operations environment (.variable name) contract []
  | pair (left : Summarizes operations environment a first leftRow)
      (right : Summarizes operations environment b second rightRow) :
      Summarizes operations environment (.pair a b) (.pair first second) (leftRow ++ rightRow)
  | lambda (body : Summarizes operations (environment.extend parameter input) code output latent) :
      Summarizes operations environment (.lambda parameter code) (.function input output latent) []
  | app (function : Summarizes operations environment f (.function input output latent) functionRow)
      (argument : Summarizes operations environment a input argumentRow) :
      Summarizes operations environment (.app f a) output (functionRow ++ argumentRow ++ latent)
  | bind (initializer : Summarizes operations environment a input initializerRow)
      (body : Summarizes operations (environment.extend parameter input) b output bodyRow) :
      Summarizes operations environment (.bind parameter a b) output (initializerRow ++ bodyRow)
  | branch (condition : Summarizes operations environment test .scalar conditionRow)
      (yes : Summarizes operations environment a output yesRow)
      (no : Summarizes operations environment b output noRow) :
      Summarizes operations environment (.branch test a b) output (conditionRow ++ yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output))
      (operand : Summarizes operations environment value input operandRow) :
      Summarizes operations environment (.perform (freezeEffect effect) operation value) output
        (operandRow ++ [⟨effect, operation, false⟩])
  | cleanup (callback : Summarizes operations environment action (.function .scalar .scalar latent) callbackRow)
      (body : Summarizes operations environment code output bodyRow) :
      Summarizes operations environment (.cleanup action code) output
        (callbackRow ++ bodyRow ++ qualify true latent)
  | resource {world : List Nat} {bodyRow : Nat → Footprint}
      (initializer : Summarizes operations environment initial .scalar initialRow)
      (body : ∀ identity, identity ∉ world →
        Summarizes operations environment
          (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (outward : ∀ identity, identity ∉ world → outsideCell identity (bodyRow identity) = row) :
      Summarizes operations environment (.resource binder initial code) output (initialRow ++ row)

theorem value_has_no_immediate_demands (summary : Summarizes operations environment value contract footprint)
    (isValue : value.IsValue) : footprint = [] := by
  induction summary with
  | unit | boolean | integer | reference | lambda => rfl
  | «variable» => cases isValue
  | pair left right ihLeft ihRight => simp [ihLeft isValue.1, ihRight isValue.2]
  | app | bind | branch | perform | cleanup | resource => cases isValue

def AgreeOn (source destination : Environment) (dependencies : List Dependency) : Prop :=
  ∀ name, Dependency.variable name ∈ dependencies → source name = destination name

theorem agree_left (agree : AgreeOn source destination (left ++ right)) : AgreeOn source destination left :=
  fun _ member => agree _ (List.mem_append_left _ member)
theorem agree_right (agree : AgreeOn source destination (left ++ right)) : AgreeOn source destination right :=
  fun _ member => agree _ (List.mem_append_right _ member)

theorem agree_extend (agree : AgreeOn source destination (without (.variable binder) dependencies)) :
    AgreeOn (source.extend binder contract) (destination.extend binder contract) dependencies := by
  intro name member
  by_cases same : name = binder
  · simp [Environment.extend, same]
  · simp only [Environment.extend, if_neg same]
    exact agree name (mem_without.mpr ⟨member, by simpa using same⟩)

theorem agree_resource_opening {code : Code} {binder identity : Nat}
    (agree : AgreeOn source destination code.dependencies) :
    AgreeOn source destination (code.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies := by
  intro name member
  rcases List.mem_append.mp (ScopedExpressions.acquisition_dependency_bound binder identity code member) with original | introduced
  · exact agree name original
  · simp at introduced

theorem environment_congr (summary : Summarizes operations source code contract footprint)
    (agree : AgreeOn source destination code.dependencies) :
    Summarizes operations destination code contract footprint := by
  induction summary generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference
  | «variable» known => exact .variable ((agree _ List.mem_cons_self).symm.trans known)
  | pair left right ihLeft ihRight => exact .pair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | lambda body ih => exact .lambda (ih (agree_extend agree))
  | app function argument ihFunction ihArgument => exact .app (ihFunction (agree_left agree)) (ihArgument (agree_right agree))
  | bind initializer body ihInit ihBody => exact .bind (ihInit (agree_left agree)) (ihBody (agree_extend (agree_right agree)))
  | branch condition yes no ihCondition ihYes ihNo =>
      exact .branch (ihCondition (agree_left (agree_left agree))) (ihYes (agree_right (agree_left agree))) (ihNo (agree_right agree))
  | perform known operand ih => exact .perform known (ih (agree_right agree))
  | cleanup callback body ihCallback ihBody => exact .cleanup (ihCallback (agree_left agree)) (ihBody (agree_right agree))
  | resource initializer body outward ihInit ihBody =>
      exact .resource (ihInit (agree_left agree))
        (fun identity fresh => ihBody identity fresh (agree_resource_opening (agree_right agree))) outward

theorem closed_value_environment (summary : Summarizes operations source value contract footprint)
    (closed : ClosedValue value) (destination : Environment) :
    Summarizes operations destination value contract footprint :=
  environment_congr summary (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))

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

/-- Substitution retains the full callable contract and the exact footprint,
    including demands latent inside returned or higher-order functions. -/
theorem substitution
    (summary : Summarizes operations (environment.extend name input) code result footprint)
    (replacement : Summarizes operations environment value input []) (closed : ClosedValue value) :
    Summarizes operations environment (code.subst name value) result footprint := by
  cases summary with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference
  | «variable» known =>
      simp only [Code.subst]
      split
      · rename_i same
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact replacement
      · rename_i different
        exact .variable (by simpa [Environment.extend, Ne.symm different] using known)
  | pair left right => exact .pair (substitution left replacement closed) (substitution right replacement closed)
  | lambda body =>
      rename_i bodyCode output latent parameter domain
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte]
        exact .lambda (by simpa only [Environment.extend_shadow] using body)
      · simp only [Code.subst, if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact .lambda (substitution rearranged
          (closed_value_environment replacement closed (environment.extend parameter domain)) closed)
  | app function argument => exact .app (substitution function replacement closed) (substitution argument replacement closed)
  | bind initializer body =>
      rename_i a domain initializerRow parameter b bodyRow
      apply Summarizes.bind (substitution initializer replacement closed)
      by_cases same : name = parameter
      · subst parameter
        simpa only [ite_true, Environment.extend_shadow] using body
      · simp only [if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact substitution rearranged (closed_value_environment replacement closed (environment.extend parameter domain)) closed
  | branch condition yes no =>
      exact .branch (substitution condition replacement closed)
        (substitution yes replacement closed) (substitution no replacement closed)
  | perform known operand => exact .perform known (substitution operand replacement closed)
  | cleanup callback body => exact .cleanup (substitution callback replacement closed) (substitution body replacement closed)
  | resource initializer body outward =>
      apply Summarizes.resource (substitution initializer replacement closed) _ outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact substitution (body identity fresh) replacement closed
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes, Code.instantiation_nodes]; all_goals omega

def CheckedAt (operations : Operations) (environment : Environment) (context : ProtectionContracts.Context)
    (code : Code) (contract : Contract) : Prop :=
  ∃ footprint, Summarizes operations environment code contract footprint ∧ checkFootprint context footprint = true

theorem beta_summary
    (summary : Summarizes operations environment (.app (.lambda parameter body) argument) result footprint)
    (closed : ClosedValue argument) : Summarizes operations environment (body.subst parameter argument) result footprint := by
  cases summary with
  | app function argument => cases function with
      | lambda body =>
          have empty := value_has_no_immediate_demands argument closed.1
          subst_vars
          simpa using substitution body argument closed

theorem bind_summary
    (summary : Summarizes operations environment (.bind parameter value body) result footprint)
    (closed : ClosedValue value) : Summarizes operations environment (body.subst parameter value) result footprint := by
  cases summary with
  | bind initializer body =>
      have empty := value_has_no_immediate_demands initializer closed.1
      subst_vars
      simpa using substitution body initializer closed

theorem beta_step
    (checked : CheckedAt operations environment context (.app (.lambda parameter body) argument) result)
    (argumentClosed : ClosedValue argument) (functionClosed : ClosedValue (.lambda parameter body)) :
    RawStep ⟨.app (.lambda parameter body) argument, scope, tail⟩
      ⟨body.subst parameter argument, .none, tail⟩ [] [] ∧
      CheckedAt operations environment context (body.subst parameter argument) result := by
  obtain ⟨footprint, summary, admitted⟩ := checked
  exact ⟨.beta _ _ _ _ _ argumentClosed functionClosed,
    footprint, beta_summary summary argumentClosed, admitted⟩

theorem bind_step
    (checked : CheckedAt operations environment context (.bind parameter value body) result)
    (closed : ClosedValue value) (ready : ClosedExcept parameter body) :
    RawStep ⟨.bind parameter value body, scope, tail⟩
      ⟨body.subst parameter value, scope, tail⟩ [] [] ∧
      CheckedAt operations environment context (body.subst parameter value) result := by
  obtain ⟨footprint, summary, admitted⟩ := checked
  exact ⟨.bind _ _ _ _ _ closed ready, footprint, bind_summary summary closed, admitted⟩

theorem actual_request_admitted
    (checked : CheckedAt operations environment context (.perform (freezeEffect effect) operation operand) result) :
    checkRequest context ⟨effect, operation, false⟩ = true := by
  obtain ⟨footprint, summary, admitted⟩ := checked
  generalize shape : Code.perform (freezeEffect effect) operation operand = code at summary
  cases summary <;> try cases shape
  case perform known operand =>
    obtain ⟨effectEq, operationEq, operandEq⟩ := Code.perform.inj shape
    have same := freeze_effect_injective effectEq
    cases same; cases operationEq; cases operandEq
    simp only [checkFootprint, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at admitted
    exact admitted.2

/-- Source cleanup contributes the callback's latent row under a running
    barrier. Independent port typing must still establish Unit → Unit. -/
theorem cleanup_invocation_checked
    (checked : CheckedAt operations environment context (.cleanup callback body) result)
    (isValue : callback.IsValue) :
    CheckedAt operations environment (.barrier true :: context) (.app callback .unit) .scalar := by
  obtain ⟨footprint, summary, admitted⟩ := checked
  cases summary with
  | cleanup callback body =>
      have empty := value_has_no_immediate_demands callback isValue
      subst_vars
      rw [check_footprint_append] at admitted
      have latentChecked := (Bool.and_eq_true_iff.mp admitted).2
      rw [check_qualified] at latentChecked
      exact ⟨_, by simpa using Summarizes.app callback Summarizes.unit, latentChecked⟩

namespace Examples

def effect : Instance := .user 0 []
def operations : Operations := fun requested operation =>
  if requested = effect ∧ operation = 0 then some (.scalar, .scalar) else none
def latent : Footprint := [⟨effect, 0, false⟩]
def functionContract : Contract := .function .scalar .scalar latent
def function : Code := .lambda 0 (.perform (freezeEffect effect) 0 .unit)
def applyFunction : Code := .lambda 1 (.app (.variable 1) .unit)
def disposeContext : ProtectionContracts.Context := [.handler effect 11 [(0, ⟨true, some [], none⟩)]]
def resumeContext : ProtectionContracts.Context := [.handler effect 11 [(0, ⟨false, some [], some []⟩)]]

theorem function_summary : Summarizes operations environment function functionContract [] :=
  .lambda (.perform (by simp [operations]) .unit)

theorem function_closed : ClosedValue function := ⟨trivial, rfl, by intro dependency member; cases member⟩
theorem unit_closed : ClosedValue .unit := ⟨trivial, rfl, by intro dependency member; cases member⟩

theorem creation_checked (context : ProtectionContracts.Context) :
    CheckedAt operations environment context function functionContract := ⟨[], function_summary, rfl⟩

theorem ordinary_invocation_checked : CheckedAt operations environment disposeContext (.app function .unit) .scalar :=
  ⟨latent, by simpa [latent] using Summarizes.app function_summary Summarizes.unit, by decide⟩

theorem protected_invocation_rejected :
    ¬ CheckedAt operations environment (.barrier true :: disposeContext) (.app function .unit) .scalar := by
  intro checked
  have after := (beta_step checked unit_closed function_closed (scope := .none) (tail := .nil)).2
  have request := actual_request_admitted after
  have rejected : checkRequest (.barrier true :: disposeContext) ⟨effect, 0, false⟩ = false := by decide
  rw [rejected] at request
  cases request

theorem higher_order_summary : Summarizes operations environment applyFunction
    (.function functionContract .scalar latent) [] := by
  apply Summarizes.lambda
  simpa [functionContract] using Summarizes.app
    (Summarizes.variable (operations := operations)
      (show (environment.extend 1 functionContract) 1 = some functionContract by simp [Environment.extend])) Summarizes.unit

theorem higher_order_substitution : Summarizes operations environment
    ((Code.app (.variable 1) .unit).subst 1 function) .scalar latent := by
  apply substitution (input := functionContract) (replacement := function_summary) (closed := function_closed)
  simpa [functionContract] using Summarizes.app
    (Summarizes.variable (operations := operations)
      (show (environment.extend 1 functionContract) 1 = some functionContract by simp [Environment.extend])) Summarizes.unit

theorem cleanup_checked : CheckedAt operations environment resumeContext (.cleanup function .unit) .scalar :=
  ⟨qualify true latent, by simpa using Summarizes.cleanup function_summary Summarizes.unit, by decide⟩

theorem cleanup_rejected : ¬ CheckedAt operations environment disposeContext (.cleanup function .unit) .scalar :=
  fun checked => protected_invocation_rejected (cleanup_invocation_checked checked trivial)

end Examples

end Ash.OneShot.CallableProtection

#print axioms Ash.OneShot.CallableProtection.value_has_no_immediate_demands
#print axioms Ash.OneShot.CallableProtection.agree_left
#print axioms Ash.OneShot.CallableProtection.agree_right
#print axioms Ash.OneShot.CallableProtection.agree_extend
#print axioms Ash.OneShot.CallableProtection.agree_resource_opening
#print axioms Ash.OneShot.CallableProtection.environment_congr
#print axioms Ash.OneShot.CallableProtection.closed_value_environment
#print axioms Ash.OneShot.CallableProtection.Environment.extend_shadow
#print axioms Ash.OneShot.CallableProtection.Environment.extend_commute
#print axioms Ash.OneShot.CallableProtection.substitution
#print axioms Ash.OneShot.CallableProtection.beta_summary
#print axioms Ash.OneShot.CallableProtection.bind_summary
#print axioms Ash.OneShot.CallableProtection.beta_step
#print axioms Ash.OneShot.CallableProtection.bind_step
#print axioms Ash.OneShot.CallableProtection.actual_request_admitted
#print axioms Ash.OneShot.CallableProtection.cleanup_invocation_checked
#print axioms Ash.OneShot.CallableProtection.Examples.function_summary
#print axioms Ash.OneShot.CallableProtection.Examples.function_closed
#print axioms Ash.OneShot.CallableProtection.Examples.unit_closed
#print axioms Ash.OneShot.CallableProtection.Examples.creation_checked
#print axioms Ash.OneShot.CallableProtection.Examples.ordinary_invocation_checked
#print axioms Ash.OneShot.CallableProtection.Examples.protected_invocation_rejected
#print axioms Ash.OneShot.CallableProtection.Examples.higher_order_summary
#print axioms Ash.OneShot.CallableProtection.Examples.higher_order_substitution
#print axioms Ash.OneShot.CallableProtection.Examples.cleanup_checked
#print axioms Ash.OneShot.CallableProtection.Examples.cleanup_rejected
