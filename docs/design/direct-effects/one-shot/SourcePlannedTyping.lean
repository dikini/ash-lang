import SourcePlanSignatures
import SourceDependencySubstitution

/-! Source typing authenticates stable recursive signatures against actual code. Function
types retain the body signature used by their lambda derivation.
The earlier hereditary judgment supplies its existing type, effect, resource
and ownership obligations at exactly the same source and dependency indices. -/
namespace Ash.OneShot.SourcePlannedTyping
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures (Signature signature clauseSignatures)

inductive Value where
  | unit | boolean | integer
  | reference : Nat → Value
  | pair : Value → Value → Value
  | function : Value → Value → List Instance → Footprint → {dependencies : Dependencies} → Signature dependencies → Value

def Value.erase : Value → SourceDependencyAnnotations.Value
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference identity => .reference identity
  | .pair left right => .pair left.erase right.erase
  | @Value.function input output requests latent dependencies _ =>
      .function input.erase output.erase requests latent dependencies

abbrev Environment := Nat → Option Value
def Environment.extend (environment : Environment) (name : Nat) (value : Value) : Environment :=
  fun other => if other = name then some value else environment other
def Environment.erase (environment : Environment) : SourceDependencyAnnotations.Environment :=
  fun name => (environment name).map Value.erase

abbrev Operations := Instance → Nat → Option (Value × Value)
def Operations.erase (operations : Operations) : SourceDependencyAnnotations.Operations :=
  fun effect operation => (operations effect operation).map (fun pair => (pair.1.erase, pair.2.erase))

structure Contract where
  input : Value
  answer : Value
  held : Bool
  resumeDemand : List Nat
  resumeRow : Footprint
  closeDemand : List Nat
  closeRow : Option Footprint
  resumeEffects : List Instance
  closeEffects : List Instance

def Contract.erase (contract : Contract) : SourceDependencyAnnotations.Contract :=
  ⟨contract.input.erase, contract.answer.erase, contract.held, contract.resumeDemand,
    contract.resumeRow, contract.closeDemand, contract.closeRow, contract.resumeEffects, contract.closeEffects⟩

abbrev Contracts := Nat → Option Contract
def Contracts.insert (contracts : Contracts) (owner : Nat) (contract : Contract) : Contracts :=
  fun other => if other = owner then some contract else contracts other
def Contracts.erase (contracts : Contracts) : SourceDependencyAnnotations.Contracts :=
  fun owner => (contracts owner).map Contract.erase

theorem environment_erase_extend (environment : Environment) :
    (environment.extend name value).erase = environment.erase.extend name value.erase := by
  funext other
  by_cases same : other = name <;>
    simp [Environment.extend, Environment.erase, SourceDependencyAnnotations.Environment.extend, same]

theorem contracts_erase_insert (contracts : Contracts) :
    (contracts.insert owner contract).erase = contracts.erase.insert owner contract.erase := by
  funext other
  by_cases same : other = owner <;>
    simp [Contracts.insert, Contracts.erase, SourceDependencyAnnotations.Contracts.insert, same]

/- These rules authenticate annotations against actual code. The full typing
judgment below pairs them with the existing hereditary source derivation;
annotation authentication alone asserts no effect or ownership admissibility. -/
mutual
inductive Annotation (operations : Operations) :
    Contracts → List Nat → Execution.Scope → Environment → Code → Value →
      {dependencies : Dependencies} → Signature dependencies → Prop where
  | unit : Annotation operations contracts world scope environment .unit .unit .pure
  | boolean : Annotation operations contracts world scope environment (.boolean value) .boolean .pure
  | integer : Annotation operations contracts world scope environment (.integer value) .integer .pure
  | reference : Annotation operations contracts world scope environment (.resourceRef (.activation identity)) (.reference identity) .pure
  | variable (known : environment name = some value) :
      Annotation operations contracts world scope environment (.variable name) value .pure
  | lambda (body : Annotation operations contracts world .none (environment.extend parameter input) code output plan) :
      Annotation operations contracts world scope environment (.lambda parameter code)
        (.function input output requests latent plan) .pure
  | purePair (left : Annotation operations contracts world scope environment a first .pure)
      (right : Annotation operations contracts world scope environment b second .pure) :
      Annotation operations contracts world scope environment (.pair a b) (.pair first second) .pure
  | pair (left : Annotation operations contracts world scope environment a first leftPlan)
      (right : Annotation operations contracts world scope environment b second rightPlan) :
      Annotation operations contracts world scope environment (.pair a b) (.pair first second) (.sequence leftPlan rightPlan)
  | app (function : Annotation operations contracts world scope environment f
        (.function input output requests latent bodyPlan) functionPlan)
      (argument : Annotation operations contracts world scope environment a input argumentPlan) :
      Annotation operations contracts world scope environment (.app f a) output
        (.sequence functionPlan (.sequence argumentPlan bodyPlan))
  | bind (initializer : Annotation operations contracts world scope environment a input initialPlan)
      (body : Annotation operations contracts world scope (environment.extend parameter input) b output bodyPlan) :
      Annotation operations contracts world scope environment (.bind parameter a b) output (.sequence initialPlan bodyPlan)
  | branch (condition : Annotation operations contracts world scope environment test .boolean conditionPlan)
      (yes : Annotation operations contracts world scope environment a output yesPlan)
      (no : Annotation operations contracts world scope environment b output noPlan) :
      Annotation operations contracts world scope environment (.branch test a b) output
        (.sequence conditionPlan (.choice yesPlan noPlan))
  | perform (known : operations effect operation = some (input, output))
      (operand : Annotation operations contracts world scope environment value input operandPlan) :
      Annotation operations contracts world scope environment (.perform (Instantiation.freezeEffect effect) operation value)
        output (.sequence operandPlan (.request (effect := effect) (operation := operation)))
  | handler {plans : ClausePlans arms families}
      (body : Annotation operations contracts world scope environment code answer bodyPlan)
      (declarations : Declarations operations contracts world environment effect answer plans) :
      Annotation operations contracts world scope environment (.handle (Instantiation.freezeEffect effect) code arms) answer
        (.handler (effect := effect) (table := table) required (clauseSignatures plans) bodyPlan)
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (operand : Annotation operations contracts world scope environment value contract.input operandPlan) :
      Annotation operations contracts world scope environment (.resume binder value) contract.answer
        (.sequence operandPlan (.invoke (key := ⟨owner, .resume⟩)))
  | discard (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner) :
      Annotation operations contracts world scope environment (.discard binder) .unit (.invoke (key := ⟨owner, .dispose⟩))
  | cleanup (callback : Annotation operations contracts world scope environment action
        (.function .unit .unit requests latent callbackBody) callbackPlan)
      (body : Annotation operations contracts world scope environment code output bodyPlan) :
      Annotation operations contracts world scope environment (.cleanup action code) output
        (.sequence callbackPlan (.cleanup (needs := requests) callbackBody bodyPlan))
  | resource (initializer : Annotation operations contracts world scope environment initial .integer initialPlan)
      (body : ∀ identity, identity ∉ world → Annotation operations contracts (world ++ [identity]) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyPlan identity)) :
      Annotation operations contracts world scope environment (.resource binder initial code) output
        (.sequence initialPlan (.resource bodyPlan))

inductive Offer (operations : Operations) :
    Contracts → List Nat → Environment → Nat → Nat → Value → Value → Value →
      List Instance → List Instance → Code → Bool → {family : Option (Nat → Dependencies)} → ModePlans family → Prop where
  | unavailable : Offer operations contracts world environment parameter binder argument input answer
      resumeEffects closeEffects code held .unavailable
  | available (body : ∀ owner (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        Annotation operations (contracts.insert owner contract) world (.ticket binder owner)
          (environment.extend parameter argument) code answer (signature (plans owner))) :
      Offer operations contracts world environment parameter binder argument input answer
        resumeEffects closeEffects code held (.available plans)

inductive Declarations (operations : Operations) :
    Contracts → List Nat → Environment → Instance → Value → {clauses : Clauses} →
      {families : ClauseDependencies} → ClausePlans clauses families → Prop where
  | nil : Declarations operations contracts world environment effect answer .nil
  | cons (known : operations effect operation = some (argument, input))
      (ordinary : Offer operations contracts world environment parameter binder argument input answer
        resumeEffects closeEffects body false ordinaryPlan)
      (protectedMode : Offer operations contracts world environment parameter binder argument input answer
        resumeEffects closeEffects body true protectedPlan)
      (rest : Declarations operations contracts world environment effect answer restPlan) :
      Declarations operations contracts world environment effect answer
        (.cons (operation := operation) (parameter := parameter) (binder := binder) (body := body) ordinaryPlan protectedPlan restPlan)
end

/-- Both derivations describe the same code, value type and dependency tree.
The existing source judgment retains all of its effect, row and owner indices.
This pairs the derivations at their roots; synchronization of intermediate type
choices for machine-frame storage remains a separate integration obligation. -/
structure Typed (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (world : List Nat) (allowed : List Instance) (scope : Execution.Scope) (environment : Environment)
    (code : Code) (value : Value) (demand : List Nat) (requirements : Requirements demand)
    {dependencies : Dependencies} (plan : Signature dependencies) : Prop where
  source : SourceDependencyAnnotations.Expression operations.erase policy contracts.erase world allowed scope
    environment.erase code value.erase demand requirements dependencies
  annotation : Annotation operations contracts world scope environment code value plan

/-- The complete earlier hereditary proof is reused without changing its code,
requirements or ownership demand. -/
theorem Typed.erase (typed : Typed operations policy contracts world allowed scope environment code value demand requirements plan) :
    DeclaredSources.Expression operations.erase.erase policy contracts.erase.erase world allowed scope
      environment.erase.erase code value.erase.erase demand requirements :=
  SourceDependencyAnnotations.expression_erase typed.source

/-- A function's stable type retrieves its actual source body with that same
signature. Its syntax and bound parameter come from the lambda being typed. -/
theorem Annotation.lambda_body
    (typed : Annotation operations contracts world scope environment (.lambda parameter code)
      (.function input output requests latent bodySignature) plan) :
    Annotation operations contracts world .none (environment.extend parameter input) code output bodySignature := by
  cases typed with
  | lambda body => exact body

/-- Recover the actual handler clauses checked by the source annotation. The
stable signature records their actions without asserting literal code equality. -/
theorem Annotation.handler_declarations {declarationsSignature : SourcePlanSignatures.ClauseSignatures families}
    (typed : Annotation operations contracts world scope environment (.handle (Instantiation.freezeEffect effect) code arms)
      answer (.handler (effect := effect) (table := table) required declarationsSignature bodySignature)) :
    ∃ plans : ClausePlans arms families, clauseSignatures plans = declarationsSignature ∧
      Declarations operations contracts world environment effect answer plans ∧
      Annotation operations contracts world scope environment code answer bodySignature := by
  generalize frozen : Instantiation.freezeEffect effect = actualEffect at typed
  cases typed with
  | handler body declarations => exact ⟨_, rfl, declarations, body⟩

end Ash.OneShot.SourcePlannedTyping

#print axioms Ash.OneShot.SourcePlannedTyping.environment_erase_extend
#print axioms Ash.OneShot.SourcePlannedTyping.contracts_erase_insert
#print axioms Ash.OneShot.SourcePlannedTyping.Typed.erase
#print axioms Ash.OneShot.SourcePlannedTyping.Annotation.lambda_body

#print axioms Ash.OneShot.SourcePlannedTyping.Annotation.handler_declarations
