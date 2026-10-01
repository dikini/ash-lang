import CoreCallbackRecipeProducer
import CoreCallableContractAdmission
import CoreCallableChecks

/-! Finite lexical and callable annotation checks at the same Core function
site. These checks retain full public contracts and compute dependency support.
Private plan origin and recursive body admission remain producer obligations;
no signature comparison identifies a literal private plan. -/
namespace Ash.OneShot.CoreCallableGraphAnnotationChecks
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax (Graph Node Binder ValueType)
open CoreCallableContractSource (Contract)
open CoreCallableReceiverRefinement (LexicalBounds CallBounds ReceiverRefines)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission

/-- Exact finite membership checks, retaining operation and activation identities. -/
def subsetB [DecidableEq α] (first second : List α) : Bool := first.all (fun item => decide (item ∈ second))
theorem subsetB_sound {first second : List α} [DecidableEq α] (valid : subsetB first second = true) : first ⊆ second := by
  intro item member
  exact of_decide_eq_true ((List.all_eq_true.mp valid) item member)

def effectsB (first second : List Instantiation.Effect) : Bool := subsetB first second && subsetB second first
theorem effectsB_sound (valid : effectsB first second = true) : EffectsSame first second := by
  obtain ⟨left, right⟩ : subsetB first second = true ∧ subsetB second first = true :=
    by simpa only [effectsB, Bool.and_eq_true] using valid
  exact fun effect => ⟨fun member => subsetB_sound left member, fun member => subsetB_sound right member⟩

/-- Core types check the declared callable allowance, not private-plan identity.
The full contract's plans and complete rows remain unchanged input data. -/
def typeB (resources : Instantiation.Environment) : ValueType → Contract → Bool
  | .unit, .unit | .boolean, .boolean | .integer, .integer => true
  | .reference name, .reference identity => decide (name.instantiate resources = .activation identity)
  | .product first second, .pair left right => typeB resources first left && typeB resources second right
  | .function first second effects, .function input output requests latent _ _ =>
      typeB resources first input && typeB resources second output &&
      effectsB (effects.map (fun effect => effect.instantiate resources)) (allowanceEffects requests) &&
      latent.all (fun request => decide (request.effect ∈ requests))
  | _, _ => false

theorem typeB_sound (valid : typeB resources ty contract = true) :
    TypeAgreement resources ty contract.value := by
  induction ty generalizing contract with
  | unit => cases contract <;> simp [typeB] at valid; exact .unit
  | boolean => cases contract <;> simp [typeB] at valid; exact .boolean
  | integer => cases contract <;> simp [typeB] at valid; exact .integer
  | reference name => cases contract <;> simp only [typeB, Bool.false_eq_true] at valid
                      exact .reference (of_decide_eq_true valid)
  | product first second ihFirst ihSecond =>
      cases contract <;> simp only [typeB, Bool.false_eq_true] at valid
      obtain ⟨left, right⟩ := (by simpa only [Bool.and_eq_true] using valid)
        |> id
      exact .product (ihFirst left) (ihSecond right)
  | function first second effects ihFirst ihSecond =>
      cases contract <;> simp only [typeB, Bool.false_eq_true] at valid
      obtain ⟨⟨⟨left, right⟩, effects⟩, latent⟩ := (by simpa only [Bool.and_eq_true] using valid)
      exact .function (ihFirst left) (ihSecond right) (effectsB_sound effects)
        (fun request member => of_decide_eq_true ((List.all_eq_true.mp latent) request member))
  | unsupported kind => cases contract <;> simp [typeB] at valid

/-- An entry names its actual Core binder site. Support is separate from the
public contract's ports; checked lookup never manufactures a missing name. -/
structure Binding where
  site : Nat
  name : Nat
  contract : Contract
  support : List Nat
abbrev Bindings := List Binding

def Bindings.lookup : Bindings → Nat → Option Binding
  | [], _ => none
  | entry :: rest, name => if name = entry.name then some entry else Bindings.lookup rest name

def Bindings.environment (bindings : Bindings) : CoreCallableContractSource.Environment :=
  fun name => (bindings.lookup name).map Binding.contract

def Bindings.lexical (bindings : Bindings) : LexicalBounds :=
  bindings.map (fun entry => (entry.name, entry.support))

theorem Bindings.lexical_lookup (bindings : Bindings) :
    bindings.lexical.lookup name = (bindings.lookup name).map Binding.support := by
  induction bindings with
  | nil => rfl
  | cons entry rest ih => simp only [Bindings.lexical, List.map_cons, LexicalBounds.lookup, Bindings.lookup]; split <;> first | rfl | exact ih

/-- This checks the binder declaration and support data, independently of any
source or authentication judgment. Actual bound-value admission remains separate. -/
def bindingB (graph : Graph) (resources : Instantiation.Environment) (world receiver : List Nat) (entry : Binding) : Bool :=
  match graph.node entry.site with
  | none => false
  | some node => node.kind.binders.any (fun binder => decide (binder.id = entry.name) && typeB resources binder.type entry.contract) &&
      subsetB entry.contract.port.resources world && subsetB entry.support receiver

theorem bindingB_sound (valid : bindingB graph resources world receiver entry = true) :
    ∃ node binder, graph.node entry.site = some node ∧ binder ∈ node.kind.binders ∧ binder.id = entry.name ∧
      TypeAgreement resources binder.type entry.contract.value ∧
      ScopedPorts.InWorld world entry.contract.port ∧ entry.support ⊆ receiver := by
  cases found : graph.node entry.site with
  | none => simp [bindingB, found] at valid
  | some node =>
      simp only [bindingB, found, Bool.and_eq_true] at valid
      obtain ⟨⟨declared, issued⟩, received⟩ := valid
      obtain ⟨binder, member, same, typed⟩ := (by simpa only [Bool.and_eq_true] using List.any_eq_true.mp declared)
      exact ⟨node, binder, rfl, member, of_decide_eq_true same, typeB_sound typed,
        subsetB_sound issued, subsetB_sound received⟩

def knownB (lexical : LexicalBounds) (dependencies : List Syntax.Dependency) : Bool :=
  dependencies.all (fun dependency => match dependency with
    | .variable name => (lexical.lookup name).isSome
    | _ => true)

theorem knownB_sound (valid : knownB lexical dependencies = true) :
    CoreCallableContractAdmission.LexicalBounds.Known lexical dependencies := by
  intro name member
  have found := (List.all_eq_true.mp valid) (.variable name) member
  cases lookup : lexical.lookup name with
  | none => simp [lookup] at found
  | some resources => exact ⟨resources, rfl⟩

/-- No proof-bearing admission fields occur in this finite annotation. Public
plan/rows are retained as full contract data; their body provenance is not inferred. -/
structure LambdaData where
  site : Nat
  bindings : Bindings
  input : Contract
  output : Contract
  requests : List Instance
  latent : Footprint
  dependencies : Dependencies
  publicPlan : Plan dependencies
  publicRows : Rows (signature publicPlan)

def LambdaData.contract (data : LambdaData) : Contract :=
  .function data.input data.output data.requests data.latent data.publicPlan data.publicRows

def LambdaData.code (resources : Instantiation.Environment) (callable : CoreCallableChecks.CheckedCallable) : Code :=
  .lambda callable.parameter (callable.rawBody.instantiate resources)

def LambdaData.support (data : LambdaData) (resources : Instantiation.Environment)
    (callable : CoreCallableChecks.CheckedCallable) : List Nat :=
  ScopedPorts.Support.evaluate data.bindings.lexical.environment (LambdaData.code resources callable).dependencies

/-- The same identified site and body reference supply both metadata checks.
The current receiver receives actual computed free-name support, including
resources absent from the public function's ports. -/
def lambdaB (graph : Graph) (resources : Instantiation.Environment) (world receiver : List Nat)
    (data : LambdaData) (callable : CoreCallableChecks.CheckedCallable) : Bool :=
  match graph.node data.site, graph.node callable.body with
  | some node, some body => match node.kind with
    | .function binder bodyIndex =>
      decide (binder.id = callable.parameter) && decide (bodyIndex = callable.body) &&
      typeB resources binder.type data.input && typeB resources node.type data.contract &&
      effectsB (node.effects.map (fun effect => effect.instantiate resources)) [] &&
      typeB resources body.type data.output &&
      subsetB (body.effects.map (fun effect => effect.instantiate resources)) (allowanceEffects data.requests) &&
      data.bindings.all (bindingB graph resources world receiver) &&
      knownB data.bindings.lexical (LambdaData.code resources callable).dependencies &&
      subsetB (data.support resources callable) receiver && subsetB receiver world &&
      subsetB data.contract.port.resources world
    | _ => false
  | _, _ => false

/-- Facts constructed by the gate. They check annotation data without claiming
that an actual saved value already has a body source or hereditary admission. -/
structure LambdaGuards (graph : Graph) (resources : Instantiation.Environment) (world receiver : List Nat)
    (data : LambdaData) (callable : CoreCallableChecks.CheckedCallable) (binder : Binder) (node body : Node) : Prop where
  site : graph.node data.site = some node
  kind : node.kind = .function binder callable.body
  parameter : binder.id = callable.parameter
  bodySite : graph.node callable.body = some body
  inputType : TypeAgreement resources binder.type data.input.value
  metadata : Metadata resources node data.contract.value []
  bodyMetadata : Metadata resources body data.output.value (body.effects.map (fun effect => effect.instantiate resources))
  bodyBound : (body.effects.map (fun effect => effect.instantiate resources)) ⊆ allowanceEffects data.requests
  bindings : ∀ entry ∈ data.bindings, ∃ node binder, graph.node entry.site = some node ∧ binder ∈ node.kind.binders ∧
    binder.id = entry.name ∧ TypeAgreement resources binder.type entry.contract.value ∧
    ScopedPorts.InWorld world entry.contract.port ∧ entry.support ⊆ receiver
  known : CoreCallableContractAdmission.LexicalBounds.Known data.bindings.lexical (LambdaData.code resources callable).dependencies
  received : data.support resources callable ⊆ receiver
  receiverIssued : receiver ⊆ world
  formed : ScopedPorts.InWorld world data.contract.port

theorem lambdaB_sound (valid : lambdaB graph resources world receiver data callable = true) :
    ∃ binder node body, LambdaGuards graph resources world receiver data callable binder node body := by
  cases site : graph.node data.site with
  | none => simp [lambdaB, site] at valid
  | some node =>
    cases bodySite : graph.node callable.body with
    | none => simp [lambdaB, site, bodySite] at valid
    | some body =>
      cases kind : node.kind <;> simp only [lambdaB, site, bodySite, kind, Bool.false_eq_true] at valid
      rename_i binder bodyIndex
      simp only [Bool.and_eq_true] at valid
      rcases valid with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨parameter, bodyRef⟩, inputType⟩, metadata⟩, effects⟩, bodyType⟩, bound⟩, bindings⟩, known⟩, received⟩, issued⟩, formed⟩
      have bodySame : bodyIndex = callable.body := of_decide_eq_true bodyRef
      cases bodySame
      refine ⟨binder, node, body, ⟨site, kind, of_decide_eq_true parameter, bodySite, typeB_sound inputType,
        ⟨typeB_sound metadata, effectsB_sound effects⟩, ⟨typeB_sound bodyType, fun _ => Iff.rfl⟩,
        subsetB_sound bound, ?_, knownB_sound known, subsetB_sound received, subsetB_sound issued, subsetB_sound formed⟩⟩
      intro entry member
      exact bindingB_sound ((List.all_eq_true.mp bindings) entry member)

inductive Error where
  | callable : CoreCallableChecks.Error → Error
  | annotation
  deriving Repr

/-- Reuse the existing finite function-site validator and then check these
metadata and dependency-support data at its exact returned raw body. -/
def checkLambda (graph : Graph) (resources : Instantiation.Environment) (world receiver : List Nat)
    (data : LambdaData) : Except Error CoreCallableChecks.CheckedCallable :=
  match CoreCallableChecks.checkFunction graph data.site with
  | .error error => .error (.callable error)
  | .ok callable => if lambdaB graph resources world receiver data callable then .ok callable else .error .annotation

theorem checkLambda_sound (success : checkLambda graph resources world receiver data = .ok callable) :
    CoreCallableChecks.checkFunction graph data.site = .ok callable ∧
    ∃ binder node body, LambdaGuards graph resources world receiver data callable binder node body := by
  cases checked : CoreCallableChecks.checkFunction graph data.site with
  | error error => simp [checkLambda, checked] at success
  | ok result =>
    simp only [checkLambda, checked] at success
    split at success
    · rename_i valid
      have same : result = callable := by simpa using success
      cases same
      exact ⟨rfl, lambdaB_sound valid⟩
    · simp at success

theorem LambdaGuards.latent_bound
    (guards : LambdaGuards graph resources world receiver data callable binder node body) :
    ∀ request ∈ data.latent, request.effect ∈ data.requests := by
  have typed := guards.metadata.type
  generalize typeSame : node.type = ty at typed
  cases data with
  | mk site bindings input output requests latent dependencies publicPlan publicRows =>
    cases typed with
    | function inputType outputType same bound => exact bound

/-- A same-site receiver-aware gate: only the computed support list supplies
current Bounds. A recursive body producer must still supply the same literal
private family, its hereditary authentication and receiver-dependent refinement. -/
theorem receiver_lambda
    (success : checkLambda graph resources world receiver data = .ok callable)
    {privateDependencies : LexicalBounds → CallBounds world → Dependencies}
    {privatePlans : ∀ lexical call, Plan (privateDependencies lexical call)}
    {privateRows : ∀ lexical call, Rows (signature (privatePlans lexical call))}
    (bodySource : ∀ lexical : LexicalBounds, ∀ call : CallBounds world,
      CoreCallableContractAdmission.IndexedSource (evidence := declarationPolicy) registry outward owners call.world data.requests .none
        (data.bindings.environment.extend callable.parameter data.input) (callable.rawBody.instantiate resources)
        data.output bodyDemand bodyReq (privatePlans lexical call) (privateRows lexical call))
    (bodyOutward : RecursiveOutward.Outward bodyReq (some data.latent))
    (publicRecipes : CoreCallbackRecipeProducer.Recipes data.publicPlan)
    (bodyAuthentication : ∀ lexical : LexicalBounds, ∀ call : CallBounds world,
      CoreCallableContractAdmission.LexicalBounds.Known lexical (LambdaData.code resources callable).dependencies →
      ScopedPorts.Support.evaluate lexical.environment (LambdaData.code resources callable).dependencies ⊆ call.receiver →
      CoreCallableContractAdmission.Authenticated (evidence := declarationPolicy) registry outward (bodySource lexical call)
        (lexical.extend callable.parameter call.argument) call.receiver)
    (bodyRefinement : ∀ lexical : LexicalBounds, ∀ call : CallBounds world,
      CoreCallableContractAdmission.LexicalBounds.Known lexical (LambdaData.code resources callable).dependencies →
      ScopedPorts.Support.evaluate lexical.environment (LambdaData.code resources callable).dependencies ⊆ call.receiver →
      ReceiverRefines data.publicRows (privateRows lexical call) call.receiver
        (ScopedPorts.Support.evaluate (lexical.extend callable.parameter call.argument).environment
          (callable.rawBody.instantiate resources).dependencies)) :
    ∃ source : CoreCallableContractAdmission.IndexedSource (evidence := declarationPolicy) registry outward owners world allowed scope
        data.bindings.environment (LambdaData.code resources callable) data.contract [] (.request [] []) .pure Rows.pure,
      CoreCallableContractAdmission.Authenticated (evidence := declarationPolicy) registry outward source data.bindings.lexical receiver ∧
      CoreValueRelation.CallableCertificate graph callable.parameter callable.body callable.rawBody := by
  letI : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
  obtain ⟨functionChecked, binder, node, body, guards⟩ := checkLambda_sound success
  let source := CoreCallableContractAdmission.IndexedSource.receiverLambda (allowed := allowed) (scope := scope)
    bodySource bodyOutward guards.latent_bound publicRecipes.certified guards.formed
  refine ⟨source, ?_, CoreCallableChecks.checkFunction_certificate functionChecked⟩
  apply CoreCallableContractAdmission.Authenticated.checked (SourceSupport.bounds_iff.mpr guards.received)
  exact CoreCallableContractAdmission.Hereditary.receiverLambda bodyOutward guards.latent_bound
    publicRecipes.certified guards.formed guards.known bodyAuthentication bodyRefinement

end Ash.OneShot.CoreCallableGraphAnnotationChecks
#print axioms Ash.OneShot.CoreCallableGraphAnnotationChecks.typeB_sound
#print axioms Ash.OneShot.CoreCallableGraphAnnotationChecks.bindingB_sound
#print axioms Ash.OneShot.CoreCallableGraphAnnotationChecks.knownB_sound

#print axioms Ash.OneShot.CoreCallableGraphAnnotationChecks.lambdaB_sound
#print axioms Ash.OneShot.CoreCallableGraphAnnotationChecks.checkLambda_sound
#print axioms Ash.OneShot.CoreCallableGraphAnnotationChecks.receiver_lambda
