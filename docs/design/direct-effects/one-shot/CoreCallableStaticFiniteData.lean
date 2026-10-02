import CoreCallableGraphAnnotationChecks

/-! Finite constructor annotations retain their exact full contracts and literal
plans. Their fields are syntax and structural tags, never Source/Auth proofs.
The checker constructs those judgments as outputs. Unsupported source forms
remain explicit full-fragment obligations. -/
namespace Ash.OneShot.CoreCallableStaticProducer
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractAdmission
open CoreCallableContractRegistries (Owners OwnerContract)

abbrev Bindings := List (Nat × Contract)

def environment : Bindings → Environment
  | [] => Environment.empty
  | (name, contract) :: rest => (environment rest).extend name contract

/-- A finite path into the literal full-contract environment. A tail path is
checked for shadowing; it cannot select an older binding of the same name. -/
inductive BindingRef : Bindings → Nat → Contract → Type where
  | head : BindingRef ((name, contract) :: rest) name contract
  | tail (next : BindingRef rest name contract) : BindingRef ((bound, value) :: rest) name contract

def BindingRef.check : BindingRef bindings name contract → Bool
  | .head => true
  | @BindingRef.tail _ name _ bound _ next => decide (name ≠ bound) && next.check

theorem BindingRef.sound (reference : BindingRef bindings name contract)
    (valid : reference.check = true) : environment bindings name = some contract := by
  induction reference with
  | head => simp [environment, Environment.extend]
  | @tail rest name contract bound value next ih =>
      obtain ⟨miss, checked⟩ : decide (name ≠ bound) = true ∧ next.check = true :=
        by simpa only [BindingRef.check, Bool.and_eq_true] using valid
      simp only [environment, Environment.extend, if_neg (of_decide_eq_true miss)]
      exact ih checked

/-- Public declaration certification is constructed from retained structural
recipe data. Handler and resource templates need their universal validators. -/
inductive RecipeTag : {dependencies : Dependencies} → Plan dependencies → Type where
  | pure : RecipeTag .pure
  | request : RecipeTag .request
  | invoke : RecipeTag .invoke
  | sequence (left : RecipeTag first) (right : RecipeTag second) : RecipeTag (.sequence first second)
  | choice (left : RecipeTag first) (right : RecipeTag second) : RecipeTag (.choice first second)
  | cleanup (callback : RecipeTag first) (body : RecipeTag second) : RecipeTag (.cleanup first second)
  | unsupported (plan : Plan dependencies) : RecipeTag plan

def RecipeTag.check : RecipeTag plan → Bool
  | .pure | .request | .invoke => true
  | .sequence left right | .choice left right | .cleanup left right => left.check && right.check
  | .unsupported _ => false

theorem RecipeTag.sound (tag : RecipeTag plan) (valid : tag.check = true) :
    CoreCallbackRecipeProducer.Recipes plan := by
  induction tag with
  | pure => exact .pure
  | request => exact .request
  | invoke => exact .invoke
  | sequence left right ihL ihR =>
      obtain ⟨a,b⟩ : left.check = true ∧ right.check = true := by simpa only [RecipeTag.check, Bool.and_eq_true] using valid
      exact .sequence (ihL a) (ihR b)
  | choice left right ihL ihR =>
      obtain ⟨a,b⟩ : left.check = true ∧ right.check = true := by simpa only [RecipeTag.check, Bool.and_eq_true] using valid
      exact .choice (ihL a) (ihR b)
  | cleanup callback body ihC ihB =>
      obtain ⟨a,b⟩ : callback.check = true ∧ body.check = true := by simpa only [RecipeTag.check, Bool.and_eq_true] using valid
      exact .cleanup (ihC a) (ihB b)
  | unsupported => cases valid

inductive PureTag : {dependencies : Dependencies} → Plan dependencies → Type where
  | pure : PureTag .pure
  | sequence (first : PureTag left) (second : PureTag right) : PureTag (.sequence left right)

theorem PureTag.sound (tag : PureTag plan) : CorePayloadRefinement.PurePlan plan := by
  induction tag with
  | pure => exact .pure
  | sequence first second ihF ihS => exact .sequence ihF ihS

/-- Finite structural instructions for the existing exact row transports.
The indices fix complete rows; tags cannot select another private family. -/
inductive RefinementTag : {firstDeps actualDeps : Dependencies} →
    {first : SourcePlanSignatures.Signature firstDeps} → {actual : SourcePlanSignatures.Signature actualDeps} →
    Rows first → Rows actual → Type where
  | identity (rows : Rows checking) : RefinementTag rows rows
  | pure (tag : PureTag plan) (rows : Rows (signature plan)) : RefinementTag Rows.pure rows
  | prependPure (tag : PureTag plan) (prefixRows : Rows (signature plan)) (suffix : Rows checking) :
      RefinementTag suffix (.sequence prefixRows suffix)
  | choice (left : RefinementTag before first) (right : RefinementTag before second) :
      RefinementTag before (.choice first second)
  | compose (first : RefinementTag before middle) (second : RefinementTag middle after) :
      RefinementTag before after

theorem RefinementTag.sound (tag : RefinementTag before after) :
    CoreCallableRootRefinement.Refines before after := by
  induction tag with
  | identity rows => exact .identity rows
  | pure tag rows => exact .of_exact (.pure_plan tag.sound rows)
  | prependPure tag prefixRows suffix => exact .of_exact (.pure_prefix tag.sound prefixRows suffix)
  | choice left right ihL ihR => exact .choice ihL ihR
  | compose first second ihF ihS => exact .compose ihF ihS

abbrev OperationEntries := List (Instance × Nat × Contract × Contract)

def operations : OperationEntries → Instance → Nat → Option (Contract × Contract)
  | [], _, _ => none
  | (effect, operation, input, output) :: rest, requested, key =>
      if requested = effect ∧ key = operation then some (input, output) else operations rest requested key

inductive OperationRef : OperationEntries → Instance → Nat → Contract → Contract → Type where
  | head : OperationRef ((effect, operation, input, output) :: rest) effect operation input output
  | tail (next : OperationRef rest effect operation input output) :
      OperationRef ((requested, key, argument, answer) :: rest) effect operation input output

def OperationRef.check : OperationRef entries effect operation input output → Bool
  | .head => true
  | @OperationRef.tail _ effect operation _ _ requested key _ _ next =>
      decide (effect ≠ requested ∨ operation ≠ key) && next.check

theorem OperationRef.sound (reference : OperationRef entries effect operation input output)
    (valid : reference.check = true) : operations entries effect operation = some (input, output) := by
  induction reference with
  | head => simp [operations]
  | @tail rest effect operation input output requested key argument answer next ih =>
      obtain ⟨miss, checked⟩ : decide (effect ≠ requested ∨ operation ≠ key) = true ∧ next.check = true :=
        by simpa only [OperationRef.check, Bool.and_eq_true] using valid
      have different : ¬ (effect = requested ∧ operation = key) := by
        intro same
        rcases of_decide_eq_true miss with a | b
        · exact a same.1
        · exact b same.2
      simp only [operations, if_neg different]
      exact ih checked

/-- Finite permutation instructions retain the exact scalar demand lists. -/
inductive DemandPermutation : List Nat → List Nat → Type where
  | refl (owners : List Nat) : DemandPermutation owners owners
  | swap (first second : Nat) (rest : List Nat) : DemandPermutation (first :: second :: rest) (second :: first :: rest)
  | cons (owner : Nat) (next : DemandPermutation before after) : DemandPermutation (owner :: before) (owner :: after)
  | trans (first : DemandPermutation before middle) (second : DemandPermutation middle after) : DemandPermutation before after

theorem DemandPermutation.sound (instructions : DemandPermutation before after) : before.Perm after := by
  induction instructions with
  | refl owners => exact .refl owners
  | swap first second rest => exact .swap _ _ _
  | cons owner next ih => exact .cons _ ih
  | trans first second ihF ihS => exact .trans ihF ihS

/-- Finite lookup instructions retain the exact full contract on a literal
owner insertion spine. Checking rejects shadowed older entries. -/
inductive OwnerRef : Owners → Nat → OwnerContract → Type where
  | head : OwnerRef (Owners.insert base owner contract) owner contract
  | tail (next : OwnerRef base owner contract) : OwnerRef (Owners.insert base bound stored) owner contract

def OwnerRef.check : OwnerRef owners owner contract → Bool
  | .head => true
  | .tail (bound := bound) next => decide (owner ≠ bound) && next.check

theorem OwnerRef.sound (reference : OwnerRef owners owner contract)
    (valid : reference.check = true) : owners owner = some contract := by
  induction reference with
  | head => exact Owners.insert_here
  | tail next ih =>
      rename_i base actualOwner actualContract bound stored
      obtain ⟨different, checked⟩ : actualOwner ≠ bound ∧ next.check = true := by
        simpa only [OwnerRef.check, Bool.and_eq_true, decide_eq_true_eq] using valid
      rw [Owners.insert_other different]
      exact ih checked


def registry (entries : OperationEntries) (policy : Syntax.TicketPolicy) : CoreCallableContractRegistries.Registry :=
  ⟨operations entries, policy⟩

inductive Error where
  | unsupported : String → Error
  | lexicalShadowing
  | missingLexicalSupport
  | operationShadowing
  | unissuedPort
  | unavailableEffect
  | unsupportedRecipe
  | latentSummary
  | latentAllowance
  | support
  | ownerShadowing
  | ownerScope
  | capability
  | protectedOwner
  | graphShape : CoreSyntax.Error → Error
  | graphNode
  | graphMetadata
  | graphTranslation : CoreSyntax.Error → Error
  | graphCode
  deriving Repr

/-- Extraction preserves the first full binding, even when an older name is shadowed. -/
theorem environment_first_binding : environment ((name,contract) :: rest) name = some contract := by
  simp [environment,Environment.extend]

theorem registry_exact_operations : (registry entries policy).operations = operations entries := rfl

theorem registry_exact_policy : (registry entries policy).policy = policy := rfl

#print axioms environment_first_binding
#print axioms registry_exact_operations
#print axioms registry_exact_policy
end Ash.OneShot.CoreCallableStaticProducer
