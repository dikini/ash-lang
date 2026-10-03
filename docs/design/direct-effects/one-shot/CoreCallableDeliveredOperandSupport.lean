import CoreCallableStorageRecipes
import CoreValueRelation
namespace Ash.OneShot.CoreCallableDeliveredOperandSupport
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableStaticProducer
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourcePlanSignatures (signature)
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Scalars have empty actual support by Code shape. Every other closed value
retains the whole executed storage result, including captures and nested trees. -/
def actualSupport (code : Code) (stored : CallableContracts.Contract) : List Nat :=
  match code with
  | .unit | .boolean _ | .integer _ => []
  | _ => stored.storageOf

theorem actualSupport_storage : actualSupport code stored ⊆ stored.storageOf := by
  cases code <;> simp [actualSupport]

theorem actualSupport_sound
    (derived : CallableContracts.Derives declarations storageEnvironment world .none code stored)
    (closed : ClosedValue code) : Syntax.resourceDependencies code.dependencies ⊆ actualSupport code stored := by
  have bounded := CallableContracts.value_support derived closed.1
  cases code <;> simp_all [actualSupport, Code.dependencies, Syntax.resourceDependencies]

/-- Closed actual Code has the same dependency support in every lexical map. -/
theorem actualSupport_bounds
    (derived : CallableContracts.Derives declarations storageEnvironment world .none code stored)
    (closed : ClosedValue code) (lexical : LexicalBounds) :
    SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds lexical.environment code.dependencies (actualSupport code stored) := by
  apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
  rw [ScopedPorts.Support.evaluation_congr (destination := ScopedPorts.Support.empty)
    (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))]
  rw [ScopedPorts.Support.empty_evaluation]
  exact actualSupport_sound derived closed

/-- Aggregate projection retains the complete storage tree's capture union. -/
theorem actualSupport_pair : actualSupport (.pair left right) stored = stored.storageOf := rfl

theorem actualSupport_lambda : actualSupport (.lambda formal body) stored = stored.storageOf := rfl

/-- Omitting an actual retained identity cannot authenticate the delivered
support, independently of the public rich domain or erased callable port. -/
theorem captured_identity_required
    (derived : CallableContracts.Derives declarations storageEnvironment world .none code stored)
    (closed : ClosedValue code) (retained : identity ∈ Syntax.resourceDependencies code.dependencies)
    (outside : identity ∉ bound) : ¬ actualSupport code stored ⊆ bound := by
  intro received
  exact outside (received (actualSupport_sound derived closed retained))

inductive Error where
  | rich : CoreCallableStaticProducer.Error → Error
  | storage
  | receiver
  deriving Repr

/-- Runtime correspondence is consumed at this handoff, never stored in static
instructions. Full rich and storage judgments are outputs of the executed checks. -/
structure DeliveredSupport (declarations : Instantiation.DeclarationRegistry)
    (reference : OperationRef entries requested operation argument input)
    (annotation : Annotation entries owners richBindings code argument demand requirements plan rows)
    (storageBindings : CoreCallableReturnStorageProducer.Bindings)
    (inst : Instantiation.Environment) (recipe : CoreCallableStorageRecipes.Recipe)
    (graph : CoreSyntax.Graph) (machineOwners : CoreTranslation.OwnerMap)
    (heap : CoreMachine.Heap) (value : CoreMachine.Value)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat) (allowed : List Instance)
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  known : operations entries requested operation = some (argument,input)
  related : CoreValueRelation.ValueRel graph machineOwners heap value code
  rich : Result entries policy outward owners world allowed .none richBindings code argument demand requirements plan rows lexical receiver
  richAccepted : CoreCallableStaticProducer.check annotation policy outward world allowed .none lexical receiver = .ok rich
  stored : CallableContracts.Contract
  storageAccepted : CoreCallableStorageRecipes.check storageBindings inst code recipe = some stored
  storageDerived : CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment storageBindings) world .none code stored
  storedReceived : stored.storageOf ⊆ receiver
  closed : ClosedValue code
  supportBounded : Syntax.resourceDependencies code.dependencies ⊆ actualSupport code stored
  formalReceived : actualSupport code stored ⊆ receiver

def checkOperandSupport {declarations : Instantiation.DeclarationRegistry}
    (reference : OperationRef entries requested operation argument input)
    (annotation : Annotation entries owners richBindings code argument demand requirements plan rows)
    (storageBindings : CoreCallableReturnStorageProducer.Bindings)
    (inst : Instantiation.Environment) (recipe : CoreCallableStorageRecipes.Recipe)
    (related : CoreValueRelation.ValueRel graph machineOwners heap value code)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat) (allowed : List Instance)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (DeliveredSupport declarations reference annotation storageBindings inst recipe graph machineOwners heap value
      policy outward world allowed lexical receiver) := do
  if located : reference.check = true then
    match acceptedRich : CoreCallableStaticProducer.check annotation policy outward world allowed .none lexical receiver with
    | .error error => .error (.rich error)
    | .ok rich =>
      match accepted : CoreCallableStorageRecipes.check storageBindings inst code recipe with
      | none => .error .storage
      | some stored =>
        if bounded : CoreCallableGraphAnnotationChecks.subsetB stored.storageOf receiver = true then
          let derived := CoreCallableStorageRecipes.check_sound (declarations := declarations) (world := world) (ticket := .none) accepted
          let closed := related.closed
          let received := CoreCallableGraphAnnotationChecks.subsetB_sound bounded
          .ok ⟨reference.sound located,related,rich,acceptedRich,stored,accepted,derived,received,closed,
            actualSupport_sound derived closed,(actualSupport_storage (code := code)).trans received⟩
        else .error .receiver
  else .error (.rich .operationShadowing)

#print axioms actualSupport_storage
#print axioms actualSupport_sound
#print axioms actualSupport_bounds
#print axioms actualSupport_pair
#print axioms actualSupport_lambda
#print axioms captured_identity_required
#print axioms checkOperandSupport
end Ash.OneShot.CoreCallableDeliveredOperandSupport
