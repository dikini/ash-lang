import CoreCallableContractSource

/-! Immutable declaration registry and common continuation endpoints for the
experimental callable source. Public contracts retain their plans; each actual
callable's private body remains separate recursive source evidence. -/
namespace Ash.OneShot.CoreCallableContractRegistries
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)

structure Registry where
  operations : Instance → Nat → Option (Contract × Contract)
  policy : Syntax.TicketPolicy

def Registry.ports (registry : Registry) : ScopedPorts.Signature :=
  fun effect operation => (registry.operations effect operation).map (fun pair => (pair.1.port, pair.2.port))

/-- Both continuation endpoints use common contracts. Historical demand,
rights and outward rows are unchanged scalar interfaces. -/
structure OwnerContract where
  input : Contract
  answer : Contract
  held : Bool
  resumeDemand : List Nat
  resumeRow : Footprint
  closeDemand : List Nat
  closeRow : Option Footprint
  resumeEffects : List Instance
  closeEffects : List Instance

abbrev Owners := Nat → Option OwnerContract

def OwnerContract.legacy (contract : OwnerContract) : SourcePlannedTyping.Contract :=
  ⟨contract.input.value, contract.answer.value, contract.held, contract.resumeDemand,
    contract.resumeRow, contract.closeDemand, contract.closeRow, contract.resumeEffects, contract.closeEffects⟩

def Owners.legacy (owners : Owners) : SourcePlannedTyping.Contracts :=
  fun owner => (owners owner).map OwnerContract.legacy

def OwnerContract.lower (contract : OwnerContract) := contract.legacy.erase.erase
def Owners.lower (owners : Owners) := owners.legacy.erase.erase

theorem Owners.known_lower {owners : Owners} {owner : Nat} {contract : OwnerContract}
    (known : owners owner = some contract) : owners.lower owner = some contract.lower := by
  simp [lower, OwnerContract.lower, legacy, SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, known]

def Owners.insert (owners : Owners) (owner : Nat) (contract : OwnerContract) : Owners :=
  fun other => if other = owner then some contract else owners other

@[simp] theorem Owners.insert_here {owners : Owners} {owner : Nat} {contract : OwnerContract} : (owners.insert owner contract) owner = some contract := by
  simp [insert]
@[simp] theorem Owners.insert_other {owners : Owners} {owner other : Nat} {contract : OwnerContract} (different : other ≠ owner) :
    (owners.insert owner contract) other = owners other := by simp [insert, different]
@[simp] theorem Owners.legacy_insert {owners : Owners} {owner : Nat} {contract : OwnerContract} : (owners.insert owner contract).legacy =
    owners.legacy.insert owner contract.legacy := by
  funext other
  by_cases same : other = owner <;> simp [legacy, insert, SourcePlannedTyping.Contracts.insert, same]

theorem Owners.known_legacy {owners : Owners} {owner : Nat} {contract : OwnerContract} (known : owners owner = some contract) :
    owners.legacy owner = some contract.legacy := by simp [legacy, known]

#print axioms Owners.insert_here
#print axioms Owners.insert_other
#print axioms Owners.known_lower
#print axioms Owners.legacy_insert
#print axioms Owners.known_legacy
end Ash.OneShot.CoreCallableContractRegistries
