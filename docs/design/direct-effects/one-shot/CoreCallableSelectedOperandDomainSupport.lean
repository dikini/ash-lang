import CoreCallableDeliveredOperandSupport
namespace Ash.OneShot.CoreCallableSelectedOperandDomainSupport
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableStaticProducer CoreCallableDeliveredOperandSupport
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Only full scalar contracts carry the empty selected domain support. -/
inductive ScalarDomain : Contract → Prop where
  | unit : ScalarDomain .unit
  | boolean : ScalarDomain .boolean
  | integer : ScalarDomain .integer

def domainSupport (argument : Contract) (receiver : List Nat) : List Nat :=
  match argument with | .unit | .boolean | .integer => [] | _ => receiver

theorem domainSupport_received : domainSupport argument receiver ⊆ receiver := by
  cases argument <;> simp [domainSupport]

theorem nonscalar_domainSupport (nonScalar : ¬ ScalarDomain argument) :
    domainSupport argument receiver = receiver := by
  cases argument <;> simp_all [domainSupport,ScalarDomain.unit,ScalarDomain.boolean,ScalarDomain.integer]

/-- Shape comes from the same full source and actual closed operand. -/
theorem closed_scalar_shape {registry : CoreCallableContractRegistries.Registry} {environment : CoreCallableContractSource.Environment} (scalar : ScalarDomain argument)
    (source : IndexedSource registry outward owners world allowed scope environment deliveredCode argument
      demand requirements plan rows) (closed : ClosedValue deliveredCode) :
    deliveredCode = Code.unit ∨ (∃ value, deliveredCode = Code.boolean value) ∨
      (∃ value, deliveredCode = Code.integer value) := by
  cases deliveredCode <;> simp_all [ClosedValue,Code.IsValue]
  all_goals cases source <;> cases scalar

theorem delivered_support_in_domain
    {reference : OperationRef entries requested operation argument input}
    {annotation : Annotation entries owners richBindings deliveredCode argument demand requirements plan rows}
    (delivered : DeliveredSupport storageDeclarations reference annotation storageBindings inst recipe
      graph machineOwners heap value policy outward world allowed lexical receiver) :
    actualSupport deliveredCode delivered.stored ⊆ domainSupport argument receiver := by
  by_cases scalar : ScalarDomain argument
  · obtain shape | shape | shape := closed_scalar_shape scalar delivered.rich.source delivered.closed
    · simp [shape,actualSupport]
    · obtain ⟨value,same⟩ := shape; simp [same,actualSupport]
    · obtain ⟨value,same⟩ := shape; simp [same,actualSupport]
  · rw [nonscalar_domainSupport scalar]
    exact actualSupport_storage.trans delivered.storedReceived

#print axioms domainSupport_received
#print axioms nonscalar_domainSupport
#print axioms closed_scalar_shape
#print axioms delivered_support_in_domain
end Ash.OneShot.CoreCallableSelectedOperandDomainSupport
