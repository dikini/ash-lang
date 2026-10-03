import CoreCallableCompositionalResourceOpening

/-! Interfaces for the fixed existing schema backend. Every producer accepts
finite current data; result projections and rejection proofs consume its
computed output or current finite metadata. General admission stays open. -/
namespace Ash.OneShot.ResourceBackendInterfaces
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableStaticProducer
open CoreCallableStaticRegistryBackend

#check Backend
#check Backend.registry
#check Backend.valid
#check Backend.selected_lookup
#check CellError
#check Annotation
#check Annotation.perform
#check Annotation.lambda
#check Result
#check Result.mk
#check Result.source
#check Result.authenticated
#check Result.receivingIssued
#check Result.tree
#check BackendResult
#check BackendResult.mk
#check BackendResult.source
#check BackendResult.authenticated
#check BackendResult.receivingIssued
#check BackendResult.tree
#check check
#check checkGraph
#check check_cell
#check StaticTree.receiverLambda
#check StaticTree.resource
#check CoreCallableFiniteRegistryBridge.transfer_tree
#check CoreCallableFiniteRegistryBridge.produced_rechecked
#check CoreCallableFiniteRegistryBridge.recheck
#check CoreCallableFiniteRegistryBridge.recheck_cell
#check CoreCallableFiniteRegistryBridge.recheck_cell_success
#check CoreCallableCompositionalResourceBody.Checking.plan
#check CoreCallableCompositionalResourceBody.Checking.rows
#check CoreCallableCompositionalResourceBody.FunctionSlot
#check CoreCallableCompositionalResourceOpening.Opening
#check CoreCallableCompositionalResourceOpening.Result
#check CoreCallableCompositionalResourceOpening.check_compositional
#check CoreCallableCompositionalResourceOpening.check_compositional_cell
#check CoreCallableCompositionalResourceOpening.check_compositional_cell_inputs
#check CoreCallableCompositionalResourceOpening.check_compositional_cell_tree

 theorem literal_registry_exact : Backend.literal.registry entries policy = registry entries policy := rfl

 theorem cell_registry_exact : (Backend.cell api).registry entries policy =
    CoreCallableFiniteCellRegistry.registry (some api) entries policy := rfl

 theorem cell_policy_exact : ((Backend.cell api).registry entries policy).policy = policy := rfl

 theorem invalid_schema_rejected
    (annotation : Annotation entries owners bindings code contract demand requirements plan rows)
    (invalid : api.check = false) :
    check_cell annotation api policy outward world allowed scope lexical receiver =
      .error .incompatibleRegistry := by
  simp [check_cell,CoreCallableFiniteRegistryCompatibility.compatible,invalid]

 theorem incompatible_entries_rejected
    (annotation : Annotation entries owners bindings code contract demand requirements plan rows)
    (invalid : CoreCallableFiniteRegistryCompatibility.compatible api entries = false) :
    check_cell annotation api policy outward world allowed scope lexical receiver =
      .error .incompatibleRegistry := by
  simp [check_cell,invalid]

 theorem shadowed_operation_rejected :
    (OperationRef.tail (requested := effect) (key := operation) (argument := otherInput) (answer := otherOutput)
      (OperationRef.head : OperationRef [(effect,operation,input,output)] effect operation input output)).check = false := by
  simp [OperationRef.check]

 theorem wrong_full_write_output_rejected :
    CoreCallableFiniteRegistryCompatibility.entryCompatible
      (.cell identity,1,.pair (.reference identity) .integer,.boolean) = false := by
  simp [CoreCallableFiniteRegistryCompatibility.entryCompatible,
    CoreCallableFiniteRegistryCompatibility.writeRecord]

 theorem fresh_schema_read_differs_from_empty_literal (accepted : api.check = true) :
    (Backend.literal.registry [] policy).operations (.cell identity) 0 = none ∧
    ((Backend.cell api).registry [] policy).operations (.cell identity) 0 =
      some (.reference identity,.integer) := by
  exact ⟨rfl,CoreCallableFiniteCellRegistry.read_known accepted⟩

#print axioms literal_registry_exact
#print axioms cell_registry_exact
#print axioms cell_policy_exact
#print axioms invalid_schema_rejected
#print axioms incompatible_entries_rejected
#print axioms shadowed_operation_rejected
#print axioms wrong_full_write_output_rejected
#print axioms fresh_schema_read_differs_from_empty_literal
end Ash.OneShot.ResourceBackendInterfaces
