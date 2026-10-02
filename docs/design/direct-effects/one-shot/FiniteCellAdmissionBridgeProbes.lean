import CoreCallableFiniteCellInitialRoot
namespace Ash.OneShot.FiniteCellAdmissionBridgeProbes
set_option maxRecDepth 10000
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableFiniteRegistryCompatibility CoreCallableFiniteRegistryBridge
open CoreCallableFiniteCellInitialRoot

def incompatible : CoreCallableStaticProducer.OperationEntries :=
  [(.cell 0,0,.reference 0,.boolean)]
def incompatibleInitial : CoreCallableStaticProducer.Annotation incompatible globals.owners []
    (.integer 17) .integer [] (.request [] []) .pure
    SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Rows.pure := .integer 17

theorem incompatible_full_cell_rejected : compatible CoreCallableFiniteCellRegistry.original incompatible = false := by simp [compatible,incompatible,entryCompatible,readRecord]

theorem incompatible_recheck_rejected : recheck incompatibleInitial CoreCallableFiniteCellRegistry.original policy
    [] [] [] .none [] [] = .error .incompatibleRegistry := by
  simp [recheck,compatible,incompatible,entryCompatible,readRecord]

/-- A later correct record cannot repair the nearer incompatible original key. -/
theorem incompatible_nearest_record_rejected : compatible CoreCallableFiniteCellRegistry.original
    (incompatible ++ entries) = false := by simp [compatible,incompatible,entryCompatible,readRecord]

theorem incompatible_api_rejected : recheck initial
    { CoreCallableFiniteCellRegistry.original with binder := 1 } policy [] [] [] .none [] [] =
    .error .incompatibleRegistry := by
  simp [recheck,compatible,CoreCallableFiniteCellRegistry.CellApi.check]

/-- Exact full non-cell contracts are preserved, including arbitrary functions. -/
theorem noncell_full_record_preserved (input output : Contract)
    (valid : compatible CoreCallableFiniteCellRegistry.original
      [(.user 42 [],3,input,output)] = true) :
    (CoreCallableFiniteCellRegistry.registry (some CoreCallableFiniteCellRegistry.original)
      [(.user 42 [],3,input,output)] policy).operations (.user 42 []) 3 = some (input,output) :=
  selected_lookup_preserved valid (by rfl)

theorem fresh_cell_added_original_lookup_absent :
    CoreCallableStaticProducer.operations entries (.cell 7) 0 = none := rfl

theorem fresh_cell_added_exact_full_lookup :
    globals.registry.operations (.cell 7) 0 = some (.reference 7,.integer) := by
  simp [globals,CoreCallableContractAdmission.Globals.registry,CoreCallableFiniteCellRegistry.operations,
    CoreCallableFiniteCellRegistry.cellOperations,CoreCallableFiniteCellRegistry.original,CoreCallableFiniteCellRegistry.CellApi.check]

theorem shadowed_original_handle_rejected :
    (CoreCallableFiniteResourceTemplate.LocalRef.tail (bound := 9)
      (value := .reference (.bound 3))
      (CoreCallableFiniteResourceTemplate.LocalRef.head (name := 9)
        (pattern := .slot 1) (rest := []))).check = false := rfl

#print axioms shadowed_original_handle_rejected
#print axioms incompatible_full_cell_rejected
#print axioms incompatible_recheck_rejected
#print axioms incompatible_nearest_record_rejected
#print axioms incompatible_api_rejected
#print axioms noncell_full_record_preserved
#print axioms fresh_cell_added_original_lookup_absent
#print axioms fresh_cell_added_exact_full_lookup
end Ash.OneShot.FiniteCellAdmissionBridgeProbes
