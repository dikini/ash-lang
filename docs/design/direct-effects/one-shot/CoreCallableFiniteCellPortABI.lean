import CoreCallableFiniteRegistryBridge
import CoreCallableInitialAdmission
namespace Ash.OneShot.CoreCallableFiniteCellPortABI
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractAdmission
open CoreCallableFiniteCellRegistry
open CoreCallableContractExecution (lowerOperations)

def globals (api : CellApi) (entries : CoreCallableStaticProducer.OperationEntries)
    (policy : Syntax.TicketPolicy) (owners : CoreCallableContractRegistries.Owners) : Globals :=
  ⟨operations (some api) entries,policy,owners⟩
def originalGlobals (entries : CoreCallableStaticProducer.OperationEntries)
    (policy : Syntax.TicketPolicy) (owners : CoreCallableContractRegistries.Owners) : Globals :=
  ⟨CoreCallableStaticProducer.operations entries,policy,owners⟩

/-- The equality is only a port ABI projection. Full original contracts remain
in the globals, and non-cell entries retain their original ordered lookup. -/
theorem checked_port_abi (checked : api.check = true) :
    (lowerOperations (globals api entries policy owners)).ports =
      ScopedPorts.withCellSignatures (lowerOperations (originalGlobals entries policy owners)).ports := by
  funext effect operation
  cases effect with
  | user family arguments => rfl
  | cell identity =>
    by_cases read : operation = 0
    · subst operation
      simp [globals,lowerOperations,CoherentSourceTypes.Operations.ports,operations,checked,
        cellOperations,ScopedPorts.withCellSignatures,
        CoreCallableContractSource.Contract.value,SourcePlannedTyping.Value.erase,
        SourceDependencyAnnotations.Value.erase,CoherentSourceTypes.Value.port]
    · by_cases write : operation = 1
      · subst operation
        simp [globals,lowerOperations,CoherentSourceTypes.Operations.ports,operations,checked,
          cellOperations,ScopedPorts.withCellSignatures,
          CoreCallableContractSource.Contract.value,SourcePlannedTyping.Value.erase,
          SourceDependencyAnnotations.Value.erase,CoherentSourceTypes.Value.port]
      · cases operation with
        | zero => exact False.elim (read rfl)
        | succ op => cases op with
          | zero => exact False.elim (write rfl)
          | succ op => simp [globals,lowerOperations,CoherentSourceTypes.Operations.ports,
              operations,checked,cellOperations,ScopedPorts.withCellSignatures]

theorem compatibility_port_abi
    (accepted : CoreCallableFiniteRegistryCompatibility.compatible api entries = true) :
    (lowerOperations (globals api entries policy owners)).ports =
      ScopedPorts.withCellSignatures (lowerOperations (originalGlobals entries policy owners)).ports :=
  checked_port_abi (Bool.and_eq_true_iff.mp accepted).1

#print axioms checked_port_abi
#print axioms compatibility_port_abi
end Ash.OneShot.CoreCallableFiniteCellPortABI
