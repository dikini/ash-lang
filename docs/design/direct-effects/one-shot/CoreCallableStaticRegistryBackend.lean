import CoreCallableFiniteRegistryCompatibility

/-! Fixed interpretations of the existing literal table and checked original
cell schema. The selector is finite data; validity and complete selected
operation contracts are computed by the existing finite checks. -/
namespace Ash.OneShot.CoreCallableStaticRegistryBackend
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableStaticProducer (OperationEntries Error)
open CoreCallableFiniteCellRegistry (CellApi)
open CoreCallableContractSource (Contract)

inductive Backend where
  | literal
  | cell (api : CellApi)

def Backend.registry (backend : Backend) (entries : OperationEntries)
    (policy : Syntax.TicketPolicy) : CoreCallableContractRegistries.Registry :=
  ⟨(match backend with
    | .literal => CoreCallableStaticProducer.operations entries
    | .cell api => CoreCallableFiniteCellRegistry.operations (some api) entries), policy⟩

def Backend.valid (backend : Backend) (entries : OperationEntries) : Bool :=
  match backend with
  | .literal => true
  | .cell api => CoreCallableFiniteRegistryCompatibility.compatible api entries

theorem Backend.selected_lookup (backend : Backend)
    (valid : backend.valid entries = true)
    (selected : CoreCallableStaticProducer.operations entries effect operation = some (input,output)) :
    (backend.registry entries policy).operations effect operation = some (input,output) := by
  cases backend with
  | literal => exact selected
  | cell api => exact CoreCallableFiniteRegistryCompatibility.selected_lookup_preserved valid selected

inductive CellError where
  | incompatibleRegistry
  | originalCheck : Error → CellError

#print axioms Backend.selected_lookup
end Ash.OneShot.CoreCallableStaticRegistryBackend
