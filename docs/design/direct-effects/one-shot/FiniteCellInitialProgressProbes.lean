import CoreCallableFiniteCellPortABI
import CoreCallableFiniteCellInitialRoot
namespace Ash.OneShot.FiniteCellInitialProgressProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractExecution (lowerOperations)
open CoreCallableInitialAdmission
open CoreCallableFiniteCellInitialRoot (rootCode policy entries)
open CoreCallableFiniteCellPortABI
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- This consumes the same produced closed-root Program, not a replacement
fixture or a supplied progress judgment. The actual first step is the existing
NamedAccessStep, and its joint projection is the established port invariant. -/
theorem same_root_initial_step :
    ∃ program : Program CoreCallableFiniteCellInitialRoot.globals (fun _ => none) [] rootCode,
      ∃ registry after,
        NamedAccessStep [] ⟨⟨⟨rootCode,.none,.nil⟩,[],[]⟩,[]⟩ after ∧
        ScopedPortJoint.Valid (lowerOperations CoreCallableFiniteCellInitialRoot.globals).ports
          policy registry [] after program.result.port [] := by
  obtain ⟨program,_⟩ := CoreCallableFiniteCellInitialRoot.initial_program
  have builtins := compatibility_port_abi (policy := policy)
    (owners := CoreCallableFiniteCellInitialRoot.globals.owners)
    CoreCallableFiniteCellInitialRoot.original_compatibility
  have progress := program.initial_progress builtins
  rcases progress with value | ⟨registry,after,step,joint⟩
  · cases value
  · exact ⟨program,registry,after,step,joint⟩

/-- An invalid schema cannot acquire the builtin ABI by projection. -/
theorem invalid_api_has_no_builtin_abi (invalid : api.check = false)
    (users : ScopedPorts.Signature) :
    (lowerOperations (globals api entries policy owners)).ports ≠
      ScopedPorts.withCellSignatures users := by
  intro equal
  have selected := congrFun (congrFun equal (.cell 7)) 0
  simp [globals,lowerOperations,CoherentSourceTypes.Operations.ports,
    CoreCallableFiniteCellRegistry.operations,invalid,ScopedPorts.withCellSignatures] at selected

theorem invalid_original_schema :
    ({ CoreCallableFiniteCellRegistry.original with binder := 1 } :
      CoreCallableFiniteCellRegistry.CellApi).check = false := by
  simp [CoreCallableFiniteCellRegistry.CellApi.check]

#print axioms same_root_initial_step
#print axioms invalid_api_has_no_builtin_abi
#print axioms invalid_original_schema
end Ash.OneShot.FiniteCellInitialProgressProbes
