import CoreCallableFiniteHandlerDeclarations
import CoreCallableFiniteRegistryCompatibility
namespace Ash.OneShot.CoreCallableFiniteHandlerRegistryCoverage
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableStaticProducer
open CoreCallableFiniteHandlerSource
open CoreCallableFiniteCellRegistry (CellApi)
open CoreCallableContractSource (Contract)

def targetKeys (entries : OperationEntries) : Instance → List Nat
  | .user family arguments => operationKeys entries (.user family arguments)
  | .cell _ => [0,1]

/-- This is full rich record coverage, not selected-request coverage. -/
def TargetCovers (api : CellApi) (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (requested : Instance) (clauses : Clauses) : Prop :=
  ∀ operation input output,
    (CoreCallableFiniteCellRegistry.registry (some api) entries policy).operations requested operation = some (input,output) →
    operation ∈ ScopedTyping.clauseKeys clauses

def keysCheck (entries : OperationEntries) (requested : Instance) (clauses : Clauses) : Bool :=
  CoreCallableGraphAnnotationChecks.subsetB (targetKeys entries requested) (ScopedTyping.clauseKeys clauses) &&
  CoreCallableGraphAnnotationChecks.subsetB (ScopedTyping.clauseKeys clauses) (targetKeys entries requested) &&
  decide (ScopedTyping.clauseKeys clauses).Nodup

theorem old_known_key (known : operations entries requested operation = some pair) :
    operation ∈ operationKeys entries requested := by
  induction entries with
  | nil => cases known
  | cons entry rest ih =>
    obtain ⟨effect,key,input,output⟩ := entry
    simp only [operations] at known
    by_cases same : requested = effect ∧ operation = key
    · simp only [if_pos same] at known
      simp [operationKeys,same.1,same.2]
    · simp only [if_neg same] at known
      by_cases effectSame : requested = effect
      · simp only [operationKeys,if_pos effectSame,List.mem_cons]
        exact Or.inr (ih known)
      · simpa [operationKeys,effectSame] using ih known

theorem target_known_key (apiValid : api.check = true)
    (known : (CoreCallableFiniteCellRegistry.registry (some api) entries policy).operations requested operation = some pair) :
    operation ∈ targetKeys entries requested := by
  cases requested with
  | user family arguments => exact old_known_key known
  | cell identity =>
    by_cases read : operation = 0
    · simp [targetKeys,read]
    · by_cases write : operation = 1
      · simp [targetKeys,write]
      · simp [CoreCallableFiniteCellRegistry.registry,CoreCallableFiniteCellRegistry.operations,
          apiValid,CoreCallableFiniteCellRegistry.cellOperations,read,write] at known

structure CoverageReceipt (api : CellApi) (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (requested : Instance) (clauses : Clauses) : Prop where
  compatibility : CoreCallableFiniteRegistryCompatibility.compatible api entries = true
  full : TargetCovers api entries policy requested clauses
  noExtra : ScopedTyping.clauseKeys clauses ⊆ targetKeys entries requested
  unique : (ScopedTyping.clauseKeys clauses).Nodup

inductive Error where
  | incompatibleRegistry | operationCoverage
  deriving Repr

theorem coverage_sound
    (compatible : CoreCallableFiniteRegistryCompatibility.compatible api entries = true)
    (checked : keysCheck entries requested clauses = true) : CoverageReceipt api entries policy requested clauses := by
  obtain ⟨⟨covers,noExtra⟩,unique⟩ := (by simpa only [keysCheck,Bool.and_eq_true] using checked :
    (CoreCallableGraphAnnotationChecks.subsetB (targetKeys entries requested) (ScopedTyping.clauseKeys clauses) = true ∧
     CoreCallableGraphAnnotationChecks.subsetB (ScopedTyping.clauseKeys clauses) (targetKeys entries requested) = true) ∧
     decide (ScopedTyping.clauseKeys clauses).Nodup = true)
  have apiValid : api.check = true := (by
    simpa only [CoreCallableFiniteRegistryCompatibility.compatible,Bool.and_eq_true] using compatible :
    api.check = true ∧ entries.all CoreCallableFiniteRegistryCompatibility.entryCompatible = true).1
  exact ⟨compatible,(fun _ _ _ known => CoreCallableGraphAnnotationChecks.subsetB_sound covers (target_known_key apiValid known)),
    CoreCallableGraphAnnotationChecks.subsetB_sound noExtra,of_decide_eq_true unique⟩

def check (api : CellApi) (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (requested : Instance) (clauses : Clauses) : Except Error (PLift (CoverageReceipt api entries policy requested clauses)) :=
  if compatible : CoreCallableFiniteRegistryCompatibility.compatible api entries = true then
    if covered : keysCheck entries requested clauses = true then .ok ⟨coverage_sound compatible covered⟩
    else .error .operationCoverage
  else .error .incompatibleRegistry

theorem CoverageReceipt.ports (receipt : CoverageReceipt api entries policy requested clauses) :
    ScopedPorts.Covers (CoreCallableFiniteCellRegistry.registry (some api) entries policy).ports requested clauses := by
  intro operation input output known
  change ((CoreCallableFiniteCellRegistry.registry (some api) entries policy).operations requested operation).map
    (fun pair => (pair.1.port,pair.2.port)) = some (input,output) at known
  cases actual : (CoreCallableFiniteCellRegistry.registry (some api) entries policy).operations requested operation with
  | none => simp [actual] at known
  | some pair => exact receipt.full operation pair.1 pair.2 actual

#print axioms old_known_key
#print axioms target_known_key
#print axioms coverage_sound
#print axioms CoverageReceipt.ports
end Ash.OneShot.CoreCallableFiniteHandlerRegistryCoverage
