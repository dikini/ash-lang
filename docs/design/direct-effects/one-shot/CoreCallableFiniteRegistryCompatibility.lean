import CoreCallableFiniteCellRegistry
namespace Ash.OneShot.CoreCallableFiniteRegistryCompatibility
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableStaticProducer (OperationEntries operations)
open CoreCallableFiniteCellRegistry (CellApi)

/-- Only exact full scalar cell contracts match. A higher-order contract is
never accepted by comparing its erased port. Non-cell contracts are copied. -/
def readRecord (identity : Nat) : Contract → Contract → Bool
  | .reference actual,.integer => decide (actual = identity)
  | _,_ => false

def writeRecord (identity : Nat) : Contract → Contract → Bool
  | .pair (.reference actual) .integer,.unit => decide (actual = identity)
  | _,_ => false

def entryCompatible : Instance × Nat × Contract × Contract → Bool
  | (.user _ _,_,_,_) => true
  | (.cell identity,operation,input,output) =>
      if operation = 0 then readRecord identity input output
      else if operation = 1 then writeRecord identity input output else false

def compatible (api : CellApi) (entries : OperationEntries) : Bool :=
  api.check && entries.all entryCompatible

 theorem readRecord_exact (valid : readRecord identity input output = true) :
    input = .reference identity ∧ output = .integer := by
  cases input <;> cases output <;> simp_all [readRecord]

 theorem writeRecord_exact (valid : writeRecord identity input output = true) :
    input = .pair (.reference identity) .integer ∧ output = .unit := by
  cases input with
  | pair left right =>
      cases left <;> cases right <;> cases output <;> simp_all [writeRecord]
  | unit | boolean | integer | reference | function => simp [writeRecord] at valid

 theorem cell_entry_exact (valid : entryCompatible (.cell identity,operation,input,output) = true) :
    CoreCallableFiniteCellRegistry.cellOperations identity operation = some (input,output) := by
  by_cases read : operation = 0
  · obtain ⟨a,b⟩ := readRecord_exact (by simpa [entryCompatible,read] using valid)
    simp [CoreCallableFiniteCellRegistry.cellOperations,read,a,b]
  · by_cases write : operation = 1
    · obtain ⟨a,b⟩ := writeRecord_exact (by simpa [entryCompatible,read,write] using valid)
      simp [CoreCallableFiniteCellRegistry.cellOperations,write,a,b]
    · simp [entryCompatible,read,write] at valid

 theorem selected_original_record (selected : operations entries effect operation = some (input,output)) :
    (effect,operation,input,output) ∈ entries := by
  induction entries with
  | nil => simp [operations] at selected
  | cons entry rest ih =>
      rcases entry with ⟨found,key,argument,answer⟩
      by_cases same : effect = found ∧ operation = key
      · simp only [operations,if_pos same,Option.some.injEq,Prod.mk.injEq] at selected
        rcases selected with ⟨a,b⟩
        simp [same.1,same.2,a,b]
      · simp only [operations,if_neg same] at selected
        exact List.mem_cons_of_mem _ (ih selected)

/-- Successful selected lookup preservation, not registry equality. The new
registry may answer fresh cell requests absent from the old finite entries. -/
 theorem selected_lookup_preserved (accepted : compatible api entries = true)
    (selected : operations entries effect operation = some (input,output)) :
    (CoreCallableFiniteCellRegistry.registry (some api) entries policy).operations effect operation = some (input,output) := by
  obtain ⟨apiValid,checked⟩ : api.check = true ∧ entries.all entryCompatible = true := by
    simpa [compatible] using accepted
  cases effect with
  | user family arguments => exact selected
  | cell identity =>
      have actual := (List.all_eq_true.mp checked) _ (selected_original_record selected)
      simp only [CoreCallableFiniteCellRegistry.registry,CoreCallableFiniteCellRegistry.operations,apiValid]
      exact cell_entry_exact actual

#print axioms readRecord_exact
#print axioms writeRecord_exact
#print axioms cell_entry_exact
#print axioms selected_original_record
#print axioms selected_lookup_preserved
end Ash.OneShot.CoreCallableFiniteRegistryCompatibility
