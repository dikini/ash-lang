import CoreCallableStaticFiniteData
import CoreExportedOperationMetadata

/-! Finite original declaration schemas. This adapter does not add a fallback
signature: cell operations exist only after exact schema validation. Non-cell
entries retain their original full contracts and existing lookup order. -/
namespace Ash.OneShot.CoreCallableFiniteCellRegistry
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreOperationSignatures

structure CellApi where
  binder : Nat
  read : RawEntry
  write : RawEntry
  sourceManifest : List String
  deriving DecidableEq, Repr

def readDeclaration (binder : Nat) : RawEntry :=
  ⟨.cell (.bound binder),0,.reference (.bound binder),.integer⟩
def writeDeclaration (binder : Nat) : RawEntry :=
  ⟨.cell (.bound binder),1,.product (.reference (.bound binder)) .integer,.unit⟩

def CellApi.check (api : CellApi) : Bool :=
  decide (api.binder = 0 ∧ api.read = readDeclaration api.binder ∧ api.write = writeDeclaration api.binder ∧ api.sourceManifest = CoreExportedOperationMetadata.sourceManifest)

def original : CellApi := ⟨0,readDeclaration 0,writeDeclaration 0,CoreExportedOperationMetadata.sourceManifest⟩

theorem original_read : original.read ∈ CoreExportedOperationMetadata.entries := by decide
theorem original_write : original.write ∈ CoreExportedOperationMetadata.entries := by decide

def cellOperations (identity operation : Nat) : Option (Contract × Contract) :=
  if operation = 0 then some (.reference identity,.integer)
  else if operation = 1 then some (.pair (.reference identity) .integer,.unit) else none

/-- The finite original schema is interpreted at the requested exact instance.
An absent or invalid schema contributes no cell declaration. -/
def operations (api : Option CellApi) (entries : CoreCallableStaticProducer.OperationEntries) :
    Instance → Nat → Option (Contract × Contract)
  | .cell identity, operation => match api with
      | none => none
      | some declaration => if declaration.check then cellOperations identity operation else none
  | .user family arguments, operation => CoreCallableStaticProducer.operations entries (.user family arguments) operation

def registry (api : Option CellApi) (entries : CoreCallableStaticProducer.OperationEntries)
    (policy : Syntax.TicketPolicy) : CoreCallableContractRegistries.Registry := ⟨operations api entries,policy⟩

theorem checked_declarations {api : CellApi} (accepted : api.check = true) :
    api.read = readDeclaration api.binder ∧ api.write = writeDeclaration api.binder := ⟨(of_decide_eq_true accepted).2.1,(of_decide_eq_true accepted).2.2.1⟩

theorem checked_original {api : CellApi} (accepted : api.check = true) : api = original := by
  obtain ⟨binder,read,write,manifest⟩ := of_decide_eq_true accepted
  cases api
  simp_all [original]

theorem checked_source_identity {api : CellApi} (accepted : api.check = true) :
    api.read ∈ CoreExportedOperationMetadata.entries ∧ api.write ∈ CoreExportedOperationMetadata.entries ∧
    api.sourceManifest = CoreExportedFixture.identityManifest := by
  rw [checked_original accepted]
  exact ⟨original_read,original_write,rfl⟩

theorem read_known {api : CellApi} (accepted : api.check = true) :
    (registry (some api) entries policy).operations (.cell identity) 0 = some (.reference identity,.integer) := by
  simp [registry,operations,accepted,cellOperations]
theorem write_known {api : CellApi} (accepted : api.check = true) :
    (registry (some api) entries policy).operations (.cell identity) 1 =
      some (.pair (.reference identity) .integer,.unit) := by
  simp [registry,operations,accepted,cellOperations]
theorem noncell_lookup_preserved :
    (registry api entries policy).operations (.user family arguments) operation =
      CoreCallableStaticProducer.operations entries (.user family arguments) operation := rfl

/-- Full rich scalar contracts agree with realization of the SAME raw
read/write declarations, not only with a separately guessed public port. -/
theorem read_realization {api : CellApi} (accepted : api.check = true) (environment : Instantiation.Environment) (identity : Nat) :
    resolveEntry (environment.bind api.binder identity) api.read =
      .ok ⟨.cell identity,0,(Contract.reference identity).port,Contract.integer.port⟩ := by
  rw [(checked_declarations accepted).1]
  simp [resolveEntry,readDeclaration,realizeEffect,realizeName,Instantiation.Environment.bind,
    declarationPort,CoreOperationSignatures.emptySupport,CoreTypeSupport.decorate,
    realizeType,Contract.port,Contract.value,ScopedPorts.eraseType, Except.mapError, Except.bind, Except.pure,
    SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase,
    CoherentSourceTypes.Value.port, Bind.bind, Pure.pure]

theorem write_realization {api : CellApi} (accepted : api.check = true) (environment : Instantiation.Environment) (identity : Nat) :
    resolveEntry (environment.bind api.binder identity) api.write =
      .ok ⟨.cell identity,1,(Contract.pair (.reference identity) .integer).port,Contract.unit.port⟩ := by
  rw [(checked_declarations accepted).2]
  simp [resolveEntry,writeDeclaration,realizeEffect,realizeName,Instantiation.Environment.bind,
    declarationPort,CoreOperationSignatures.emptySupport,CoreTypeSupport.decorate,
    realizeType,Contract.port,Contract.value,ScopedPorts.eraseType, Except.mapError, Except.bind, Except.pure,
    SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase,
    CoherentSourceTypes.Value.port, Bind.bind, Pure.pure]

#print axioms original_read
#print axioms original_write
#print axioms checked_declarations
#print axioms checked_original
#print axioms checked_source_identity
#print axioms read_known
#print axioms write_known
#print axioms noncell_lookup_preserved
#print axioms read_realization
#print axioms write_realization
end Ash.OneShot.CoreCallableFiniteCellRegistry
