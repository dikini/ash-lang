import SourceScheduledCapture

/-! Packaging the current one-shot state for combined preservation.
The snapshot carries evolving metadata and the concrete run. Its validity is a
separate proposition, exactly the existing complete installation invariant. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)

/-- Metadata that can change at allocation, capture or continuation use.
This record contains no admission or successor-validity evidence. -/
structure Snapshot (operations : Operations) where
  contracts : Contracts
  tables : CallableProtectionFrames.Tables
  families : SourceDependencyFrames.Families
  required : SourceContextualRechecking.Required
  annotations : Nat → Option SourceDependencyCapture.Scope
  world : List Nat
  history : List Nat
  resumes : RecursiveRequirements.Store
  disposals : RecursiveRequirements.Store
  annotatedStore : RecursiveRequirements.Store
  owners : ContractRows contracts
  run : LexicalUnwind.UseRunState

/-- Preservation keeps the language signature, terminal value type, outward
interpretations, resource allowance and effect budget fixed. All changing data
comes from the snapshot; no copy of the invariant is introduced. -/
def Valid (policy : Syntax.TicketPolicy) (outward : List Instance)
    (ambient : List Nat) (budget : Footprint) (ports : OperationRows operations)
    (emptyRows : EnvironmentRows (fun _ => none)) (output : Value) (outputRows : ValueRows output)
    (snapshot : Snapshot operations) : Prop :=
  InstallationState operations policy snapshot.contracts snapshot.tables snapshot.families snapshot.required outward
    snapshot.annotations snapshot.world ambient snapshot.history snapshot.resumes snapshot.disposals snapshot.annotatedStore
    budget ports snapshot.owners emptyRows (.value output) (.value outputRows) snapshot.run

variable {operations : Operations} {policy : Syntax.TicketPolicy} {contracts : Contracts}
  {tables : CallableProtectionFrames.Tables} {families : SourceDependencyFrames.Families}
  {required : SourceContextualRechecking.Required} {outward : List Instance}
  {annotations : Nat → Option SourceDependencyCapture.Scope} {world ambient history : List Nat}
  {resumes disposals annotatedStore : RecursiveRequirements.Store} {budget : Footprint}
  {ports : OperationRows operations} {owners : ContractRows contracts}
  {emptyRows : EnvironmentRows (fun _ => none)} {output : Value} {outputRows : ValueRows output}
  {run : LexicalUnwind.UseRunState} {snapshot : Snapshot operations}

/-- Package the metadata already indexing an existing complete-state endpoint.
The proof argument selects the endpoint; no proposition is eliminated into data. -/
def Snapshot.ofState
    (_state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows (.value output) (.value outputRows) run) :
    Snapshot operations :=
  ⟨contracts, tables, families, required, annotations, world, history, resumes, disposals, annotatedStore, owners, run⟩

@[simp] theorem Snapshot.ofState_run
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows (.value output) (.value outputRows) run) :
    (Snapshot.ofState state).run = run := rfl

/-- The package retains the exact existing invariant. -/
theorem valid_ofState
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows (.value output) (.value outputRows) run) :
    Valid policy outward ambient budget ports emptyRows output outputRows (Snapshot.ofState state) := state

/-- Unpacking requires no translation of source witnesses or metadata. -/
theorem Valid.unpack
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot) :
    InstallationState operations policy snapshot.contracts snapshot.tables snapshot.families snapshot.required outward
      snapshot.annotations snapshot.world ambient snapshot.history snapshot.resumes snapshot.disposals snapshot.annotatedStore
      budget ports snapshot.owners emptyRows (.value output) (.value outputRows) snapshot.run := valid

/-- Existential packaging preserves the concrete run of a complete-state result. -/
theorem pack
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows (.value output) (.value outputRows) run) :
    ∃ snapshot : Snapshot operations, snapshot.run = run ∧
      Valid policy outward ambient budget ports emptyRows output outputRows snapshot :=
  ⟨Snapshot.ofState state, rfl, valid_ofState state⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Snapshot.ofState
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Snapshot.ofState_run
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.valid_ofState
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Valid.unpack
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.pack
