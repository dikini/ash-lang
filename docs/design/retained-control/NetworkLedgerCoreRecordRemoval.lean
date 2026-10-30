import NetworkLedgerCoreRecordLookup

/- Actual normalized Core Record removal, conditional on the checked linked
   shape, exact captures and nonreentrant selected host allocation. -/
namespace Ash.NetworkLedger.CoreRecordRemoval

open Ash.NetworkLedger
open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreValues
open Ash.NetworkLedger.CoreRecordLookup
open Ash.NetworkLedger.CoreRecordProjection

/-- Every normal return removes the first matching whole Record. -/
theorem record_removal_body_correct (c : Constructors) (program : Program)
    (checked : CheckedRemovalBase c program)
    (projection : RecordProjectionShape program checked.projection)
    (functionName : projection.functionName = checked.projectionName)
    (entryName : projection.recordName = checked.miss.entryName)
    (code : projection.code = checked.projectionCode)
    (captureValues : List Value) (captureEnv : Environment)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved : Nat)
    (wanted : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.miss.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv) :
    ∀ start finish payload payloadResolved list result,
      Resolve start payload payloadResolved → readCell start payloadResolved = some [wanted, list] →
      BoundedLocations start → Ident c start wanted queryId → Children c start list entries →
      RemovalRepresentedEntries c (RecordEntry projection.record) start key entries →
      Resolve start selfAddress selfResolved →
      readCell start selfResolved = some (.closureCode checked.code :: captureValues) →
      Resolve start comparisonAddress comparisonResolved →
      readCell start comparisonResolved = some [.closureCode checked.comparator.code] →
      Resolve start projectionAddress projectionResolved →
      readCell start projectionResolved = some [.closureCode checked.projectionCode] →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body start result finish →
      RemovalOutcome c start finish result (Ash.NetworkLedger.remove key queryId entries).1
        (Ash.NetworkLedger.remove key queryId entries).2 := by
  apply removal_body_correct_with c program checked (RecordEntry projection.record)
    (record_entry_retained projection.record) captureValues captureEnv selfAddress selfResolved
    comparisonAddress comparisonResolved projectionAddress projectionResolved wanted queryId key entries
    selfBinding comparisonBinding projectionBinding captureBindings
  intro env start entryAddress keyAddress entryRep functionBinding entryBinding functionResolution functionCell
  obtain ⟨address, resolved, payload, tuple, parent, phase, children, same, resolution, cell,
    payloadResolution, fields⟩ := entryRep
  have addressEq : address = entryAddress := by simpa using same.symm
  subst address
  have functionBound : CoreEval.lookup env projection.functionName = some (.location projectionAddress) := by
    simpa [functionName] using functionBinding
  have entryBound : CoreEval.lookup env projection.recordName = some (.location entryAddress) := by
    simpa [entryName] using entryBinding
  have closureCell : readCell start projectionResolved = some [.closureCode projection.code] := by
    simpa [code] using functionCell
  have functionFresh : projection.functionName ≠ checked.comparisonPair.contextBinder := by
    simpa [functionName] using checked.projectionFresh
  have entryFresh : projection.recordName ≠ checked.comparisonPair.contextBinder := by
    simpa [entryName] using checked.entryFresh
  exact record_projection_after_query program env start checked.projection projection.function projection.argument
    projection.code projection.context projection.storage projection.parameter projection.body projection.scrutinee
    projection.returnKey projection.functionName projection.recordName projection.keyName projection.parentName
    projection.phaseName projection.childrenName checked.comparisonPair.contextBinder projection.record
    projectionAddress projectionResolved entryAddress resolved payload tuple keyAddress parent phase children
    functionFresh entryFresh projection.callShape projection.functionShape projection.argumentShape
    functionBound entryBound functionResolution closureCell projection.closureShape projection.differentParent
    projection.differentPhase projection.differentChildren projection.bodyShape projection.scrutineeShape
    projection.returnShape resolution cell payloadResolution fields


/-- The finite result clauses need no unique-key assumption. -/
theorem record_removal_outcome_clauses (c : Constructors) (start finish : Store)
    (result : Value) (key : Value → Id) (queryId : Id) (entries : List Value)
    (outcome : RemovalOutcome c start finish result (Ash.NetworkLedger.remove key queryId entries).1
      (Ash.NetworkLedger.remove key queryId entries).2) :
    RemovalOutcome c start finish result (Ash.NetworkLedger.erase key queryId entries)
        (Ash.NetworkLedger.remove key queryId entries).2 ∧
      ((Ash.NetworkLedger.remove key queryId entries).2 = .found ↔ queryId ∈ entries.map key) ∧
      ((Ash.NetworkLedger.remove key queryId entries).2 = .missing ↔ queryId ∉ entries.map key) ∧
      List.Sublist (Ash.NetworkLedger.erase key queryId entries) entries := by
  refine ⟨?_, Ash.NetworkLedger.remove_found_iff key queryId entries,
    Ash.NetworkLedger.remove_missing_iff key queryId entries,
    Ash.NetworkLedger.erase_subsequence key queryId entries⟩
  simpa only [Ash.NetworkLedger.remove_sequence] using outcome

end Ash.NetworkLedger.CoreRecordRemoval
