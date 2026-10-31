import NetworkLedgerCoreLookup
import NetworkLedgerCoreRecordProjection

/- Record instantiation of the finite lookup proof. Exact linked identities,
   capture values, provider behavior and represented finite inputs remain
   premises of a consuming call. -/
namespace Ash.NetworkLedger.CoreRecordLookup

open Ash.NetworkLedger
open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreValues
open Ash.NetworkLedger.CoreLookup
open Ash.NetworkLedger.CoreRecordProjection

/-- A whole Record preserves its original key and the other three fields. -/
def RecordEntry (tag : Constructor) (store : Store) (value : Value) (keyAddress : Nat) : Prop :=
  ∃ address resolved payload tuple parent phase children,
    value = .location address ∧
    Resolve store address resolved ∧ readCell store resolved = some [.tag tag, .location payload] ∧
    Resolve store payload tuple ∧ readCell store tuple = some [.location keyAddress, parent, phase, children]

/-- Preserving all old cells and aliases preserves the whole Record. -/
theorem record_entry_retained (tag : Constructor) (before after : Store) (entry : Value) (keyAddress : Nat)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ location old, readCell before location = some old → readCell after location = some old)
    (entryRep : RecordEntry tag before entry keyAddress) : RecordEntry tag after entry keyAddress := by
  obtain ⟨address, resolved, payload, tuple, parent, phase, children, same, resolution, cell,
    payloadResolution, fields⟩ := entryRep
  exact ⟨address, resolved, payload, tuple, parent, phase, children, same,
    resolve_preserved aliases cells resolution, cells resolved _ cell,
    resolve_preserved aliases cells payloadResolution, cells tuple _ fields⟩

/-- Exact normalized stored Record projection used by the linked call. -/
structure RecordProjectionShape (program : Program) (call : NodeId) where
  function : NodeId
  argument : NodeId
  code : NodeId
  context : NodeId
  storage : NodeId
  parameter : Binder
  body : NodeId
  scrutinee : NodeId
  returnKey : NodeId
  functionName : Binder
  recordName : Binder
  keyName : Binder
  parentName : Binder
  phaseName : Binder
  childrenName : Binder
  record : Constructor
  differentParent : keyName ≠ parentName
  differentPhase : keyName ≠ phaseName
  differentChildren : keyName ≠ childrenName
  callShape : program call = some (.apply function argument)
  functionShape : program function = some (.variable functionName)
  argumentShape : program argument = some (.variable recordName)
  closureShape : program code = some (.closure context [] storage parameter body)
  bodyShape : program body = some (.caseMatch scrutinee
    [(.constructor record (some (.tuple [.binder keyName, .binder parentName, .binder phaseName,
      .binder childrenName])), returnKey)])
  scrutineeShape : program scrutinee = some (.variable parameter)
  returnShape : program returnKey = some (.variable keyName)

/-- Every finite Record lookup returns the first matching original Record. -/
theorem record_lookup_body_correct (c : Constructors) (program : Program) (absent present : Constructor)
    (checked : CheckedLookupBase c program absent present)
    (projection : RecordProjectionShape program checked.projection)
    (functionName : projection.functionName = checked.projectionName)
    (entryName : projection.recordName = checked.entryName)
    (code : projection.code = checked.projectionCode)
    (captureValues : List Value) (captureEnv : Environment)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved : Nat)
    (wanted : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv) :
    ∀ start finish payload payloadResolved list result,
      Resolve start payload payloadResolved → readCell start payloadResolved = some [wanted, list] →
      BoundedLocations start → Ident c start wanted queryId → Children c start list entries →
      RepresentedEntries c (RecordEntry projection.record) start key entries →
      Resolve start selfAddress selfResolved →
      readCell start selfResolved = some (.closureCode checked.code :: captureValues) →
      Resolve start comparisonAddress comparisonResolved →
      readCell start comparisonResolved = some [.closureCode checked.comparator.code] →
      Resolve start projectionAddress projectionResolved →
      readCell start projectionResolved = some [.closureCode checked.projectionCode] →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body start result finish →
      LookupOutcome absent present start finish result (Ash.NetworkLedger.lookup key queryId entries) := by
  apply lookup_body_correct_with c program absent present checked (RecordEntry projection.record)
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

end Ash.NetworkLedger.CoreRecordLookup
