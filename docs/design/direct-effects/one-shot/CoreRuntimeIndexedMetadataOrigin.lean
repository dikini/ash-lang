import CoreCallableOrdinaryRuntimeOrigins
import CoreRuntimeMetadataPreparation

/-! Conditional first-acquisition consumer of actual C2 output receipts. The
original empty raw map is a retained finite input (including its presence bit),
not reconstructed from a semantic environment. This leaf does not produce
initial resource admission, Rust snapshot presence, ledger or physical lengths. -/
namespace Ash.OneShot.CoreRuntimeIndexedMetadataOrigin
open CoreCallableOrdinaryRuntimeOrigins CoreRuntimeMetadataPreparation
open CoreRuntimePreparation CoreMachine CoreSyntax
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractAdmission CoreCallableContractSource CoreValueRelation
open CoreCallableReceiverRefinement
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- No ordinary binding output can invent a resource map entry. -/
theorem ordinary_no_resource_key
    (produced : ProducedBindings registry declarations outward owners world allowed scope receiver
      graph coreOwners heap replacements rich storage lexical saved) (name : Nat) :
    saved.resourceKey name = none := by
  induction produced with
  | empty => rfl
  | bind previous source authenticated finite bounded related ih => exact ih

/-- Existing ordinary runtime origin constructors cannot certify a saved
resource environment. An extended resource transition producer is necessary. -/
theorem ordinary_cannot_resource :
    ¬ ProducedBindings registry declarations outward owners world allowed scope receiver
      graph coreOwners heap replacements rich storage lexical (.resource binder key saved) := by
  intro produced
  have impossible := ordinary_no_resource_key produced binder
  simp [CoreMachine.Environment.resourceKey] at impossible

/-- Original finite absence and original finite present-empty remain distinct. -/
def emptyRaw (present : Bool) : RawMap := ⟨present,[],[]⟩
def emptyMap (present : Bool) : MapAnnotation := ⟨present,[]⟩

theorem empty_accepted (present : Bool) : (emptyRaw present).accept = some (emptyMap present) := by
  cases present <;> rfl

theorem ordinary_empty_erasure
    (produced : ProducedBindings registry declarations outward owners world allowed scope receiver
      graph coreOwners heap replacements rich storage lexical saved) (present : Bool) :
    (emptyMap present).erases saved := by
  intro name
  exact (ordinary_no_resource_key produced name).symm

/-- The SAME current transition determines the retained installed key. -/
def acquiredRaw (binder key : Nat) : RawMap := ⟨true,[(binder,.activation key)],[]⟩
def acquiredMap (binder key : Nat) : MapAnnotation := ⟨true,[(binder,key)]⟩

theorem acquired_accepted (bounded : key ≤ 2^32-1) :
    (acquiredRaw binder key).accept = some (acquiredMap binder key) := by
  simp [acquiredRaw,acquiredMap,RawMap.accept,acceptEntries, show ¬ key > 2^32-1 from Nat.not_lt.mpr bounded]

theorem acquired_is_install (present : Bool) :
    acquiredMap binder key = install binder key (emptyMap present) := rfl

/-- Indexed receipt consumption removes map/environment agreement as an input
premise. Current graph/shape, ledger, physical length and host checks remain the
existing preparation boundary. No desired successor is supplied. -/
theorem acquisition_from_ordinary
    (produced : ProducedBindings registry declarations outward owners world allowed scope receiver
      graph coreOwners before.heap replacements rich storage lexical saved)
    (present : Bool)
    (current : before.control = .returned (.integer payload))
    (head : before.frames = .resourceInitializer site binder handle body saved :: rest)
    (success : prepare graph host ledger (emptyRaw present) before = .committed after metadata remaining) :
    CoreMachine.next graph before = .stepped after ∧
    after.control = .evaluate body (.binding handle.id (.handle before.nextActivation)
      (.resource binder before.nextActivation saved)) ∧
    metadata.map = acquiredMap binder before.nextActivation ∧
    metadata.map.erases (.binding handle.id (.handle before.nextActivation)
      (.resource binder before.nextActivation saved)) := by
  have connected := acquisition_connected (empty_accepted present)
    (ordinary_empty_erasure produced present) current head success
  have installed := produced_acquisition (empty_accepted present) current head (successful_producer success)
  exact ⟨successful_erasure success,connected.1,installed,connected.2⟩

/-- The first transition also produces an accepted retained map for the SAME
saved environment used by a later current request. No request effect rewrite
or caller supplied erasure agreement is needed. -/
theorem acquired_map_lineage
    (produced : ProducedBindings registry declarations outward owners world allowed scope receiver
      graph coreOwners heap replacements rich storage lexical saved)
    (bounded : key ≤ 2^32-1) :
    (acquiredRaw binder key).accept = some (acquiredMap binder key) ∧
    (acquiredMap binder key).erases (.binding handle (.handle key) (.resource binder key saved)) := by
  constructor
  · exact acquired_accepted bounded
  · rw [acquired_is_install false]
    exact installed_erasure (ordinary_empty_erasure produced false)

/-- The SAME produced acquisition feeds a current literal request. Acquisition
and request outcomes are separately observed; this does not assume future
request success or promise replay after refusal. -/
theorem request_from_acquired
    (produced : ProducedBindings registry declarations outward owners world allowed scope receiver
      graph coreOwners acquireBefore.heap replacements rich storage lexical saved)
    (present : Bool)
    (acquireCurrent : acquireBefore.control = .returned (.integer payload))
    (acquireHead : acquireBefore.frames = .resourceInitializer site binder handle body saved :: acquireRest)
    (acquireSuccess : prepare graph host acquireLedger (emptyRaw present) acquireBefore =
      .committed acquireAfter acquireMetadata acquireRemaining)
    (bounded : acquireBefore.nextActivation ≤ 2^32-1)
    (requestCurrent : requestBefore.control = .returned value)
    (requestHead : requestBefore.frames = .request literal operationNumber
      (.binding handle.id (.handle acquireBefore.nextActivation)
        (.resource binder acquireBefore.nextActivation saved)) :: requestRest)
    (requestSuccess : prepare graph host requestLedger (acquiredRaw binder acquireBefore.nextActivation) requestBefore =
      .committed requestAfter requestMetadata requestRemaining) :
    CoreMachine.next graph acquireBefore = .stepped acquireAfter ∧
    acquireMetadata.map = acquiredMap binder acquireBefore.nextActivation ∧
    ∃ key cut,
      literal.instantiate (CoreMachine.Environment.binding handle.id (.handle acquireBefore.nextActivation)
        (.resource binder acquireBefore.nextActivation saved)).instantiation = .cell (.activation key) ∧
      requestMetadata.map = acquiredMap binder acquireBefore.nextActivation ∧
      requestMetadata.effect = some (.cell (.activation key)) ∧ requestMetadata.cut = some cut ∧
      findInterpreter graph (.cell (.activation key)) requestRest = .ok (.cell cut) ∧
      interpretCell {requestBefore with frames := requestRest} cut operationNumber value = .stepped requestAfter := by
  have acquired := acquisition_from_ordinary produced present acquireCurrent acquireHead acquireSuccess
  have lineage := acquired_map_lineage produced bounded (binder := binder) (handle := handle.id)
  exact ⟨acquired.1,acquired.2.2.1,
    request_connected lineage.1 lineage.2 requestCurrent requestHead requestSuccess⟩

#print axioms ordinary_no_resource_key
#print axioms ordinary_cannot_resource
#print axioms empty_accepted
#print axioms ordinary_empty_erasure
#print axioms acquired_accepted
#print axioms acquired_is_install
#print axioms acquisition_from_ordinary
#print axioms acquired_map_lineage
#print axioms request_from_acquired
end Ash.OneShot.CoreRuntimeIndexedMetadataOrigin
