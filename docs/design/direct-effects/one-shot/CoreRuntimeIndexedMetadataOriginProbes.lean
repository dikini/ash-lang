import CoreRuntimeIndexedMetadataOrigin
namespace Ash.OneShot.CoreRuntimeIndexedMetadataOrigin.Probes
open CoreRuntimeIndexedMetadataOrigin CoreRuntimeMetadataPreparation CoreRuntimePreparation CoreMachine CoreSyntax
open CoreCallableOrdinaryRuntimeOrigins

def host : Host := fun _ _ _ _ => .returned
def ledger (work : Nat) : CoreRuntimeMetadataPreparation.Ledger := ⟨⟨work,fun _ => 1024,true,0,2^64-1,0,0,0⟩,0,8,0,true⟩
def graph : Graph := ⟨[
  ⟨0,.unit,[],none,.unit⟩,
  ⟨1,.integer,[],none,.resource 0 ⟨7,.reference (.bound 0)⟩ 0 0⟩],1⟩
def acquire : CoreMachine.State :=
  {control := .returned (.integer 41),frames := [.resourceInitializer 1 0 ⟨7,.reference (.bound 0)⟩ 0 .empty],nextActivation := 4}
def after : CoreMachine.State := {acquire with
  control := .evaluate 0 (.binding 7 (.handle 4) (.resource 0 4 .empty))
  frames := [.resourceBoundary 1 4 41],nextActivation := 5,observations := [.acquired 1 4]}

theorem ordinaryOrigin (registry : CoreCallableContractRegistries.Registry) (declarations : Instantiation.DeclarationRegistry) :
    ProducedBindings registry declarations [] (fun _ => none) [] [] .none [] graph [] [] [] [] [] [] .empty := .empty

theorem original_none : (emptyRaw false).accept = some (emptyMap false) := rfl
theorem original_some_empty : (emptyRaw true).accept = some (emptyMap true) := rfl
theorem presence_distinct : emptyRaw false ≠ emptyRaw true := by decide
theorem installed_present : acquiredRaw 0 4 = ⟨true,[(0,.activation 4)],[]⟩ := rfl

theorem acquire_exact : ∃ metadata remaining,
    prepare graph host (ledger 3) (emptyRaw false) acquire = .committed after metadata remaining := by
  exact ⟨_,_,rfl⟩
theorem acquire_present_empty_exact : ∃ metadata remaining,
    prepare graph host (ledger 3) (emptyRaw true) acquire = .committed after metadata remaining := by
  exact ⟨_,_,rfl⟩
theorem acquire_one_short : prepare graph host (ledger 2) (emptyRaw false) acquire =
    .stopped ⟨.workExhausted,.acquisition,.work,none,some 0⟩ [] := rfl

theorem connected_empty (registry : CoreCallableContractRegistries.Registry) (declarations : Instantiation.DeclarationRegistry) :
    ∃ metadata remaining,
      prepare graph host (ledger 3) (emptyRaw false) acquire = .committed after metadata remaining ∧
      CoreMachine.next graph acquire = .stepped after ∧ metadata.map = acquiredMap 0 4 ∧
      metadata.map.erases (.binding 7 (.handle 4) (.resource 0 4 .empty)) := by
  obtain ⟨metadata,remaining,success⟩ := acquire_exact
  have connected := acquisition_from_ordinary (ordinaryOrigin registry declarations) false rfl rfl success
  exact ⟨metadata,remaining,success,connected.1,connected.2.2⟩

def request : CoreMachine.State := {control := .returned (.handle 4),frames := [
  .request (.cell (.bound 0)) 0 (.binding 7 (.handle 4) (.resource 0 4 .empty)),.resourceBoundary 1 4 41],observations := [.acquired 1 4]}
def requestAfter : CoreMachine.State := {request with
  control := .returned (.integer 41),frames := [.resourceBoundary 1 4 41],observations := [.acquired 1 4,.read 4 41]}

theorem request_exact : ∃ metadata remaining,
    prepare graph host (ledger 4) (acquiredRaw 0 4) request = .committed requestAfter metadata remaining := by
  exact ⟨_,_,rfl⟩
theorem request_one_short : prepare graph host (ledger 3) (acquiredRaw 0 4) request =
    .stopped ⟨.workExhausted,.access,.work,some 1,some 0⟩ [.acquired 1 4] := rfl

theorem connected_request (registry : CoreCallableContractRegistries.Registry) (declarations : Instantiation.DeclarationRegistry) :
    ∃ acquireMetadata acquireRemaining requestMetadata requestRemaining,
      prepare graph host (ledger 3) (emptyRaw false) acquire = .committed after acquireMetadata acquireRemaining ∧
      prepare graph host (ledger 4) (acquiredRaw 0 4) request = .committed requestAfter requestMetadata requestRemaining ∧
      CoreMachine.next graph acquire = .stepped after ∧
      acquireMetadata.map = acquiredMap 0 4 ∧
      requestMetadata.map = acquiredMap 0 4 ∧ requestMetadata.effect = some (.cell (.activation 4)) := by
  obtain ⟨am,ar,asuccess⟩ := acquire_exact
  obtain ⟨rm,rr,rsuccess⟩ := request_exact
  have connected := request_from_acquired (ordinaryOrigin registry declarations) false rfl rfl asuccess
    (by decide) rfl rfl rsuccess
  obtain ⟨key,cut,literal,map,effect,_⟩ := connected.2.2
  have keyEq : key = 4 := by
    change Instantiation.Effect.cell (.activation 4) = .cell (.activation key) at literal
    exact (Instantiation.ResourceName.activation.inj (Instantiation.Effect.cell.inj literal)).symm
  subst key
  exact ⟨am,ar,rm,rr,asuccess,rsuccess,connected.1,connected.2.1,map,effect⟩

/-- A missing retained acquisition map remains an invariant error, even with
zero budget. It is not reclassified as resource exhaustion. -/
theorem missing_map_not_capacity : produce graph (ledger 0) (emptyRaw false) request = .error (.unbound 0) := rfl
theorem word_rejected : (acquiredRaw 0 (2^32)).accept = none := rfl

#print axioms original_none
#print axioms original_some_empty
#print axioms presence_distinct
#print axioms installed_present
#print axioms acquire_exact
#print axioms acquire_present_empty_exact
#print axioms acquire_one_short
#print axioms connected_empty
#print axioms request_exact
#print axioms request_one_short
#print axioms connected_request
#print axioms missing_map_not_capacity
#print axioms word_rejected
end Ash.OneShot.CoreRuntimeIndexedMetadataOrigin.Probes
