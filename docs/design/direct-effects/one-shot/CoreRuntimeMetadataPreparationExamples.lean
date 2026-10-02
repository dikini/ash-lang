import CoreRuntimeMetadataPreparation
namespace Ash.OneShot.CoreRuntimeMetadataPreparation.Examples
open CoreRuntimeMetadataPreparation CoreRuntimePreparation CoreMachine CoreSyntax

def host : Host := fun _ _ _ _ => .returned
def ledger (work : Nat) : Ledger := ⟨⟨work,fun _ => 1024,true,0,2^64-1,0,0,0⟩,0,8,0,true⟩
def graph : Graph := ⟨[
  ⟨0,.unit,[],none,.unit⟩,
  ⟨1,.integer,[],none,.resource 0 ⟨7,.reference (.bound 0)⟩ 0 0⟩,
  ⟨2,.unit,[],none,.handler 8 (.user 3 []) 0 []⟩,
  ⟨3,.unit,[],none,.handler 9 (.cell (.bound 0)) 0 []⟩],1⟩
def raw : RawMap := ⟨true,[(0,.activation 4)],[]⟩
def map : MapAnnotation := ⟨true,[(0,4)]⟩
def environment : CoreMachine.Environment := .resource 0 4 .empty
def acquire : CoreMachine.State :=
  {control := .returned (.integer 41),frames := [.resourceInitializer 1 0 ⟨7,.reference (.bound 0)⟩ 0 environment],nextActivation := 7}

theorem absent_presence : RawMap.accept ⟨false,[],[]⟩ = some ⟨false,[]⟩ := rfl
theorem empty_present : RawMap.accept ⟨true,[],[]⟩ = some ⟨true,[]⟩ := rfl
theorem unsupported_type : RawMap.accept ⟨true,[(0,.unsupported)],[]⟩ = none := rfl
theorem unsupported_row : RawMap.accept ⟨true,[],[0]⟩ = none := rfl
theorem duplicate_rejected : RawMap.accept ⟨true,[(0,.activation 4),(0,.activation 8)],[]⟩ = none := rfl
theorem absent_with_entries_rejected : RawMap.accept ⟨false,[(0,.activation 4)],[]⟩ = none := rfl
theorem activation_word_rejected : RawMap.accept ⟨true,[(0,.activation (2^32))],[]⟩ = none := rfl

theorem shadow_work : work (acquisitionMetadata map) = 5 := rfl
theorem shadow_result : install 0 7 map = ⟨true,[(0,7)]⟩ := rfl
theorem original_map_agrees : map.erases environment := by
  intro name
  by_cases same : name = 0
  · subst name; rfl
  · simp [map,environment,lookup,Environment.resourceKey,same,Ne.symm same]

theorem acquire_exact :
    ∃ metadata remaining, prepare graph host (ledger 5) raw acquire =
      .committed {acquire with
        control := .evaluate 0 (.binding 7 (.handle 7) (.resource 0 7 environment))
        frames := [.resourceBoundary 1 7 41]
        nextActivation := 8
        observations := [.acquired 1 7]} metadata remaining := by
  exact ⟨_,_,rfl⟩

theorem acquire_one_short : prepare graph host (ledger 4) raw acquire =
    .stopped ⟨.workExhausted,.acquisition,.work,none,some 0⟩ [] := rfl

theorem old_clone_diagnostic : runRequests host (ledger 2).limits (acquisitionMetadata map) =
    .error ⟨.workExhausted,.acquisition,.work,none,some 0⟩ := rfl

theorem parameter_diagnostic : runRequests host (ledger 3).limits (acquisitionMetadata map) =
    .error ⟨.workExhausted,.acquisition,.work,some 1,some 0⟩ := rfl

theorem finite_key_refusal : prepare graph host (ledger 5) raw {acquire with nextActivation := 2^32-1} =
    .stopped ⟨.configuredCapacity,.acquisition,.activationKeys,some 1,some 0⟩ [] := rfl

def request : CoreMachine.State := {control := .returned (.handle 4),frames := [
  .request (.cell (.bound 0)) 0 environment,
  .bind 6 0 .empty,.handlerBoundary 2 .empty 1,.resourceBoundary 1 4 41],observations := [.written 4 40]}

theorem request_exact : ∃ metadata remaining,
    prepare graph host (ledger 6) raw request = .committed {request with
      control := .returned (.integer 41)
      frames := [.bind 6 0 .empty,.handlerBoundary 2 .empty 1,.resourceBoundary 1 4 41]
      observations := [.written 4 40,.read 4 41]} metadata remaining := by exact ⟨_,_,rfl⟩

theorem request_one_short : prepare graph host (ledger 5) raw request =
    .stopped ⟨.workExhausted,.access,.work,some 1,some 0⟩ [.written 4 40] := rfl

theorem same_id_unsupported : produce graph (ledger 100) raw {request with frames := [
    .request (.cell (.bound 0)) 0 environment,.handlerBoundary 3 environment 2,.resourceBoundary 1 4 41]} =
      .error (.sameIdHandler 3) := rfl

theorem missing_map_not_capacity : produce graph (ledger 0) ⟨false,[],[]⟩ request =
    .error (.unbound 0) := rfl

def laterRefusal : Host := fun ordinal _ _ _ => if ordinal == 1 then .storageReservationFailed else .returned

theorem later_reservation_refusal : runRequests laterRefusal (ledger 3).limits
    [reserve .access .instantiationStorage 1,reserve .access .instantiationStorage 1] =
      .error ⟨.storageReservationFailed,.access,.instantiationStorage,some 1,none⟩ := rfl

#print axioms absent_presence
#print axioms empty_present
#print axioms unsupported_type
#print axioms unsupported_row
#print axioms duplicate_rejected
#print axioms absent_with_entries_rejected
#print axioms activation_word_rejected
#print axioms shadow_work
#print axioms shadow_result
#print axioms original_map_agrees
#print axioms acquire_exact
#print axioms acquire_one_short
#print axioms old_clone_diagnostic
#print axioms parameter_diagnostic
#print axioms finite_key_refusal
#print axioms request_exact
#print axioms request_one_short
#print axioms same_id_unsupported
#print axioms missing_map_not_capacity
#print axioms later_reservation_refusal
end Ash.OneShot.CoreRuntimeMetadataPreparation.Examples
