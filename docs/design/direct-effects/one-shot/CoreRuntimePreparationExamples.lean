import CoreRuntimePreparation

namespace Ash.OneShot.CoreRuntimePreparation.Examples
open CoreRuntimePreparation CoreMachine CoreSyntax

def host : Host := fun _ _ _ _ => .returned
def limits (work : Nat) : Limits :=
  ⟨work, fun _ => 1024, true, 0, 2^64 - 1, 8, 1, 0⟩
def graph : Graph := ⟨[
  ⟨0, .unit, [], none, .unit⟩,
  ⟨1, .unit, [], none, .cleanup ⟨7, .function .unit .unit []⟩ 0 0⟩], 1⟩
def environment : CoreMachine.Environment := .binding 7 (.closure 8 0 .empty) .empty
def acquire : CoreMachine.State := { control := .evaluate 1 environment }
def start : CoreMachine.State :=
  { control := .returned (.integer 42), frames := [.cleanupBoundary 0 environment 0] }
def started : CoreMachine.State :=
  { start with
    control := .evaluate 0 environment,
    frames := [.cleanupCompletion 0 (.integer 42)], observations := [.cleanupStarted 0] }

theorem acquire_exact : prepare graph host (limits 3) acquire =
    .committed { acquire with
      control := .evaluate 0 environment,
      frames := [.cleanupBoundary 0 environment 0], nextCleanup := 1,
      observations := [.entered 1, .cleanupArmed 0] } := rfl

theorem acquire_one_short : prepare graph host (limits 2) acquire =
    .stopped ⟨.workExhausted, .acquisition, .work, 3, some 2⟩ [.entered 1] := rfl

theorem start_exact : prepare graph host (limits 2) start = .committed started := rfl

theorem start_one_short : prepare graph host (limits 1) start =
    .stopped ⟨.workExhausted, .cleanup, .work, 2, some 1⟩ [] := rfl

theorem missing_binding_is_not_capacity :
    prepare graph host (limits 0) { acquire with
      control := .evaluate 1 .empty } =
      .invariant .cleanupCallback := rfl

theorem nonunit_finish_is_not_capacity :
    prepare graph host (limits 0)
      { start with frames := [.cleanupCompletion 0 (.integer 42)] } =
        .invariant .cleanupResult := rfl

theorem finish_has_no_extra_work : prepare graph host (limits 0)
    { started with
      control := .returned .unit } =
      .committed { started with
      control := .returned (.integer 42), frames := [],
        observations := [.cleanupStarted 0, .cleanupFinished 0] } := rfl

theorem finite_key_last_success : activationIncrement (2^32 - 1) (2^32 - 2) =
    .ok (2^32 - 1) := rfl

theorem finite_key_exhausted : activationIncrement (2^32 - 1) (2^32 - 1) =
    .error ⟨.configuredCapacity, .acquisition, .activationKeys, 1, some 0⟩ := rfl

def capture : List CoreMachine.Frame := [.bind 3 0 .empty, .cleanupBoundary 0 environment 9]
def owner : CoreMachine.Frame := .clauseBoundary 4 5 6 7 (some capture)
def resume : CoreMachine.State := { control := .returned .unit, frames := [.resume 4 5, owner] }
def restored : CoreMachine.State :=
  { resume with
    frames := capture ++ [.clauseBoundary 4 5 6 7 none], observations := [.resumed 7] }

theorem resume_exact : prepare graph host (limits 0) resume = .committed restored := rfl

theorem resume_one_short : prepare graph host
    { limits 0 with available := fun r => if r == .frames then 2 else 1024, capturedCells := 2 } resume =
      .stopped ⟨.configuredCapacity, .capture, .frames, 2, some 1⟩ [] := rfl

theorem resume_bad_accounting_is_invariant : prepare graph host
    { limits 0 with capturedCells := 1 } resume = .runtimeInvariant := rfl

def discard : CoreMachine.State := { control := .discard 4 5, frames := [owner], observations := [.written 0 11] }
def cut : OwnerCut := ⟨[], 4, 5, 6, 7, capture, []⟩

theorem discard_exact_preflight : prepare graph host (limits 8) discard =
    .projectionReady cut [.cleanupBoundary 0 environment 9] [.written 0 11] := rfl

theorem discard_one_short : prepare graph host (limits 7) discard =
    .stopped ⟨.workExhausted, .capture, .work, 4, some 3⟩ [.written 0 11] := rfl

def cursor : ProjectionCursor := ⟨discard, cut, capture, none, []⟩
def popped : ProjectionCursor :=
  { cursor with pending := [.cleanupBoundary 0 environment 9], popped := some (.bind 3 0 .empty) }

theorem projection_origin : beginProjection graph host (limits 8) discard = some cursor := rfl
theorem projection_not_started_on_short_preflight :
    beginProjection graph host (limits 7) discard = none := rfl
theorem projection_popped : popProjection cursor = some popped := rfl
theorem projection_spent_owner : popped.ownerFrames = [.clauseBoundary 4 5 6 7 none] := rfl
theorem projection_prior_write : popped.published = [.written 0 11] := rfl

def refusal : Failure := ⟨.allocatorRefused, .teardown, .environmentDisposal, 1, none⟩
theorem projection_stop_prior_write :
    (stopProjection popped refusal rfl).cursor.published = [.written 0 11] := rfl

def secondReservationRefuses : Host := fun ordinal _ _ _ =>
  if ordinal == 0 then .returned else .storageReservationFailed

theorem identical_later_reservation_can_refuse :
    checkAll secondReservationRefuses (limits 0)
      [.reserve .cleanup .frames 1, .reserve .cleanup .frames 1] =
        .error ⟨.storageReservationFailed, .cleanup, .frames, 1, none⟩ := rfl

#print axioms identical_later_reservation_can_refuse
#print axioms acquire_exact
#print axioms acquire_one_short
#print axioms start_exact
#print axioms start_one_short
#print axioms missing_binding_is_not_capacity
#print axioms nonunit_finish_is_not_capacity
#print axioms finish_has_no_extra_work
#print axioms finite_key_last_success
#print axioms finite_key_exhausted
#print axioms resume_exact
#print axioms resume_one_short
#print axioms resume_bad_accounting_is_invariant
#print axioms discard_exact_preflight
#print axioms discard_one_short
#print axioms projection_origin
#print axioms projection_not_started_on_short_preflight
#print axioms projection_popped
#print axioms projection_spent_owner
#print axioms projection_prior_write
#print axioms projection_stop_prior_write
end Ash.OneShot.CoreRuntimePreparation.Examples
