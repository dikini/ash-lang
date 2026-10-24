import @builtin.foreign as Foreign

pub foreign checked library NativeSqlite {
    profile "x86_64-unknown-linux-gnu"
    repr CInt = signed(32)
    repr Address = opaque
    repr InputAddress = bytes
    const NativeOk : CInt = 0
    const ReadWriteCreate : CInt = 6
    owner ConnectionState<H, C> {
        representation Address
        owned C
        host H
        teardown Close
    }
    symbol Open<H, C> : String -> Foreign.CheckedCall<(Int, Foreign.Output<Foreign.Nullable<ConnectionState<H, C>>>)> {
        name "sqlite3_open_v2"
        abi (pointer(InputAddress), out(pointer(Address)), CInt, pointer(InputAddress)) -> CInt
        host H
        assumes {}
        operand 0 from 0 nul call_borrow
        operand 2 from constant ReadWriteCreate
        operand 3 from null
        output result as scalar
        output 1 as owner(ConnectionState<H, C>)
        outcome otherwise { readable result, readable 1 }
    }
    symbol Close<H, C> : ConnectionState<H, C> -> Foreign.CheckedCall<Foreign.Disposition<Int>> {
        name "sqlite3_close"
        abi (pointer(Address)) -> CInt
        host H
        assumes {}
        operand 0 from 0 current
        output result as scalar
        retained_dependents block
        outcome result == NativeOk { readable result, consumed 0 }
        outcome otherwise { readable result, retained 0 }
    }
    symbol Initialize<H> : Unit -> Foreign.CheckedCall<Int> {
        name "sqlite3_initialize"
        abi () -> CInt
        host H
        assumes {}
        output result as scalar
        outcome otherwise { readable result }
    }
}

// Initialization is an explicit host responsibility before acquiring Connection.
// This module never shuts down SQLite's shared host state.
pub type InitError = NativeOpenError(Int)
    | OpenContradiction(Int)
    | OpenConversion(Foreign.ConversionError)
    | OpenBoundary(Foreign.BoundaryFailure)
pub type CloseError = NativeCloseError(Int)
    | CloseBlocked
    | CloseConversion(Foreign.ConversionError)
pub type Acquire<S, D, I> = Acquired(S, D) | Refused(I)

pub interface ConnectionProvider<Access> {
    open_status : Access -> Int ! {ConnectionOps<Access>}
}
pub effect ConnectionOps<Access> {
    open_status : Access -> Int
}
pub resource Connection<H, C> {
    owned C
    host H
    input String
    state ConnectionState<H, C>
    data Int
    acquisition Acquire<ConnectionState<H, C>, Int, InitError>
    completion Foreign.CheckedFinish<ConnectionState<H, C>, CloseError>
    result Foreign.CheckedScope<Answer, InitError, CloseError> for <Answer>
    codec checked_scope
    provider ConnectionProvider<Connection<H, C>>
    effect ConnectionOps<Connection<H, C>>
    interpret Open<H, C>, Close<H, C>
    acquire path => match perform Open<H, C>.call path {
        Foreign.CheckedReturned((status, Foreign.Readable(Foreign.NonNull(state)))) => match open_policy (status, true) {
            PublishConnection => Acquired(state, status)
            RefusePartial => Refused (NativeOpenError status)
            _ => {
                let reject : Foreign.ViolationCause -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_reject_acquisition
                let denied = reject (Foreign.UnexpectedStatus status)
                Refused (OpenContradiction status)
            }
        }
        Foreign.CheckedReturned((status, Foreign.Readable(Foreign.Null))) => match open_policy (status, false) {
            RefuseNoOwner => Refused (NativeOpenError status)
            _ => {
                let reject : Foreign.ViolationCause -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_reject_acquisition
                let denied = reject (Foreign.ContradictoryNativeResult(status, 0))
                Refused (OpenContradiction status)
            }
        }
        Foreign.CheckedReturned((status, Foreign.Unreadable)) => {
            let reject : Foreign.ViolationCause -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_reject_acquisition
            let denied = reject (Foreign.UnexpectedStatus status)
            Refused (OpenContradiction status)
        }
        Foreign.CheckedConversionFailed(error) => Refused (OpenConversion error)
        Foreign.BoundaryFailed(reason) => Refused (OpenBoundary reason)
    }
    finish (state, data) => match perform Close<H, C>.call state {
        Foreign.CheckedReturned(Foreign.Consumed(status)) => match status == 0 {
            true => Foreign.FinishedConsumed Foreign.FinishOk
            false => Foreign.FinishedConsumed (Foreign.FinishError (NativeCloseError status))
        }
        Foreign.CheckedReturned(Foreign.Retained(status)) => Foreign.FinishedRetained(state, NativeCloseError status)
        Foreign.CheckedReturned(Foreign.BlockedDependent) => Foreign.FinishedRetained(state, CloseBlocked)
        Foreign.CheckedConversionFailed(error) => Foreign.FinishedRetained(state, CloseConversion error)
        Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason
    }
    handlers (state, status) {
        open_status access => resume status
    }
}

// Pure classification supplements the resource's direct guarded branches.
// A partial owner remains unpublished; the common guard owns once-only Close.
pub type OpenPolicy = PublishConnection | RefusePartial | RefuseNoOwner | RejectOpen
pub open_policy : (Int, Bool) -> OpenPolicy
open_policy (status, nonnull) = match status == 0 {
    true => match nonnull { true => PublishConnection false => RejectOpen }
    false => match status == 100 {
        true => RejectOpen
        false => match status == 101 {
            true => RejectOpen
            false => match status == 21 {
                true => RejectOpen
                false => match nonnull {
                    true => RefusePartial
                    false => match status == 7 { true => RefuseNoOwner false => RejectOpen }
                }
            }
        }
    }
}

pub type Execution = Prepared | Row | Done | ExecutionError
pub type Bindings = Known | Uncertain
pub type Availability = Usable | Unavailable
pub type Policy = Policy(Execution, Bindings, Availability)
// ReturnedStatus carries a conforming, operation-specific admitted status only.
// Statement handlers must reject misuse/contradictions before applying these helpers.
// This slice does not yet supply those handlers, row generations, or copied text.
pub type Reply = ReturnedStatus(Int) | PreEntryRefused | BoundaryLost

pub initial_policy : Unit -> Policy
initial_policy () = Policy(Prepared, Known, Usable)

pub after_bind : (Policy, Reply) -> Policy
after_bind (Policy(execution, bindings, availability), reply) = match reply {
    ReturnedStatus(code) => match code == 0 {
        true => Policy(execution, bindings, availability)
        false => Policy(execution, Uncertain, availability)
    }
    PreEntryRefused => Policy(execution, bindings, availability)
    BoundaryLost => Policy(execution, bindings, Unavailable)
}

pub after_clear : (Policy, Reply) -> Policy
after_clear (Policy(execution, bindings, availability), reply) = match reply {
    ReturnedStatus(code) => match code == 0 {
        true => Policy(execution, Known, availability)
        false => Policy(execution, Uncertain, availability)
    }
    PreEntryRefused => Policy(execution, bindings, availability)
    BoundaryLost => Policy(execution, bindings, Unavailable)
}

pub after_reset : (Policy, Reply) -> Policy
after_reset (Policy(execution, bindings, availability), reply) = match reply {
    ReturnedStatus(_) => Policy(Prepared, bindings, availability)
    PreEntryRefused => Policy(execution, bindings, availability)
    BoundaryLost => Policy(execution, bindings, Unavailable)
}

pub can_bind : Policy -> Bool
can_bind (Policy(execution, bindings, availability)) = match availability {
    Unavailable => false
    Usable => match execution {
        Prepared => match bindings {
            Known => true
            Uncertain => false
        }
        _ => false
    }
}

pub can_clear : Policy -> Bool
can_clear (Policy(execution, _, availability)) = match availability {
    Unavailable => false
    Usable => match execution {
        Prepared => true
        _ => false
    }
}

pub can_step : Policy -> Bool
can_step (Policy(execution, bindings, availability)) = match availability {
    Unavailable => false
    Usable => match bindings {
        Uncertain => false
        Known => match execution {
            Prepared => true
            Row => true
            _ => false
        }
    }
}

pub after_step : (Policy, Reply) -> Policy
after_step (Policy(execution, bindings, availability), reply) = match reply {
    ReturnedStatus(code) => match code == 100 {
        true => Policy(Row, bindings, availability)
        false => match code == 101 {
            true => Policy(Done, bindings, availability)
            false => Policy(ExecutionError, bindings, availability)
        }
    }
    PreEntryRefused => Policy(execution, bindings, availability)
    BoundaryLost => Policy(execution, bindings, Unavailable)
}
