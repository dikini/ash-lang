import @builtin.foreign as Foreign
import @builtin.bytes as B
import @builtin.string as Text

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
    owner StatementState<H, C, S> {
        representation Address
        owned S
        host H
        retains C
        teardown Finalize
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
    symbol Prepare<H, C, S> : (ConnectionState<H, C>, String, Int) -> Foreign.CheckedCall<(Int, Foreign.Output<Foreign.Nullable<StatementState<H, C, S>>>, Foreign.Output<Foreign.Nullable<Int>>)> {
        name "sqlite3_prepare_v2"
        abi (pointer(Address), pointer(InputAddress), CInt, out(pointer(Address)), out(pointer(InputAddress))) -> CInt
        host H
        assumes {}
        operand 0 from 0 enclosing
        operand 1 from 1 nul call_borrow
        operand 2 from 2 scalar
        output result as scalar
        output 3 as owner(StatementState<H, C, S>)
        output 4 as offset_into(1)
        outcome result == NativeOk { readable result, readable 3, readable 4 }
        outcome otherwise { readable result, readable 3, unreadable 4 }
    }
    symbol Finalize<H, C, S> : StatementState<H, C, S> -> Foreign.CheckedCall<Foreign.Disposition<Int>> {
        name "sqlite3_finalize"
        abi (pointer(Address)) -> CInt
        host H
        assumes {}
        operand 0 from 0 current
        output result as scalar
        retained_dependents block
        outcome otherwise { readable result, consumed 0 }
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

pub type InitError = NativeOpenError(Int)
    | OpenContradiction(Int)
    | OpenConversion(Foreign.ConversionError)
    | OpenBoundary(Foreign.BoundaryFailure)
pub type CloseError = NativeCloseError(Int)
    | CloseBlocked
    | CloseConversion(Foreign.ConversionError)
pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)

pub interface ConnectionProvider<Access, State> {
    open_status : Access -> Int ! {ConnectionOps<Access, State>}
    borrow : Access -> State ! {ConnectionOps<Access, State>}
}
pub effect ConnectionOps<Access, State> {
    open_status : Access -> Int
    borrow : Access -> State
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
    provider ConnectionProvider<Connection<H, C>, ConnectionState<H, C>>
    effect ConnectionOps<Connection<H, C>, ConnectionState<H, C>>
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
        borrow access => resume state
    }
}

pub type PrepareError = NativePrepareError(Int)
    | PrepareContradiction(Int)
    | EmptySql
    | InvalidSql
    | InvalidTail
    | PrepareConversion(Foreign.ConversionError)
    | PrepareBoundary(Foreign.BoundaryFailure)
pub type FinalizeError = NativeFinalizeError(Int)
    | FinalizeContradiction(Int)
    | FinalizeBlocked
    | FinalizeConversion(Foreign.ConversionError)

pub interface StatementProvider<Access> {
    prepared_status : Access -> Int ! {StatementOps<Access>}
}
pub effect StatementOps<Access> {
    prepared_status : Access -> Int
}
pub resource Statement<H, C, S> {
    owned S
    host H
    input (Connection<H, C>, String)
    state StatementState<H, C, S>
    data (Connection<H, C>, Int)
    acquisition Acquire<StatementState<H, C, S>, (Connection<H, C>, Int), PrepareError>
    completion Foreign.CheckedFinish<StatementState<H, C, S>, FinalizeError>
    result Foreign.CheckedScope<Answer, PrepareError, FinalizeError> for <Answer>
    codec checked_scope
    provider StatementProvider<Statement<H, C, S>>
    effect StatementOps<Statement<H, C, S>>
    interpret Prepare<H, C, S>, Finalize<H, C, S>
    acquire (connection, sql) => match Foreign.checked_nul sql {
        Foreign.ConversionFailed(_) => Refused InvalidSql
        Foreign.Returned(()) => {
            let enclosing = perform ConnectionOps<Connection<H, C>, ConnectionState<H, C>>.borrow connection
            let length = Text.byte_length sql + 1
            match perform Prepare<H, C, S>.call (enclosing, sql, length) {
                Foreign.CheckedReturned((status, Foreign.Readable(Foreign.NonNull(state)), tail)) => {
                    let policy = prepare_policy (status, true)
                    match (policy, prepare_tail_admitted (policy, sql, tail)) {
                        (PreparePublish, true) => Acquired(state, (connection, status))
                        (PreparePublish, false) => Refused InvalidTail
                        _ => {
                            let denied = Foreign.checked_quarantine (enclosing, Foreign.UnexpectedStatus status)
                            Refused (PrepareContradiction status)
                        }
                    }
                }
                Foreign.CheckedReturned((status, Foreign.Readable(Foreign.Null), tail)) => {
                    let policy = prepare_policy (status, false)
                    match (policy, prepare_tail_admitted (policy, sql, tail)) {
                        (PrepareEmpty, true) => Refused EmptySql
                        (PrepareEmpty, false) => Refused InvalidTail
                        (PrepareNativeFailure, _) => Refused (NativePrepareError status)
                        _ => {
                            let denied = Foreign.checked_quarantine (enclosing, Foreign.ContradictoryNativeResult(status, 0))
                            Refused (PrepareContradiction status)
                        }
                    }
                }
                Foreign.CheckedReturned((status, Foreign.Unreadable, _)) => {
                    let denied = Foreign.checked_quarantine (enclosing, Foreign.ContradictoryNativeResult(status, 1))
                    Refused (PrepareContradiction status)
                }
                Foreign.CheckedConversionFailed(error) => Refused (PrepareConversion error)
                Foreign.BoundaryFailed(reason) => Refused (PrepareBoundary reason)
            }
        }
    }
    finish (state, (connection, prepared)) => {
        let outcome = perform Finalize<H, C, S>.call state
        match outcome {
            Foreign.CheckedReturned(Foreign.Consumed(status)) => match finalize_policy status {
                FinalizeOk => Foreign.FinishedConsumed Foreign.FinishOk
                FinalizeNativeError => Foreign.FinishedConsumed (Foreign.FinishError (NativeFinalizeError status))
                FinalizeReject => {
                    let enclosing = perform ConnectionOps<Connection<H, C>, ConnectionState<H, C>>.borrow connection
                    let denied = Foreign.checked_quarantine (enclosing, Foreign.UnexpectedStatus status)
                    Foreign.FinishedConsumed (Foreign.FinishError (FinalizeContradiction status))
                }
            }
            Foreign.CheckedReturned(Foreign.Retained(status)) => Foreign.FinishedRetained(state, NativeFinalizeError status)
            Foreign.CheckedReturned(Foreign.BlockedDependent) => Foreign.FinishedRetained(state, FinalizeBlocked)
            Foreign.CheckedConversionFailed(error) => Foreign.FinishedRetained(state, FinalizeConversion error)
            Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason
        }
    }
    handlers (state, (connection, prepared)) {
        prepared_status access => resume prepared
    }
}

pub type OpenPolicy = PublishConnection
    | RefusePartial
    | RefuseNoOwner
    | RejectOpen
pub open_policy : (Int, Bool) -> OpenPolicy
open_policy (status, nonnull) = match (
    status == 0, status == 100, status == 101, status == 21, status == 7, nonnull
) {
    (true, _, _, _, _, true) => PublishConnection
    (false, false, false, false, _, true) => RefusePartial
    (false, false, false, false, true, false) => RefuseNoOwner
    _ => RejectOpen
}

pub type Execution = Prepared
    | Row
    | Done
    | ExecutionError
pub type Bindings = Known
    | Uncertain
pub type Availability = Usable
    | Unavailable
pub type Policy = Policy(Execution, Bindings, Availability)
pub type Reply = ReturnedStatus(Int)
    | PreEntryRefused
    | BoundaryLost

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

pub type PreparePolicy = PreparePublish
    | PrepareEmpty
    | PrepareNativeFailure
    | PrepareReject
pub prepare_policy : (Int, Bool) -> PreparePolicy
prepare_policy (status, nonnull) = match (
    status == 0, status == 100, status == 101, status == 21, nonnull
) {
    (true, _, _, _, true) => PreparePublish
    (true, _, _, _, false) => PrepareEmpty
    (false, false, false, false, false) => PrepareNativeFailure
    _ => PrepareReject
}

pub type FinalizePolicy = FinalizeOk
    | FinalizeNativeError
    | FinalizeReject
pub finalize_policy : Int -> FinalizePolicy
finalize_policy status = match (status == 0, status == 100, status == 101, status == 21) {
    (true, _, _, _) => FinalizeOk
    (false, false, false, false) => FinalizeNativeError
    _ => FinalizeReject
}

ascii_space : Int -> Bool
ascii_space byte = match (
    byte == 9, byte == 10, byte == 11, byte == 12, byte == 13, byte == 32
) {
    (false, false, false, false, false, false) => false
    _ => true
}

tail_whitespace : (Bytes, Int) -> Bool
tail_whitespace (bytes, offset) = match offset == B.length bytes {
    true => true
    false => match B.at (bytes, offset) {
        B.InvalidIndex => false
        B.ByteAt(byte) => match ascii_space byte {
            true => tail_whitespace (bytes, offset + 1)
            false => false
        }
    }
}
pub valid_tail : (String, Int) -> Bool
valid_tail (sql, offset) = tail_whitespace (Text.to_utf8 sql, offset)

readable_tail_admitted : (String, Foreign.Output<Foreign.Nullable<Int>>) -> Bool
readable_tail_admitted (sql, tail) = match tail {
    Foreign.Readable(Foreign.NonNull(offset)) => valid_tail (sql, offset)
    _ => false
}
prepare_tail_admitted : (PreparePolicy, String, Foreign.Output<Foreign.Nullable<Int>>) -> Bool
prepare_tail_admitted (policy, sql, tail) = match policy {
    PreparePublish => readable_tail_admitted (sql, tail)
    PrepareEmpty => readable_tail_admitted (sql, tail)
    _ => false
}
