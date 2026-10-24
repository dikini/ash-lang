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
                Foreign.CheckedReturned((status, Foreign.Readable(Foreign.NonNull(state)), tail)) => match prepare_policy (status, true) {
                    PreparePublish => match tail {
                        Foreign.Readable(Foreign.NonNull(offset)) => match valid_tail (sql, offset) {
                            true => Acquired(state, (connection, status))
                            false => Refused InvalidTail
                        }
                        _ => Refused InvalidTail
                    }
                    _ => {
                        let quarantine : (ConnectionState<H, C>, Foreign.ViolationCause) -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_quarantine
                        let denied = quarantine (enclosing, Foreign.UnexpectedStatus status)
                        Refused (PrepareContradiction status)
                    }
                }
                Foreign.CheckedReturned((status, Foreign.Readable(Foreign.Null), tail)) => match prepare_policy (status, false) {
                    PrepareEmpty => match tail {
                        Foreign.Readable(Foreign.NonNull(offset)) => match valid_tail (sql, offset) {
                            true => Refused EmptySql
                            false => Refused InvalidTail
                        }
                        _ => Refused InvalidTail
                    }
                    PrepareNativeFailure => Refused (NativePrepareError status)
                    _ => {
                        let quarantine : (ConnectionState<H, C>, Foreign.ViolationCause) -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_quarantine
                        let denied = quarantine (enclosing, Foreign.ContradictoryNativeResult(status, 0))
                        Refused (PrepareContradiction status)
                    }
                }
                Foreign.CheckedReturned((status, Foreign.Unreadable, _)) => {
                    let quarantine : (ConnectionState<H, C>, Foreign.ViolationCause) -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_quarantine
                    let denied = quarantine (enclosing, Foreign.ContradictoryNativeResult(status, 1))
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
                    let quarantine : (ConnectionState<H, C>, Foreign.ViolationCause) -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_quarantine
                    let denied = quarantine (enclosing, Foreign.UnexpectedStatus status)
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
open_policy (status, nonnull) = match status == 0 {
    true => match nonnull {
        true => PublishConnection
        false => RejectOpen
    }
    false => match status == 100 {
        true => RejectOpen
        false => match status == 101 {
            true => RejectOpen
            false => match status == 21 {
                true => RejectOpen
                false => match nonnull {
                    true => RefusePartial
                    false => match status == 7 {
                        true => RefuseNoOwner
                        false => RejectOpen
                    }
                }
            }
        }
    }
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
prepare_policy (status, nonnull) = match status == 0 {
    true => match nonnull {
        true => PreparePublish
        false => PrepareEmpty
    }
    false => match status == 100 {
        true => PrepareReject
        false => match status == 101 {
            true => PrepareReject
            false => match status == 21 {
                true => PrepareReject
                false => match nonnull {
                    true => PrepareReject
                    false => PrepareNativeFailure
                }
            }
        }
    }
}

pub type FinalizePolicy = FinalizeOk
    | FinalizeNativeError
    | FinalizeReject
pub finalize_policy : Int -> FinalizePolicy
finalize_policy status = match status == 0 {
    true => FinalizeOk
    false => match status == 100 {
        true => FinalizeReject
        false => match status == 101 {
            true => FinalizeReject
            false => match status == 21 {
                true => FinalizeReject
                false => FinalizeNativeError
            }
        }
    }
}

ascii_space : Int -> Bool
ascii_space byte = match byte == 9 {
    true => true
    false => match byte == 10 {
        true => true
        false => match byte == 11 {
            true => true
            false => match byte == 12 {
                true => true
                false => match byte == 13 {
                    true => true
                    false => byte == 32
                }
            }
        }
    }
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
