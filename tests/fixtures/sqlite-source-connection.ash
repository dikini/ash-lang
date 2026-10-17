import @builtin.foreign as Foreign
pub foreign library NativeSqlite {
    profile "x86_64-unknown-linux-gnu"
    repr CInt = signed(32)
    repr Address = opaque
    repr InputAddress = bytes
    const Ok : CInt = 0
    const ReadWriteCreate : CInt = 6
    owner ConnectionState<C> {
        representation Address
        owned C
        teardown Close
    }
    symbol Initialize : Unit -> Foreign.Call<Int> {
        name "sqlite3_initialize"
        abi () -> CInt
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Open<C> : String -> Foreign.Call<(Int, Foreign.Output<Foreign.Nullable<ConnectionState<C>>>)> {
        name "sqlite3_open_v2"
        abi (pointer(InputAddress), out(pointer(Address)), CInt, pointer(InputAddress)) -> CInt
        operand 0 from 0 nul call_borrow
        operand 2 from constant ReadWriteCreate
        operand 3 from null
        output result as scalar
        output 1 as owner(ConnectionState<C>)
        outcome otherwise { readable result, readable 1 }
    }
    symbol Close<C> : ConnectionState<C> -> Foreign.Call<Foreign.Disposition<Int>> {
        name "sqlite3_close"
        abi (pointer(Address)) -> CInt
        operand 0 from 0 current
        output result as scalar
        retained_dependents block
        outcome result == Ok { readable result, consumed 0 }
        outcome otherwise { readable result, retained 0 }
    }
}
pub type OpenError = InvalidPath
    | InitializationFailed(Int)
    | InitializationRefused
    | NativeOpen(Int)
type Initialization = Initialized
    | InitializationError(OpenError)
initialization : Foreign.Call<Int> -> Initialization
initialization reply = match reply {
    Foreign.Returned(code) => match code == Ok {
        true => Initialized
        false => InitializationError (InitializationFailed code)
    }
    Foreign.ConversionFailed(_) => InitializationError InitializationRefused
}
pub type CloseError = NativeClose(Int)
    | BlockedByStatement
    | InvalidClose
pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)
pub type Finish<S, E> = Consumed
    | ConsumedFailure(E)
    | Retained(S, E)
pub type Completion<E> = Closed
    | ConsumedError(E)
    | RetainedError(E)
pub type Scope<I, E, T> = NotAcquired(I)
    | Completed(T, Completion<E>)
pub interface ConnectionProvider<Access> {
    is_open : Access -> Bool ! {ConnectionOps<Access>}
}
pub effect ConnectionOps<Access> {
    is_open : Access -> Bool
}
pub resource Connection<C> {
    owned C
    input String
    state ConnectionState<C>
    data Unit
    acquisition Acquire<ConnectionState<C>, Unit, OpenError>
    completion Finish<ConnectionState<C>, CloseError>
    result Scope<OpenError, CloseError, Answer> for <Answer>
    codec scope
    provider ConnectionProvider<Connection<C>>
    effect ConnectionOps<Connection<C>>
    interpret Open<C>, Close<C>
    acquire path => {
        let validated = match Foreign.checked_nul path {
            Foreign.Returned(_) => Initialized
            Foreign.ConversionFailed(_) => InitializationError InvalidPath
        }
        let initialized = match validated {
            Initialized => initialization (perform Initialize.call ())
            InitializationError(error) => InitializationError error
        }
        match initialized {
            Initialized => match perform Open<C>.call path {
                Foreign.Returned((code, Foreign.Readable(Foreign.NonNull(state)))) => match code == Ok {
                    true => Acquired(state, ())
                    false => Refused (NativeOpen code)
                }
                Foreign.Returned((code, _)) => Refused (NativeOpen code)
                Foreign.ConversionFailed(_) => Refused InvalidPath
            }
            InitializationError(error) => Refused error
        }
    }
    finish (state, data) => match perform Close<C>.call state {
        Foreign.Returned(Foreign.Consumed(code)) => match code == Ok {
            true => Consumed
            false => ConsumedFailure (NativeClose code)
        }
        Foreign.Returned(Foreign.Retained(code)) => Retained(state, NativeClose code)
        Foreign.Returned(Foreign.BlockedDependent) => Retained(state, BlockedByStatement)
        Foreign.ConversionFailed(_) => Retained(state, InvalidClose)
    }
    handlers (state, data) {
        is_open access => resume true
    }
}
