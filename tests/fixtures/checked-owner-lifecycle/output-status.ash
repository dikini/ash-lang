import @builtin.foreign as Foreign
foreign checked library NativeSqlite {
    profile "x86_64-unknown-linux-gnu"
    repr CInt = signed(32)
    repr Address = opaque
    repr InputAddress = bytes
    const NativeOk : CInt = 0
    const ReadWriteCreate : CInt = 6
    owner State<H, R> {
        representation Address
        owned R
        host H
        teardown Close
    }
    symbol Open<H, R> : String -> Foreign.CheckedCall<(Int, Foreign.Output<Foreign.Nullable<State<H, R>>>)> {
        name "sqlite3_open_v2"
        abi (pointer(InputAddress), out(pointer(Address)), CInt, pointer(InputAddress)) -> CInt
        host H
        assumes {}
        operand 0 from 0 nul call_borrow
        operand 2 from constant ReadWriteCreate
        operand 3 from null
        output result as scalar
        output 1 as owner(State<H, R>)
        outcome otherwise { readable result, readable 1 }
    }
    symbol Close<H, R> : State<H, R> -> Foreign.CheckedCall<Foreign.Disposition<Int>> {
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
}

pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)

effect Trace {
    note : Unit -> Unit
}

interface ProbeProvider<Access> {
    read : Access -> Int ! {ProbeOps<Access>}
}
effect ProbeOps<Access> {
    read : Access -> Int
}
resource Probe<H, R> {
    owned R
    host H
    input String
    state State<H, R>
    data Unit
    acquisition Acquire<State<H, R>, Unit, Unit>
    completion Foreign.CheckedFinish<State<H, R>, Unit>
    result Foreign.CheckedScope<Answer, Unit, Unit> for <Answer>
    codec checked_scope
    provider ProbeProvider<Probe<H, R>>
    effect ProbeOps<Probe<H, R>>
    interpret Open<H, R>, Close<H, R>
    acquire size => match perform Open<H, R>.call size {
        Foreign.CheckedReturned((status, Foreign.Readable(Foreign.NonNull(state)))) => Acquired(state, ())
        Foreign.CheckedReturned((status, Foreign.Readable(Foreign.Null))) => Refused ()
        Foreign.CheckedReturned((status, Foreign.Unreadable)) => Refused ()
        Foreign.CheckedConversionFailed(_) => Refused ()
        Foreign.BoundaryFailed(_) => Refused ()
    }
    finish (state, data) => {
        let outcome = perform Close<H, R>.call state
        let ignored = perform Trace.note ()
        match outcome {
            Foreign.CheckedReturned(Foreign.Consumed(status)) => Foreign.FinishedConsumed Foreign.FinishOk
            Foreign.CheckedReturned(Foreign.Retained(status)) => Foreign.FinishedRetained(state, ())
            Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason
            Foreign.CheckedReturned(Foreign.BlockedDependent) => {
                let ignored = "unreachable for an authenticated State-only void teardown; supplies no finish witness"
                Foreign.FinishedConsumed Foreign.FinishOk
            }
            Foreign.CheckedConversionFailed(_) => {
                let ignored = "unreachable for an authenticated State-only void teardown; supplies no finish witness"
                Foreign.FinishedConsumed Foreign.FinishOk
            }
        }
    }
    handlers (state, data) {
        read access => resume 42
    }
}

pub run : Unit -> Foreign.CheckedScope<Int, Unit, Unit>
run () = handle (foreign host H {
    resource Probe<H, R> owner = ":memory:" {
        read owner
    }
}) with Trace {
    note ignored => resume ()
}
