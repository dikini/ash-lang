import @builtin.foreign as Foreign
foreign checked library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = opaque
    repr CInt = signed(32)
    assumption Callee "the admitted native owner contract holds"
    owner State<H, R> {
        representation Address
        owned R
        host H
        teardown Free
    }
    symbol Allocate<H, R> : Int -> Foreign.CheckedCall<Foreign.Output<Foreign.Nullable<State<H, R>>>> {
        name "malloc"
        abi (Size) -> pointer(Address)
        host H
        assumes { Callee }
        operand 0 from 0 scalar
        output result as owner(State<H, R>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol Free<H, R> : State<H, R> -> Foreign.CheckedCall<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Address)) -> void
        host H
        assumes { Callee }
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
    symbol Read<H, R> : State<H, R> -> Foreign.CheckedCall<Int> {
        name "ash_owner_read"
        abi (pointer(Address)) -> CInt
        host H
        assumes { Callee }
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
}

pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)

effect Trace {
    note : Unit -> Unit
}

interface ProbeProvider<Access> {
    read : Access -> Foreign.CheckedCall<Int> ! {ProbeOps<Access>}
}
effect ProbeOps<Access> {
    read : Access -> Foreign.CheckedCall<Int>
}
resource Probe<H, R> {
    owned R
    host H
    input Int
    state State<H, R>
    data Unit
    acquisition Acquire<State<H, R>, Unit, Unit>
    completion Foreign.CheckedFinish<State<H, R>, Unit>
    result Foreign.CheckedScope<Answer, Unit, Unit> for <Answer>
    codec checked_scope
    provider ProbeProvider<Probe<H, R>>
    effect ProbeOps<Probe<H, R>>
    interpret Allocate<H, R>, Free<H, R>, Read<H, R>
    acquire size => match perform Allocate<H, R>.call size {
        Foreign.CheckedReturned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, ())
        Foreign.CheckedReturned(Foreign.Readable(Foreign.Null)) => Refused ()
        Foreign.CheckedReturned(Foreign.Unreadable) => Refused ()
        Foreign.CheckedConversionFailed(_) => Refused ()
        Foreign.BoundaryFailed(_) => Refused ()
    }
    finish (state, data) => {
        let outcome = perform Free<H, R>.call state
        let ignored = perform Trace.note ()
        match outcome {
            Foreign.CheckedReturned(Foreign.Consumed(())) => Foreign.FinishedConsumed Foreign.FinishOk
            Foreign.CheckedReturned(Foreign.Retained(())) => Foreign.FinishedRetained(state, ())
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
        read access => resume (perform Read<H, R>.call state)
    }
}

pub run : Unit -> Foreign.CheckedScope<Foreign.CheckedCall<Int>, Unit, Unit>
run () = handle (foreign host H {
    resource Probe<H, R> owner = 8 {
        read owner
    }
}) with Trace {
    note ignored => resume ()
}
