import @builtin.foreign as Foreign
import @builtin.cell as Cell
foreign checked library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = opaque
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
}

pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)

effect Trace {
    note : Unit -> Unit
}

interface ProbeProvider<Access> {
    store : (Access, Unit -> Int) -> Unit ! {ProbeOps<Access>}
    read : Access -> Int ! {ProbeOps<Access>}
}
effect ProbeOps<Access> {
    store : (Access, Unit -> Int) -> Unit
    read : Access -> Int
}
resource Probe<H, R> {
    owned R
    host H
    input (Unit -> Int)
    state State<H, R>
    data (Unit -> Int)
    acquisition Acquire<State<H, R>, Unit -> Int, Unit>
    completion Foreign.CheckedFinish<State<H, R>, Unit -> Int>
    result Foreign.CheckedScope<Answer, Unit, Unit -> Int> for <Answer>
    codec checked_scope
    provider ProbeProvider<Probe<H, R>>
    effect ProbeOps<Probe<H, R>>
    interpret Allocate<H, R>, Free<H, R>
    acquire initial => match perform Allocate<H, R>.call 8 {
        Foreign.CheckedReturned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, initial)
        Foreign.CheckedReturned(Foreign.Readable(Foreign.Null)) => Refused ()
        Foreign.CheckedReturned(Foreign.Unreadable) => Refused ()
        Foreign.CheckedConversionFailed(_) => Refused ()
        Foreign.BoundaryFailed(_) => Refused ()
    }
    finish (state, data) => {
        let outcome = perform Free<H, R>.call state
        let ignored = perform Trace.note ()
        match outcome {
            Foreign.CheckedReturned(Foreign.Consumed(())) => Foreign.FinishedConsumed (Foreign.FinishError data)
            Foreign.CheckedReturned(Foreign.Retained(())) => Foreign.FinishedRetained(state, data)
            Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason
            Foreign.CheckedReturned(Foreign.BlockedDependent) => {
                let ignored = "candidate impossible path; not witness; refinement awaiting CP assessment"
                Foreign.FinishedConsumed Foreign.FinishOk
            }
            Foreign.CheckedConversionFailed(_) => {
                let ignored = "candidate impossible path; not witness; refinement awaiting CP assessment"
                Foreign.FinishedConsumed Foreign.FinishOk
            }
        }
    }
    handlers (state, data) {
        read access => resume 42
        store (access, replacement) => {
            let ignored = Foreign.replace_data (state, replacement)
            resume ()
        }
    }
}


initial : Unit -> Int
initial () = 7
