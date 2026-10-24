import @builtin.foreign as Foreign
pub foreign checked library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = opaque
    const One : Size = 1
    assumption Callee "the admitted native owner contract holds"
    owner ArenaState<H, R> {
        representation Address
        owned R
        host H
        teardown Free
    }
    symbol Allocate<H, R> : Int -> Foreign.CheckedCall<Foreign.Output<Foreign.Nullable<ArenaState<H, R>>>> {
        name "calloc"
        abi (Size, Size) -> pointer(Address)
        host H
        assumes { Callee }
        operand 0 from 0 scalar
        operand 1 from constant One
        output result as owner(ArenaState<H, R>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol Free<H, R> : ArenaState<H, R> -> Foreign.CheckedCall<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Address)) -> void
        host H
        assumes { Callee }
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
}

pub type InitError = InvalidSize
    | AllocationRefused
pub type FinishError = ReleaseRefused

pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)

pub interface ArenaProvider<Access> {
    capacity : Access -> Int ! {ArenaOps<Access>}
}
pub effect ArenaOps<Access> {
    capacity : Access -> Int
}
pub resource Arena<H, R> {
    owned R
    host H
    input Int
    state ArenaState<H, R>
    data Int
    acquisition Acquire<ArenaState<H, R>, Int, InitError>
    completion Foreign.CheckedFinish<ArenaState<H, R>, FinishError>
    result Foreign.CheckedScope<Answer, InitError, FinishError> for <Answer>
    codec checked_scope
    provider ArenaProvider<Arena<H, R>>
    effect ArenaOps<Arena<H, R>>
    interpret Allocate<H, R>, Free<H, R>
    acquire size => match Foreign.checked_size_t size {
        Foreign.ConversionFailed(_) => Refused InvalidSize
        Foreign.Returned(valid) => match perform Allocate<H, R>.call (match valid == 0 {
            true => 1
            false => valid
        }) {
            Foreign.CheckedReturned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, size)
            Foreign.CheckedReturned(Foreign.Readable(Foreign.Null)) => Refused AllocationRefused
            Foreign.CheckedReturned(Foreign.Unreadable) => Refused AllocationRefused
            Foreign.CheckedConversionFailed(_) => Refused AllocationRefused
            Foreign.BoundaryFailed(_) => Refused AllocationRefused
        }
    }
    finish (state, data) => {
        let outcome = perform Free<H, R>.call state
        match outcome {
            Foreign.CheckedReturned(Foreign.Consumed(())) => Foreign.FinishedConsumed Foreign.FinishOk
            Foreign.CheckedReturned(Foreign.Retained(())) => Foreign.FinishedRetained(state, ReleaseRefused)
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
        capacity access => resume data
    }
}
