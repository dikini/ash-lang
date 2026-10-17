import @builtin.foreign as Foreign

pub foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Status = signed(32)
    const Held : Status = 7
    repr Address = opaque
    owner State<R> {
        representation Address
        owned R
        teardown Free
    }
    symbol Allocate<Before : EffectRow, R, After : EffectRow> : Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>> {
        name "ash_owner_acquire"
        abi (Size) -> pointer(Address)
        operand 0 from 0 scalar
        output result as owner(State<R>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol Free<Before : EffectRow, R, After : EffectRow> : State<R> -> Foreign.Call<Foreign.Disposition<Int>> {
        name "ash_owner_release"
        abi (pointer(Address)) -> Status
        operand 0 from 0 current
        retained_dependents block
        output result as scalar
        outcome result == Held { readable result, retained 0 }
        outcome otherwise { readable result, consumed 0 }
    }
}

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

pub interface ProbeProvider<Access> {
    read : Access -> Int ! {ProbeOps<Access>}
}
pub effect ProbeOps<Access> {
    read : Access -> Int
}
pub resource Probe<Before : EffectRow, R, After : EffectRow> {
    owned R
    input Int
    state State<R>
    data Int
    acquisition Acquire<State<R>, Int, Unit>
    completion Finish<State<R>, Int>
    result Scope<Unit, Int, Answer> for <Answer>
    codec scope
    provider ProbeProvider<Probe<{| Before}, R, {| After}>>
    effect ProbeOps<Probe<{| Before}, R, {| After}>>
    interpret Allocate<{| Before}, R, {| After}>, Free<{| Before}, R, {| After}>
    acquire size => match perform Allocate<{| Before}, R, {| After}>.call size {
        Foreign.Returned(Foreign.Readable(Foreign.NonNull(state))) => match size == 9 {
            true => Refused ()
            false => Acquired(state, size)
        }
        Foreign.Returned(Foreign.Readable(Foreign.Null)) => Refused ()
        Foreign.Returned(Foreign.Unreadable) => Refused ()
        Foreign.ConversionFailed(_) => Refused ()
    }
    finish (state, data) => match perform Free<{| Before}, R, {| After}>.call state {
        Foreign.Returned(Foreign.Consumed(status)) => match status == 0 {
            true => Consumed
            false => ConsumedFailure(status)
        }
        Foreign.Returned(Foreign.Retained(status)) => Retained(state, status)
        Foreign.Returned(Foreign.BlockedDependent) => Retained(state, 1)
        Foreign.ConversionFailed(_) => Retained(state, 1)
    }
    handlers (state, data) {
        read access => resume data
    }
}
