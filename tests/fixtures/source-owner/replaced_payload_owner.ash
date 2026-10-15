import @builtin.foreign as Foreign

pub foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
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
    symbol Free<Before : EffectRow, R, After : EffectRow> : State<R> -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "ash_owner_release"
        abi (pointer(Address)) -> void
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
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
    store : (Access, Unit -> Int) -> Unit ! {ProbeOps<Access>}
    read : Access -> Int ! {ProbeOps<Access>}
}
pub effect ProbeOps<Access> {
    store : (Access, Unit -> Int) -> Unit
    read : Access -> Int
}
pub resource Probe<Before : EffectRow, R, After : EffectRow> {
    owned R
    input (Unit -> Int)
    state State<R>
    data (Unit -> Int)
    acquisition Acquire<State<R>, Unit -> Int, Unit>
    completion Finish<State<R>, Unit -> Int>
    result Scope<Unit, Unit -> Int, Answer> for <Answer>
    codec scope
    provider ProbeProvider<Probe<{| Before}, R, {| After}>>
    effect ProbeOps<Probe<{| Before}, R, {| After}>>
    interpret Allocate<{| Before}, R, {| After}>, Free<{| Before}, R, {| After}>
    acquire initial => match perform Allocate<{| Before}, R, {| After}>.call 8 {
        Foreign.Returned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, initial)
        Foreign.Returned(Foreign.Readable(Foreign.Null)) => Refused ()
        Foreign.Returned(Foreign.Unreadable) => Refused ()
        Foreign.ConversionFailed(_) => Refused ()
    }
    finish (state, data) => match perform Free<{| Before}, R, {| After}>.call state {
        Foreign.Returned(Foreign.Consumed(())) => ConsumedFailure data
        Foreign.Returned(Foreign.Retained(())) => Retained(state, data)
        Foreign.Returned(Foreign.BlockedDependent) => Retained(state, data)
        Foreign.ConversionFailed(_) => Retained(state, data)
    }
    handlers (state, data) {
        read access => resume 7
        store (access, replacement) => {
            let _ = Foreign.replace_data (state, replacement)
            resume ()
        }
    }
}
