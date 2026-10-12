import @builtin.foreign as Foreign

pub foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = bytes
    owner State<R> {
        representation Address
        owned R
        teardown Free
    }
    symbol Allocate<Before : EffectRow, R, After : EffectRow> : (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>> {
        name "ash_owner_acquire"
        abi (Size) -> pointer(Address)
        operand 0 from 0 scalar
        output result as owner(State<R>)
        outcome result nonnull { readable result, initialized_bytes result from 1 }
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
    read : (Access, Int) -> Foreign.Call<Int> ! {ProbeOps<Access>}
    write : (Access, Int, Int) -> Foreign.Call<Unit> ! {ProbeOps<Access>}
}
pub effect ProbeOps<Access> {
    write : (Access, Int, Int) -> Foreign.Call<Unit>
    read : (Access, Int) -> Foreign.Call<Int>
}
pub resource Probe<Before : EffectRow, R, After : EffectRow> {
    owned R
    input (Int, Int)
    state State<R>
    data Int
    acquisition Acquire<State<R>, Int, Unit>
    completion Finish<State<R>, Unit>
    result Scope<Unit, Unit, Answer> for <Answer>
    codec scope
    provider ProbeProvider<Probe<{| Before}, R, {| After}>>
    effect ProbeOps<Probe<{| Before}, R, {| After}>>
    interpret Allocate<{| Before}, R, {| After}>, Free<{| Before}, R, {| After}>
    acquire (size, extent) => match perform Allocate<{| Before}, R, {| After}>.call (size, extent) {
        Foreign.Returned(Foreign.Readable(Foreign.NonNull(state))) => match size == 9 {
            true => Refused ()
            false => Acquired(state, size)
        }
        Foreign.Returned(Foreign.Readable(Foreign.Null)) => Refused ()
        Foreign.Returned(Foreign.Unreadable) => Refused ()
        Foreign.ConversionFailed(_) => Refused ()
    }
    finish (state, data) => match perform Free<{| Before}, R, {| After}>.call state {
        Foreign.Returned(Foreign.Consumed(())) => Consumed
        Foreign.Returned(Foreign.Retained(())) => Retained(state, ())
        Foreign.Returned(Foreign.BlockedDependent) => Retained(state, ())
        Foreign.ConversionFailed(_) => Retained(state, ())
    }
    handlers (state, data) {
        read (access, index) => {
            let read_byte = match index == 0 {
                true => Foreign.byte_read
                false => Foreign.byte_read
            }
            resume read_byte (state, index)
        }
        write (access, index, byte) => resume Foreign.byte_write (state, index, byte)
    }
}
