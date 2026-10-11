import @builtin.foreign as Foreign

pub foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = opaque
    owner ArenaState<R> {
        representation Address
        owned R
        teardown Free
    }
    symbol Allocate<R> : (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<ArenaState<R>>>> {
        name "calloc"
        abi (Size, Size) -> pointer(Address)
        operand 0 from 0 scalar
        operand 1 from 1 scalar
        output result as owner(ArenaState<R>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol Free<R> : ArenaState<R> -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Address)) -> void
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
}

pub type ArenaConfig = ArenaConfig(Int, Int)
pub type ArenaInitError = InvalidConfig
    | AllocationFailed
pub type ArenaFinishError = ReleaseFailed
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

pub interface ArenaProvider<Access> {
    usage : Access -> (Int, Int, Int, Int)
}
pub effect ArenaOps<R> {
    usage : Unit -> (Int, Int, Int, Int)
}
pub resource Arena<R> {
    owned R
    input ArenaConfig
    state ArenaState<R>
    data (Int, Int)
    acquisition Acquire<ArenaState<R>, (Int, Int), ArenaInitError>
    completion Finish<ArenaState<R>, ArenaFinishError>
    result Scope<ArenaInitError, ArenaFinishError, Answer> for <Answer>
    codec scope
    provider ArenaProvider<Arena<R>>
    effect ArenaOps<R>
    interpret Allocate<R>, Free<R>
    acquire ArenaConfig(capacity, slots) => match (
        Foreign.checked_i64 capacity,
        Foreign.checked_size_t capacity,
        Foreign.checked_i64 slots,
        Foreign.checked_size_t slots
    ) {
        (
            Foreign.Returned(_),
            Foreign.Returned(valid_capacity),
            Foreign.Returned(_),
            Foreign.Returned(valid_slots)
        ) => {
            let physical = match valid_capacity == 0 {
                true => 1
                false => valid_capacity
            }
            match perform Allocate<R>.call (physical, 1) {
                Foreign.Returned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, (valid_capacity, valid_slots))
                Foreign.Returned(Foreign.Readable(Foreign.Null)) => Refused AllocationFailed
                Foreign.Returned(Foreign.Unreadable) => Refused AllocationFailed
                Foreign.ConversionFailed(_) => Refused AllocationFailed
            }
        }
        _ => Refused InvalidConfig
    }
    finish (state, data) => match perform Free<R>.call state {
        Foreign.Returned(Foreign.Consumed(())) => Consumed
        Foreign.Returned(Foreign.Retained(())) => Retained(state, ReleaseFailed)
        Foreign.Returned(Foreign.BlockedDependent) => Retained(state, ReleaseFailed)
        Foreign.ConversionFailed(_) => Retained(state, ReleaseFailed)
    }
    handlers (state, (capacity, slots)) {
        usage () => resume (0, capacity, 0, slots)
    }
}
