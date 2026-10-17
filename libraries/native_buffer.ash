import @builtin.foreign as Foreign

pub foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Signed = signed(64)
    repr Address = bytes
    const One : Size = 1
    const MinusOne : Signed = -1
    owner State<R> {
        representation Address
        owned R
        teardown Free
    }
    symbol Allocate<R> : Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>> {
        name "calloc"
        abi (Size, Size) -> pointer(Address)
        operand 0 from 0 scalar
        operand 1 from constant One
        output result as owner(State<R>)
        outcome result nonnull { readable result, initialized_bytes result from 0 }
        outcome otherwise { readable result }
    }
    symbol Free<R> : State<R> -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Address)) -> void
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
}

pub type Error = InvalidLength
    | AllocationFailed
    | InvalidIndex
    | InvalidByte
pub type Outcome<T> = Success(T)
    | Failure(Error)
pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)
pub type Finish<S, E> = Consumed
    | ConsumedFailure(E)
    | Retained(S, E)

valid_length : Int -> Bool
valid_length size = match size == 0 {
    true => false
    false => match Foreign.checked_i64 size {
        Foreign.ConversionFailed(_) => false
        Foreign.Returned(_) => true
    }
}

valid_index : (Int, Int) -> Bool
valid_index (size, index) = match Foreign.checked_size_t index {
    Foreign.ConversionFailed(_) => false
    Foreign.Returned(_) => match Foreign.checked_size_t (size + (index * MinusOne) + MinusOne) {
        Foreign.ConversionFailed(_) => false
        Foreign.Returned(_) => true
    }
}

pub interface Provider<Access> {
    length : Access -> Int ! {Ops<Access>}
    read : (Access, Int) -> Outcome<Int> ! {Ops<Access>}
    write : (Access, Int, Int) -> Outcome<Unit> ! {Ops<Access>}
}
pub effect Ops<Access> {
    length : Access -> Int
    read : (Access, Int) -> Outcome<Int>
    write : (Access, Int, Int) -> Outcome<Unit>
}

pub resource Buffer<R> {
    owned R
    input Int
    state State<R>
    data Int
    acquisition Acquire<State<R>, Int, Error>
    completion Finish<State<R>, Unit>
    result Outcome<Answer> for <Answer>
    codec acquired_only
    provider Provider<Buffer<R>>
    effect Ops<Buffer<R>>
    interpret Allocate<R>, Free<R>
    acquire size => match valid_length size {
        false => Refused InvalidLength
        true => match perform Allocate<R>.call size {
            Foreign.Returned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, size)
            Foreign.ConversionFailed(_) => Refused InvalidLength
            _ => Refused AllocationFailed
        }
    }
    finish (state, data) => match perform Free<R>.call state {
        Foreign.Returned(Foreign.Consumed(())) => Consumed
        _ => Retained(state, ())
    }
    handlers (state, data) {
        length access => resume data
        read (access, index) => match Foreign.byte_read (state, index) {
            Foreign.Returned(value) => resume Success value
            Foreign.ConversionFailed(_) => resume Failure InvalidIndex
        }
        write (access, index, byte) => match valid_index (data, index) {
            false => resume Failure InvalidIndex
            true => {
                let success = Success ()
                match Foreign.byte_write (state, index, byte) {
                    Foreign.Returned(()) => resume success
                    Foreign.ConversionFailed(_) => resume Failure InvalidByte
                }
            }
        }
    }
}
