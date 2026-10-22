import @builtin.foreign as Foreign
foreign checked library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = bytes
    assumption Callee "the admitted native owner, initialized interval and view contracts hold"
    owner State<H, R> {
        representation Address
        owned R
        host H
        teardown Free
    }
    symbol Allocate<H, R> : (Int, Int) -> Foreign.CheckedCall<Foreign.Output<Foreign.Nullable<State<H, R>>>> {
        name "malloc"
        abi (Size) -> pointer(Address)
        host H
        assumes { Callee }
        operand 0 from 0 scalar
        output result as owner(State<H, R>)
        outcome result nonnull { readable result, initialized_bytes result from 1 }
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
    access ByteView<W, H, R> {
        window W
        owner State<H, R>
        extent bytes
        preserves QueryBytes, ByteLength
    }
    symbol QueryBytes<W, H, R> : (State<H, R>, Int) -> Foreign.CheckedCall<Foreign.Output<Foreign.Nullable<ByteView<W, H, R>>>> {
        name "ash_byte_view"
        abi (pointer(Address), Size) -> pointer(Address)
        host H
        assumes { Callee }
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as view(ByteView<W, H, R>, 1)
        outcome otherwise { readable result }
    }
    symbol ByteLength<W, H, R> : (State<H, R>, Int, ByteView<W, H, R>) -> Foreign.CheckedCall<Foreign.Extent<ByteView<W, H, R>>> {
        name "ash_byte_length"
        abi (pointer(Address), Size) -> Size
        host H
        assumes { Callee }
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as extent_of(2, 1)
        outcome otherwise { readable result }
    }
    access NulView<W, H, R> {
        window W
        owner State<H, R>
        extent nul
        preserves QueryNul
    }
    symbol QueryNul<W, H, R> : (State<H, R>, Int) -> Foreign.CheckedCall<Foreign.Output<Foreign.Nullable<NulView<W, H, R>>>> {
        name "ash_nul_view"
        abi (pointer(Address), Size) -> pointer(Address)
        host H
        assumes { Callee }
        operand 0 from 0 current
        operand 1 from 1 scalar
        output result as view(NulView<W, H, R>, 1)
        outcome otherwise { readable result }
    }
}

pub type Acquire<S, D, I> = Acquired(S, D)
    | Refused(I)
pub type CopyProbe = Copied(Foreign.CheckedCall<Bytes>)
    | NoView

effect Trace {
    note : Unit -> Unit
}
interface ProbeProvider<Access> {
    read : (Access, Int) -> Foreign.CheckedCall<Int> ! {ProbeOps<Access>}
    write : (Access, Int, Int) -> Foreign.CheckedCall<Unit> ! {ProbeOps<Access>}
    copy_bytes : (Access, Int) -> CopyProbe ! {ProbeOps<Access>}
    copy_nul : (Access, Int, Int) -> CopyProbe ! {ProbeOps<Access>}
}
effect ProbeOps<Access> {
    read : (Access, Int) -> Foreign.CheckedCall<Int>
    write : (Access, Int, Int) -> Foreign.CheckedCall<Unit>
    copy_bytes : (Access, Int) -> CopyProbe
    copy_nul : (Access, Int, Int) -> CopyProbe
}
resource Probe<H, R> {
    owned R
    host H
    input (Int, Int)
    state State<H, R>
    data Unit
    acquisition Acquire<State<H, R>, Unit, Unit>
    completion Foreign.CheckedFinish<State<H, R>, Unit>
    result Foreign.CheckedScope<Answer, Unit, Unit> for <Answer>
    codec checked_scope
    provider ProbeProvider<Probe<H, R>>
    effect ProbeOps<Probe<H, R>>
    interpret Allocate<H, R>, Free<H, R>
    acquire input => match perform Allocate<H, R>.call input {
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
        read (access, index) => {
            let action : (State<H, R>, Int) -> Foreign.CheckedCall<Int> ! {Foreign.NativeHost<H>} = Foreign.checked_byte_read
            resume action (state, index)
        }
        write (access, index, byte) => {
            let action : (State<H, R>, Int, Int) -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_byte_write
            resume action (state, index, byte)
        }
        copy_bytes (access, key) => {
            let copied = copy_window ByteView<W, H, R> from state {
                match perform QueryBytes<W, H, R>.call (state, key) {
                    Foreign.CheckedReturned(Foreign.Readable(Foreign.NonNull(view))) => match perform ByteLength<W, H, R>.call (state, key, view) {
                        Foreign.CheckedReturned(extent) => {
                            let action : (ByteView<W, H, R>, Foreign.Extent<ByteView<W, H, R>>) -> Foreign.CheckedCall<Bytes> ! {Foreign.NativeHost<H>} = Foreign.checked_copy_bytes
                            Copied (action (view, extent))
                        }
                        Foreign.CheckedConversionFailed(error) => Copied (Foreign.CheckedConversionFailed error)
                        Foreign.BoundaryFailed(reason) => Copied (Foreign.BoundaryFailed reason)
                    }
                    Foreign.CheckedReturned(_) => NoView
                    Foreign.CheckedConversionFailed(error) => Copied (Foreign.CheckedConversionFailed error)
                    Foreign.BoundaryFailed(reason) => Copied (Foreign.BoundaryFailed reason)
                }
            }
            resume copied
        }
        copy_nul (access, key, bound) => {
            let copied = copy_window NulView<W, H, R> from state {
                match perform QueryNul<W, H, R>.call (state, key) {
                    Foreign.CheckedReturned(Foreign.Readable(Foreign.NonNull(view))) => {
                        let action : (NulView<W, H, R>, Int) -> Foreign.CheckedCall<Bytes> ! {Foreign.NativeHost<H>} = Foreign.checked_copy_nul
                        Copied (action (view, bound))
                    }
                    Foreign.CheckedReturned(_) => NoView
                    Foreign.CheckedConversionFailed(error) => Copied (Foreign.CheckedConversionFailed error)
                    Foreign.BoundaryFailed(reason) => Copied (Foreign.BoundaryFailed reason)
                }
            }
            resume copied
        }
    }
}

pub run : Unit -> Foreign.CheckedScope<(Foreign.CheckedCall<Int>, Foreign.CheckedCall<Unit>, CopyProbe, CopyProbe), Unit, Unit>
run () = handle (foreign host H {
    resource Probe<H, R> owner = (8, 8) {
        let written = write (owner, 0, 7)
        let value = read (owner, 0)
        let bytes = copy_bytes (owner, 0)
        let nul = copy_nul (owner, 0, 8)
        (value, written, bytes, nul)
    }
}) with Trace {
    note ignored => resume ()
}
