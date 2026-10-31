import @builtin.cell as Cell
import @buffers.buffer as Buffer
import @builtin.generic_cell as Scoped
import frames as Frames
import decoding as Decoding

write_all<R> : (
    (Scoped.Cell<R, Bytes>, Frames.ByteValues, Int) ->
    Buffer.Outcome<Unit> ! {Scoped.Ops<R, Bytes>}
) where Scoped.Provider<R, Bytes>
write_all (buffer, Frames.End, index) = Buffer.Success ()
write_all (buffer, Frames.Byte(value, rest), index) = {
    match Buffer.write (buffer, index, value) {
        Buffer.Failure(error) => Buffer.Failure error
        Buffer.Success(()) => write_all (buffer, rest, index + 1)
    }
}

read_next<R, C> : (
    (Scoped.Cell<R, Bytes>, Cell.Handle<C>, Int) ->
    Buffer.Outcome<Frames.Next> ! {Scoped.Ops<R, Bytes>, Cell.Ops<C>}
) where Scoped.Provider<R, Bytes>, Cell.Provider<C>
read_next (buffer, position, logical_length) = {
    let index = Cell.read position
    match index == logical_length {
        true => Buffer.Success Frames.EndOfFrame
        false => match Buffer.read (buffer, index) {
            Buffer.Failure(error) => Buffer.Failure error
            Buffer.Success(value) => {
                let ignored = Cell.write (position, index + 1)
                Buffer.Success (Frames.Value value)
            }
        }
    }
}

pub run_frame : (
    Int, Frames.ByteValues
) -> Buffer.Outcome<Buffer.Outcome<Frames.DecodeResult>>
run_frame (capacity, byte_values) = {
    let logical_length = Decoding.byte_count byte_values
    match Buffer.create capacity {
        Buffer.Failure(error) => Buffer.Failure error
        Buffer.Success(initial_bytes) => Buffer.Success (
            resource Scoped.Cell<R, Bytes> buffer = initial_bytes {
                match write_all (buffer, byte_values, 0) {
                    Buffer.Failure(error) => Buffer.Failure error
                    Buffer.Success(()) => resource cell<C> position = 0 {
                        handle (Decoding.decode ()) with Decoding.Cursor {
                            next () => resume (
                                read_next (buffer, position, logical_length)
                            )
                        }
                    }
                }
            }
        )
    }
}
