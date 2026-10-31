import @buffers.buffer as Buffer
import frames as Frames

pub effect Cursor {
    next : Unit -> Buffer.Outcome<Frames.Next>
}

pub encode : Frames.Message -> Frames.ByteValues
encode Frames.Ping = Frames.Byte(0, Frames.End)
encode (Frames.Reading(value)) = Frames.Byte(1, Frames.Byte(value, Frames.End))
encode (Frames.Pair(first, second)) = Frames.Byte (
    2, Frames.Byte(first, Frames.Byte(second, Frames.End))
)

pub byte_count : Frames.ByteValues -> Int
byte_count Frames.End = 0
byte_count (Frames.Byte(value, rest)) = 1 + byte_count rest

finish : Frames.Message -> Buffer.Outcome<Frames.DecodeResult> ! {Cursor}
finish message = match perform Cursor.next () {
    Buffer.Failure(error) => Buffer.Failure error
    Buffer.Success(Frames.EndOfFrame) => Buffer.Success (Frames.Decoded message)
    Buffer.Success(Frames.Value(extra)) => Buffer.Success Frames.TrailingData
}

decode_reading : Unit -> Buffer.Outcome<Frames.DecodeResult> ! {Cursor}
decode_reading () = match perform Cursor.next () {
    Buffer.Failure(error) => Buffer.Failure error
    Buffer.Success(Frames.EndOfFrame) => Buffer.Success Frames.Truncated
    Buffer.Success(Frames.Value(value)) => finish (Frames.Reading value)
}

decode_pair : Unit -> Buffer.Outcome<Frames.DecodeResult> ! {Cursor}
decode_pair () = match perform Cursor.next () {
    Buffer.Failure(error) => Buffer.Failure error
    Buffer.Success(Frames.EndOfFrame) => Buffer.Success Frames.Truncated
    Buffer.Success(Frames.Value(first)) => match perform Cursor.next () {
        Buffer.Failure(error) => Buffer.Failure error
        Buffer.Success(Frames.EndOfFrame) => Buffer.Success Frames.Truncated
        Buffer.Success(Frames.Value(second)) => finish (Frames.Pair(first, second))
    }
}

decode_tag : Int -> Buffer.Outcome<Frames.DecodeResult> ! {Cursor}
decode_tag tag = match tag == 0 {
    true => finish Frames.Ping
    false => match tag == 1 {
        true => decode_reading ()
        false => match tag == 2 {
            true => decode_pair ()
            false => Buffer.Success Frames.BadTag
        }
    }
}

pub decode : Unit -> Buffer.Outcome<Frames.DecodeResult> ! {Cursor}
decode () = match perform Cursor.next () {
    Buffer.Failure(error) => Buffer.Failure error
    Buffer.Success(Frames.EndOfFrame) => Buffer.Success Frames.Truncated
    Buffer.Success(Frames.Value(tag)) => decode_tag tag
}
