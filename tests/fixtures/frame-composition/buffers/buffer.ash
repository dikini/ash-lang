import @builtin.generic_cell as Cell
import @builtin.bytes as ByteArray
import @builtin.integer as Integer

pub type Error = InvalidLength
    | InvalidIndex
    | InvalidByte
pub type Outcome<A> = Success(A)
    | Failure(Error)

zeroes : (Int, Int, Bytes) -> Bytes
zeroes (length, index, bytes) = match index == length {
    true => bytes
    false => match ByteArray.append_byte (bytes, 0) {
        ByteArray.BytesAppended(next) => zeroes (length, index + 1, next)
        ByteArray.InvalidByte => bytes
    }
}

pub create : Int -> Outcome<Bytes>
create length = match Integer.split_base256 length {
    Integer.Negative => Failure InvalidLength
    Integer.Parts((quotient, remainder)) => match quotient == 0 {
        false => Failure InvalidLength
        true => match remainder == 0 {
            true => Failure InvalidLength
            false => Success (zeroes (length, 0, ByteArray.empty ()))
        }
    }
}

pub length<R> : Cell.Cell<R, Bytes> -> Int ! {Cell.Ops<R, Bytes>} where Cell.Provider<R, Bytes>
length buffer = ByteArray.length (Cell.read buffer)

pub read<R> : (Cell.Cell<R, Bytes>, Int) -> Outcome<Int> ! {Cell.Ops<R, Bytes>} where Cell.Provider<R, Bytes>
read (buffer, index) = match ByteArray.at (Cell.read buffer, index) {
    ByteArray.ByteAt(value) => Success value
    ByteArray.InvalidIndex => Failure InvalidIndex
}

replace : (Bytes, Int, Int, Int, Bytes) -> Bytes
replace (original, changed_index, value, index, result) = match ByteArray.at (original, index) {
    ByteArray.InvalidIndex => result
    ByteArray.ByteAt(old) => {
        let byte = match index == changed_index {
            true => value
            false => old
        }
        match ByteArray.append_byte (result, byte) {
            ByteArray.BytesAppended(next) => replace (original, changed_index, value, index + 1, next)
            ByteArray.InvalidByte => result
        }
    }
}

pub write<R> : (Cell.Cell<R, Bytes>, Int, Int) -> Outcome<Unit> ! {Cell.Ops<R, Bytes>} where Cell.Provider<R, Bytes>
write (buffer, index, value) = {
    let original = Cell.read buffer
    match ByteArray.at (original, index) {
        ByteArray.InvalidIndex => Failure InvalidIndex
        ByteArray.ByteAt(old) => match ByteArray.append_byte (ByteArray.empty (), value) {
            ByteArray.InvalidByte => Failure InvalidByte
            ByteArray.BytesAppended(checked) => {
                let _ = Cell.write (buffer, replace (original, index, value, 0, ByteArray.empty ()))
                Success ()
            }
        }
    }
}
