import @builtin.foreign as F
import @builtin.bytes as B
import native as Raw

pub echo_bytes : Bytes -> F.Address ! {Raw.EchoBytes}
echo_bytes bytes = match B.length bytes == 3 {
    true => perform Raw.EchoBytes.call bytes
    false => F.null ()
}
