import @builtin.bytes as ByteOps
import @builtin.string as TextOps

main : Unit -> (Bool, Int, Int)
main () = {
    let original = "héllo 世界\0"
    let bytes = TextOps.to_utf8 original
    let captured : Unit -> String = fn(ignored) {
        original
    }
    match TextOps.from_utf8 bytes {
        TextOps.Decoded(text) => (TextOps.equal (text, captured ()), TextOps.byte_length text, ByteOps.length bytes)
        TextOps.InvalidUtf8 => (false, 0, 0)
    }
}
