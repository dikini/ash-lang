import @builtin.foreign as F
import @builtin.bytes as B
import @builtin.string as T
import native as Raw
import binding as Binding

is_present : F.Address -> Bool
is_present address = match F.is_null address {
    true => false
    false => true
}

main : Unit -> (Bool, Bool, Bool, (Bool, Bool, Bool, Bool, Bool, Bool, Bool)) ! {Raw.Make, Raw.Fail, Raw.Echo, Raw.Release, Raw.EchoBytes}
main () = {
    let normal = Binding.normal ()
    let null_path = Binding.null_path ()
    let body_error = Binding.body_error ()
    let bytes = T.to_utf8 "abc"
    let before = B.equal (bytes, T.to_utf8 "abc")
    let first = Binding.echo_bytes bytes
    let echoed = perform Raw.Echo.call first
    let second = Binding.echo_bytes bytes
    let short = Binding.echo_bytes (T.to_utf8 "ab")
    let wrong = Binding.echo_bytes (T.to_utf8 "abd")
    let after = B.equal (bytes, T.to_utf8 "abc")
    (normal, null_path, body_error, (before, is_present first, F.equal (first, echoed), F.equal (first, second), F.is_null short, F.is_null wrong, after))
}
