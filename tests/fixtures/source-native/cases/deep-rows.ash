import @builtin.foreign as F
import @builtin.bytes as B
import @builtin.string as T
import native as Raw

effect Nest<Rows : EffectRow> {
    tick : Unit -> Unit
}
effect Deep<Rows : EffectRow> {
    tick : Unit -> Unit
}

is_present : F.Address -> Bool
is_present address = match F.is_null address {
    true => false
    false => true
}

main : Unit -> (Bool, Bool, Bool, Bool, Bool, Bool, Bool, Unit, Bool) ! {Raw.Make, Raw.Fail, Raw.Echo, Raw.Pair, Raw.Release, Raw.EchoBytes}
main () = {
    let ignored = handle (perform Deep<DEEP_ROW>.tick ()) with Deep<DEEP_ROW> {
        tick ignored => resume ()
    }
    let address = perform Raw.Make.call ()
    let nonnull = is_present address
    let echoed = perform Raw.Echo.call address
    let bytes = T.to_utf8 "abc"
    let before = B.equal (bytes, T.to_utf8 "abc")
    let paired = perform Raw.Pair.call (address, bytes)
    let first = perform Raw.EchoBytes.call bytes
    let second = perform Raw.EchoBytes.call bytes
    let after = B.equal (bytes, T.to_utf8 "abc")
    let released = perform Raw.Release.call address
    let failed = perform Raw.Fail.call ()
    (nonnull, F.equal (address, echoed), F.equal (address, paired), before, is_present first, F.equal (first, second), after, released, F.is_null failed)
}
