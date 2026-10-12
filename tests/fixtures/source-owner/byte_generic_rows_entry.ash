import owner as Owner
import @builtin.foreign as Foreign

effect Tag {
    ping : Unit -> Unit
}

within<Before : EffectRow, R, After : EffectRow> : Owner.Probe<{| Before}, R, {| After}> -> Owner.Scope<Unit, Unit, Foreign.Call<Int>>
within outer = resource Owner.Probe<{| Before}, Inner, {| After}> inner = (43, 7) {
    Owner.read (inner, 0)
}

main : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Foreign.Call<Int>>>
main () = resource Owner.Probe<{Tag}, Outer, {}> outer = (42, 7) {
    within outer
}
