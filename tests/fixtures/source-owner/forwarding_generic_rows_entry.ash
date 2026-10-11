import owner as Owner

effect Tag {
    ping : Unit -> Unit
}

within<Before : EffectRow, R, After : EffectRow> : Owner.Probe<{| Before}, R, {| After}> -> Owner.Scope<Unit, Unit, (Int, Int)>
within outer = resource Owner.Probe<{| Before}, Inner, {| After}> inner = 4 {
    (Owner.read inner, Owner.offset (inner, 5))
}

main : Unit -> Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, (Int, Int)>>
main () = resource Owner.Probe<{Tag}, Outer, {}> outer = 42 {
    within outer
}
