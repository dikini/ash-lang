import owner as Owner

main : Unit -> Owner.Scope<Unit, Unit, (Int, Owner.Scope<Unit, Unit, (Int, Int)>, Int)>
main () = resource Owner.Probe<{}, Outer, {}> outer = 64 {
    let before = Owner.read outer
    let child = resource Owner.Probe<{}, Inner, {}> inner = 4 {
        (Owner.read inner, Owner.offset (inner, 3))
    }
    let after = Owner.read outer
    (before, child, after)
}
