import owner as Owner

main : Unit -> Owner.Scope<Unit, Unit, (Int, Int)>
main () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {
    let first = Owner.read owner
    let second = Owner.offset (owner, 1)
    (first, second)
}
