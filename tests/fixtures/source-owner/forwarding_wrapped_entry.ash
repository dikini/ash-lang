import owner as Owner

main : Unit -> Owner.Scope<Unit, Unit, (Int, Int)>
main () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {
    let value = Owner.read (Owner.Wrapped(owner))
    let offset = Owner.offset (owner, 5)
    (value, offset)
}
