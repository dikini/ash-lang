import owner as Owner

probe : Int -> Owner.Scope<Unit, Unit, (Int, Int)>
probe size = resource Owner.Probe<{}, Fresh, {}> owner = size {
    (Owner.read owner, Owner.offset (owner, 5))
}

main : Unit -> (
    Owner.Scope<Unit, Unit, (Int, Int)>,
    Owner.Scope<Unit, Unit, (Int, Int)>,
    Owner.Scope<Unit, Unit, (Int, Int)>,
    Owner.Scope<Unit, Unit, (Int, Int)>
)
main () = (probe 42, probe 8, probe 0, probe 9)
