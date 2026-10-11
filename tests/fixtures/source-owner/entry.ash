import owner as Owner

probe : Int -> Owner.Scope<Unit, Unit, Int>
probe size = resource Owner.Probe<{}, Fresh, {}> owner = size {
    match size == 7 {
        true => handle perform Owner.ProbeOps<Fresh>.read () with Owner.ProbeOps<Fresh> {
            read () => resume 84
        }
        false => perform Owner.ProbeOps<Fresh>.read ()
    }
}

main : Unit -> (
    Owner.Scope<Unit, Unit, Int>,
    Owner.Scope<Unit, Unit, Int>,
    Owner.Scope<Unit, Unit, Int>,
    Owner.Scope<Unit, Unit, Int>,
    Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, Int>>,
    Owner.Scope<Unit, Unit, Int>,
    Owner.Scope<Unit, Unit, Int>
)
main () = {
    let normal = probe 42
    let repeated = probe 8
    let refused = probe 0
    let unpublished = probe 9
    let nested = resource Owner.Probe<{}, Outer, {}> outer = 64 {
        resource Owner.Probe<{}, Inner, {}> inner = 4 {
            perform Owner.ProbeOps<Inner>.read ()
        }
    }
    let overridden = probe 7
    let conversion_refused = probe ((9223372036854775807 + 1) * 2)
    (normal, repeated, refused, unpublished, nested, overridden, conversion_refused)
}
