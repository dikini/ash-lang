import owner as Owner

probe : Int -> Owner.Outcome<Int>
probe size = resource Owner.Probe<{}, Fresh, {}> owner = size {
    match size == 7 {
        true => handle Owner.read owner with Owner.ProbeOps<Owner.Probe<{}, Fresh, {}>> {
            read ignored => resume 84
        }
        false => Owner.read owner
    }
}

main : Unit -> (
    Owner.Outcome<Int>,
    Owner.Outcome<Int>,
    Owner.Outcome<Int>,
    Owner.Outcome<Int>,
    Owner.Outcome<Owner.Outcome<Int>>,
    Owner.Outcome<Int>,
    Owner.Outcome<Int>
)
main () = {
    let normal = probe 42
    let repeated = probe 8
    let refused = resource Owner.Probe<{}, Refused, {}> owner = 0 {
        let _ = probe 777
        42
    }
    let unpublished = probe 9
    let nested = resource Owner.Probe<{}, Outer, {}> outer = 64 {
        resource Owner.Probe<{}, Inner, {}> inner = 4 {
            Owner.read inner
        }
    }
    let overridden = probe 7
    let conversion_refused = probe ((9223372036854775807 + 1) * 2)
    (normal, repeated, refused, unpublished, nested, overridden, conversion_refused)
}
