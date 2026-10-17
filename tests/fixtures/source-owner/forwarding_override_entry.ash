import owner as Owner
import helpers as Helpers

main : Unit -> Owner.Scope<Unit, Unit, (Int, (Int, Int), Int)>
main () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {
    let before = Owner.read owner
    let overridden = handle (Helpers.relay (owner, 5)) with Owner.ProbeOps<Owner.Probe<{}, Fresh, {}>> {
        read access => resume 84
        offset (access, delta) => resume 105
    }
    let after = Owner.read owner
    (before, overridden, after)
}
