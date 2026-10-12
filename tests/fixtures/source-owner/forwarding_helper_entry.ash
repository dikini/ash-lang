import owner as Owner
import helpers as Helpers

main : Unit -> Owner.Scope<Unit, Unit, (Int, Int)>
main () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {
    Helpers.relay (owner, 5)
}
