import api as Caller
import decoy as Owner
import forms (syntax send_both)

main : Unit -> Int
main () = handle (send_both Ask with ask in 42) with Caller.Ask {
    ask value => resume value
}
