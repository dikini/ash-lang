import api as Caller
import decoy as Owner
import forms (syntax send_owner)

main : Unit -> Int
main () = handle (send_owner Ask with 42) with Caller.Ask {
    ask value => resume value
}
