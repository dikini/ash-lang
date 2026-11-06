import api as Caller
import decoy as Owner
import forms (syntax send)

main : Unit -> Int
main () = handle (send 42) with Caller.Ask {
    ask value => resume value
}
