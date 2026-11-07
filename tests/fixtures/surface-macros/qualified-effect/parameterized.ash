import api as Caller
import decoy as Owner
import forms (syntax send_typed)

main : Unit -> Int
main () = handle (send_typed Generic with 42) with Caller.Generic<Int> {
    ask value => resume value
}
