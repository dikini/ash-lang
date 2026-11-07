import api as Caller
import forms (syntax send_caller)

main : Unit -> Int
main () = handle (send_caller Caller with 42) with Caller.Ask {
    ask value => resume value
}
