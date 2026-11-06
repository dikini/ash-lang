import api as Caller
import targeted_facade_forms (syntax send)

main : Unit -> Int
main () = handle (send 42) with Caller.Ask {
    ask value => resume value
}
