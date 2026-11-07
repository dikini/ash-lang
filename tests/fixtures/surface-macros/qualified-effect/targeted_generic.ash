import api as Caller
import targeted_forms (syntax send_generic)

main : Unit -> Int
main () = handle (send_generic 42) with Caller.Generic<Int> {
    ask value => resume value
}
