import api as Caller
import targeted_forms (syntax send)

effect Alias {
    ask : Bool -> Bool
}

main : Unit -> Int
main () = handle (send 42) with Caller.Ask {
    ask value => resume value
}
