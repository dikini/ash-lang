import owner_generic_forms as Forms
import owner_generic_forms (syntax send)

main : Unit -> Int
main () = handle (send 42) with Forms.Ask<Int> {
    ask value => resume value
}
