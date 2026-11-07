import operation_forms as Forms
import operation_forms (syntax request)

main : Unit -> Int
main () = handle (request ask from 40) with Forms.Ask {
    ask value => resume (value + 2)
}
