import api as Caller
import forms (syntax row_caller)

main : Unit -> Int
main () = handle (row_caller Caller in (perform Caller.Ask.ask 42)) with Caller.Ask {
    ask value => resume value
}
