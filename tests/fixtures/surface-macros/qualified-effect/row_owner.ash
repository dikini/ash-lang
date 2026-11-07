import api as Caller
import decoy as Owner
import forms (syntax row_owner)

main : Unit -> Int
main () = handle (row_owner Ask in (perform Caller.Ask.ask 42)) with Caller.Ask {
    ask value => resume value
}
