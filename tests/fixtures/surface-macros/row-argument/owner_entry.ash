import api as Caller
import decoy as Owner
import forms (syntax call_owner)

main : Unit -> Int
main () = handle (call_owner Ask in (perform Caller.Ask.ask 40)) with Caller.Ask {
    ask value => resume (value + 2)
}
