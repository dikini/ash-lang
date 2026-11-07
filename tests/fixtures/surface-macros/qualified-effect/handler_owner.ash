import api as Caller
import decoy as Owner
import forms (syntax handle_owner)

main : Unit -> Int
main () = handle_owner Ask in (perform Caller.Ask.ask 42)
