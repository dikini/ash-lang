import api as Caller
import forms (syntax handle_caller)

main : Unit -> Int
main () = handle_caller Caller in (perform Caller.Ask.ask 42)
