import api as Caller
import forms (syntax unpack_caller)

main : Unit -> Int
main () = unpack_caller Caller in Caller.Boxed(42)
