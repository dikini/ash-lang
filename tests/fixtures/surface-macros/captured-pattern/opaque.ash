import api as Caller
import forms (syntax unpack)

main : Unit -> Int
main () = unpack Hidden in Caller.Boxed(42)
