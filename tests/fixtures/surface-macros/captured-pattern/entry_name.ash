import api (Boxed)
import forms (syntax unpack_name)

main : Unit -> Int
main () = unpack_name Boxed in Boxed(42)
