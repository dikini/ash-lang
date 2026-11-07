import types as T
import decoy as Owner
import type_forms (syntax create)

main : Unit -> Int
main () = match (create Token with 42) {
    T.Token(value) => value
}
