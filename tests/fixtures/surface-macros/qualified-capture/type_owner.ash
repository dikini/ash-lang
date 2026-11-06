import types as T
import decoy as Owner
import type_forms (syntax owner_type)

main : Unit -> Int
main () = match (owner_type Token then T.Token(42)) {
    T.Token(value) => value
}
