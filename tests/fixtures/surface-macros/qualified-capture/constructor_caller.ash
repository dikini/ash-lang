import types as T
import type_forms (syntax make)

main : Unit -> Int
main () = match (make T with 42) {
    T.Token(value) => value
}
