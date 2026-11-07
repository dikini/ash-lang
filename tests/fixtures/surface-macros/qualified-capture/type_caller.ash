import types as T
import type_forms (syntax pack)

main : Unit -> Int
main () = match (pack T then T.Token(42)) {
    T.Token(value) => value
}
