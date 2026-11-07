import types as T
import type_forms (syntax pack)

main : Unit -> Int
main () = {
    let wrong = 0
    match (pack wrong then T.Token(42)) {
        T.Token(value) => value
    }
}
