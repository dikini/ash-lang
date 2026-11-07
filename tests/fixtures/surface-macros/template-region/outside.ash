import forms (syntax isolate)

main : Unit -> Int
main () = {
    let value = isolate 42
    using owner {
        value
    }
}
