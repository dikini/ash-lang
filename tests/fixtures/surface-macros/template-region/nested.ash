import forms (syntax isolate)

main : Unit -> Int
main () = region<O> outer {
    isolate (using outer {
        42
    })
}
