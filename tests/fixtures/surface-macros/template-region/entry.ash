import forms (syntax isolate)

type R = Other(Int)

main : Unit -> Int
main () = {
    let owner = 42
    isolate owner
}
