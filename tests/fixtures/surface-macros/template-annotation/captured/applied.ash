import applied_forms (syntax hold)

type Box<A> = Box(A)

main : Unit -> Int
main () = {
    let boxed = hold Box from Box(42)
    match boxed {
        Box(value) => value
    }
}
