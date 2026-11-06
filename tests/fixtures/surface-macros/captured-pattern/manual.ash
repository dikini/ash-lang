import api as Caller

main : Unit -> Int
main () = match Caller.Boxed(42) {
    Caller.Boxed(inner) => inner
}
