effect Read<A> {
    read : Unit -> A
}
main : Unit -> Int
main () = handle (perform Read<Int>.read ()) with Read<Int> {
    read ignored => resume 42
}
