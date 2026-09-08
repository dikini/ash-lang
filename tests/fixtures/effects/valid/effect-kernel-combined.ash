effect Read<A> {
    read : Unit -> A
}

relay<R : EffectRow, A> : (Unit -> A ! { | R }) -> A ! { | R }
relay action = action ()

read_number : Unit -> Int ! {Read<Int>}
read_number () = perform Read<Int>.read ()

combined : Unit -> Int ! {Read<Int>, Read<Bool>}
combined () = {
    let number = relay(read_number)
    let ignored = perform Read<Bool>.read ()
    number
}

main : Unit -> Int
main () = handle (
    handle (combined ()) with Read<Bool> {
        read ignored => resume true
    }
) with Read<Int> {
    read ignored => resume 42
}
