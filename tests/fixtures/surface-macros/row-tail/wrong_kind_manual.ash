invoke<T : Type> : (T, Unit -> Int) -> Int
invoke (value, callback) = {
    let action : Unit -> Int ! {| T} = fn(ignored) {
        callback ()
    }
    action ()
}

constant : Unit -> Int
constant () = 42

main : Unit -> Int
main () = invoke ((), constant)
