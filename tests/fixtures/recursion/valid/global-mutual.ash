first : Unit -> Int
first ignored = second ()

fn second(ignored : Unit) -> Int {
    let saved : Unit -> Int = fn(value) {
        first value
    }
    42
}

main : Unit -> Int
main () = first ()
