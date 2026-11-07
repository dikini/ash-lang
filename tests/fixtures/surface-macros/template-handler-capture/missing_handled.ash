pub syntax listen $eff:ident for $body:expr => {
    handle missing with $eff {
        ask value => resume value
    }
}

main : Unit -> Int
main () = 42
