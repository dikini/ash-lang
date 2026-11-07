pub syntax listen $eff:ident for $body:expr => {
    handle $body with $eff using missing {
        ask value => resume value
    }
}

main : Unit -> Int
main () = 42
