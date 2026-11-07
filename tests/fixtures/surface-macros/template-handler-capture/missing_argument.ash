pub syntax listen $eff:ident for $body:expr => {
    handle $body with $eff<Missing> {
        ask value => resume value
    }
}

main : Unit -> Int
main () = 42
