effect Ask {
    ask : Int -> Int
}

pub syntax listen $op:ident for $body:expr => {
    handle $body with Ask {
        missing value => resume value
        $op value => resume value
    }
}

main : Unit -> Int
main () = 42
