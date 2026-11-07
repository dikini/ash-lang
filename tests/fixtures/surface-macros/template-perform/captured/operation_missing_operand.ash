effect Ask {
    ask : Int -> Int
}

pub syntax bad $name:ident from $value:expr => {
    perform Ask.$name missing
}

main : Unit -> Int
main () = 42
