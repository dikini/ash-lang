pub syntax bad $name:ident from $value:expr => {
    perform $name.ask missing
}

main : Unit -> Int
main () = 42
