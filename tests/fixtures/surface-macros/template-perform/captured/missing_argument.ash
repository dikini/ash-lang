pub syntax bad $name:ident from $value:expr => {
    perform $name<Missing>.ask $value
}

main : Unit -> Int
main () = 42
