pub syntax bad $name:ident from $value:expr => {
    let result : $name<Missing> = $value
    result
}

main : Unit -> Int
main () = 42
