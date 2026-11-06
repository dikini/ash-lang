pub syntax bad $value:expr => {
    newtype $value = Token(Int)
    42
}

main : Unit -> Int
main () = 42
