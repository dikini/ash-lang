import forms (Read, read, syntax measure)

main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read (Token(value)) = value + 2
    }
    let read = fn(value) {
        0
    }
    measure Token(40)
}
