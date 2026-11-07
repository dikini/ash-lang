import api (Read, read)
import forms_facade (syntax measure)

main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read (Token(value)) = value + 2
    }
    measure Token(40)
}
