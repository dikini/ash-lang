import api (Read, read)
import forms_targeted (syntax measure)

main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    with Read<Token> {
        read (Token(value)) = value + 2
    }
    let owner_read = fn(value) {
        0
    }
    measure Token(40)
}
