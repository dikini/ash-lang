import forms (syntax keep)

main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    let named = keep Token from Token(42)
    match named {
        Token(value) => value
    }
}
