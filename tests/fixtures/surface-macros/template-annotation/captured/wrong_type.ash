import forms (syntax keep)

main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    newtype Other = Other(Int)
    let named = keep Token from Other(42)
    42
}
