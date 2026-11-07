import forms (syntax hold)

newtype Token = Token(Bool)

main : Unit -> Int
main () = hold ({
    let caller : Token = Token(true)
    match caller {
        Token(flag) => match flag {
            true => 41
            false => 0
        }
    }
})
