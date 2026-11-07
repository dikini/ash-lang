import forms (syntax bind)

pub syntax bad $value:expr => {
    bind Token $value
}

main : Unit -> Int
main () = 42
