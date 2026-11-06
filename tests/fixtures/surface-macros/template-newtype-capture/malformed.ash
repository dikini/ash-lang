import forms (syntax bind)

pub syntax bad $value:expr => {
    let value =
    $value
}

main : Unit -> Int
main () = bind token in 42
