import forms (syntax identity_declaration)

identity_declaration {
    pub answer : Unit -> Int
    answer () = 42
}

main : Unit -> Int
main () = answer(())
