import forms (syntax reject_declaration)

reject_declaration {
    pub answer : Unit -> Int
    answer () = 42
}

main : Unit -> Int
main () = answer(())
