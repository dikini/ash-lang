import forms (syntax emit_one)

helper : Unit -> Int
helper () = 42

emit_one {
    answer : Unit -> Int
    answer () = helper(())
}

main : Unit -> Int
main () = answer(())
