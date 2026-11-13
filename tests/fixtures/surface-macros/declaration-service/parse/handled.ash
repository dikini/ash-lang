import forms (syntax parse_handled)

helper : Unit -> Int
helper () = 42

parse_handled {
    answer : Unit -> Int
    answer () = helper(())
}

main : Unit -> Int
main () = answer(())
