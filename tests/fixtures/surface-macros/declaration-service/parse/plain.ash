import forms (syntax parse_plain)

helper : Unit -> Int
helper () = 42

parse_plain {
    answer : Unit -> Int
    answer () = helper(())
}

main : Unit -> Int
main () = answer(())
