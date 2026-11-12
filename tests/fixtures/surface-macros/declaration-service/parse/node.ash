import forms (syntax parse_node)

helper : Unit -> Int
helper () = 42

parse_node {
    answer : Unit -> Int
    answer () = helper(())
}

main : Unit -> Int
main () = answer(())
