import match_forms (syntax branches)
main : Unit -> Int
main () = {
    let unused = branches 42 else 0
    42
}
