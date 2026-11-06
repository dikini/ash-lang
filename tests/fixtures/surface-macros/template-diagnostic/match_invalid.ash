import match_forms (syntax branches)
main : Unit -> Int
main () = {
    let unused = branches 1 else true
    42
}
