import match_forms (syntax branches)
main : Unit -> Int
main () = {
    let unused = branches true else 1
    42
}
