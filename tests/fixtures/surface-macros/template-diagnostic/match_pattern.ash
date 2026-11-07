import match_forms (syntax branches)
id : Int -> Int
id value = value
main : Unit -> Int
main () = {
    let unused = branches id else fn(true) {
        1
    }
    42
}
