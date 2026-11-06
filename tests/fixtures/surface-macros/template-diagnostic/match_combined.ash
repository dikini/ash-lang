import combined_forms (syntax combined_bad)
main : Unit -> Int
main () = {
    let unused = match true {
        true => combined_bad 0
        false => 1
    }
    42
}
