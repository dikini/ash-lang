import forms (syntax rec_mixed)

main : Unit -> Int
main () = {
    let item = 100
    let result = rec_mixed item in (item ())
    match item == 100 {
        true => result
        false => 0
    }
}
