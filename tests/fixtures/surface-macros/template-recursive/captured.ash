import forms (syntax rec_bind)

main : Unit -> Int
main () = {
    let item = 100
    let result = rec_bind item in (item 1)
    match item == 100 {
        true => result
        false => 0
    }
}
