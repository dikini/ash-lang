import forms (syntax bind_function)

main : Unit -> Int
main () = {
    let item = 100
    let f : Int -> Int = bind_function item in (item + 1)
    match item == 100 {
        true => f 41
        false => 0
    }
}
