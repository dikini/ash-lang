import forms_targeted (syntax call_targeted)

adjust : Int -> Int
adjust value = value + 100

main : Unit -> Int
main () = {
    let result = call_targeted 41
    let captured = call_targeted (adjust 1)
    match captured == 102 {
        true => result
        false => 0
    }
}
