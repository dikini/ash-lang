import procedural_targeted (syntax call_procedural)

adjust : Int -> Int
adjust value = value + 100

main : Unit -> Int
main () = {
    let result = call_procedural 41
    let captured = call_procedural (adjust 1)
    match captured == 102 {
        true => result
        false => 0
    }
}
