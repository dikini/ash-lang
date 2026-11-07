import forms (syntax closure)

main : Unit -> Int
main () = {
    let temp = 40
    let f : Int -> Int = closure (temp + 1)
    f 1
}
