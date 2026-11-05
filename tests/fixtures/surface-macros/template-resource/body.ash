import @builtin.cell as Cell
import forms (syntax with_body)

main : Unit -> Int
main () = {
    let c = 40
    with_body 2 in c
}
