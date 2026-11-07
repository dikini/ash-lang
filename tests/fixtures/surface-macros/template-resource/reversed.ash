import @builtin.cell as Cell
import forms (syntax hold)

main : Unit -> Int
main () = {
    let c = 5
    c + (hold 37)
}
