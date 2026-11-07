import @builtin.cell as Cell
import forms (syntax hold)

main : Unit -> Int
main () = {
    let c = 41
    hold (c + 1)
}
