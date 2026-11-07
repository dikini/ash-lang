import @builtin.cell as Cell
import forms (syntax typed)

type R = Other(Int)

main : Unit -> Int
main () = typed 42
