import @builtin.generic_cell as Scoped
import helper (read_outer)

main : Unit -> Int
main () = resource Scoped.Cell<R, Int> outer = 42 {
    read_outer outer
}
