import macros (syntax bind as with_value)
import acceptance_template_copy (syntax twice_template)
import acceptance_decoy (syntax bump, syntax choose)
import @builtin.cell as Cell

main : Unit -> Int
main () = resource cell<R> c = 3 {
    let total = twice_template (with_value item = 5 when true in {
        let prior = Cell.read c
        let _ = Cell.write (c, prior + 1)
        item + prior
    })
    total + Cell.read c + 14
}
