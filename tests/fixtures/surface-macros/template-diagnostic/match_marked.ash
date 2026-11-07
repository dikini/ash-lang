import match_forms (syntax branches)
import match_marked_forms (syntax marked)
main : Unit -> Int
main () = {
    let unused = branches 1 else marked true
    42
}
