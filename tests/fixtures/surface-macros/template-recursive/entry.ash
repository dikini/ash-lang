import forms (syntax cycle)

main : Unit -> Int
main () = {
    let first = 40
    cycle (first + 2)
}
