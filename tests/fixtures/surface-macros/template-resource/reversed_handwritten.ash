import @builtin.cell as Cell

main : Unit -> Int
main () = {
    let c = 5
    c + (resource cell<R> local_cell = 37 {
        Cell.read local_cell
    })
}
