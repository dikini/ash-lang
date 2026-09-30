import @builtin.cell as Cell

main : Unit -> Int
main () = {
  let later = resource cell<R> c = 41 {
    let copied = Cell.read c
    let callback : Unit -> Int = fn(ignored) {
      copied
    }
    callback
  }
  later ()
}
