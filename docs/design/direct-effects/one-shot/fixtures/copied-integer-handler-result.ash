import @builtin.cell as Cell

effect Number {
  get : Unit -> Int
}

main : Unit -> Int
main () = {
  let later = handle (resource cell<R> c = 41 {
    let copied = perform Number.get ()
    let callback : Unit -> Int = fn(ignored) {
      copied
    }
    callback
  }) with Number {
    get ignored => resume 42
  }
  later ()
}
