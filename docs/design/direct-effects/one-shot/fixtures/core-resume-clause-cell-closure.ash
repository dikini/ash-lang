import @builtin.cell as Cell

effect Ask {
  ask : Unit -> (Unit -> Unit)
}

main : Unit -> Unit
main () = handle ({
  let later = perform Ask.ask ()
  later ()
}) with Ask {
  ask ignored => resource cell<R> c = 41 {
    let callback : Unit -> Unit = fn(ignored) {
      let held = c
      ()
    }
    resume callback
  }
}
