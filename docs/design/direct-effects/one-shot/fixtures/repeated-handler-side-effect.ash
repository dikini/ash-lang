effect Pulse {
  tick : Unit -> Unit
}

effect Audit {
  mark : Unit -> Unit
}

main : Unit -> Int
main () = handle (handle {
  let first = perform Pulse.tick ()
  let second = perform Pulse.tick ()
  0
} with Pulse {
  tick ignored => {
    let recorded = perform Audit.mark ()
    resume ()
  }
}) with Audit {
  mark ignored => {
    let result = resume ()
    result + 1
  }
}
