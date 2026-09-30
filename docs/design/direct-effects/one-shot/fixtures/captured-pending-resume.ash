effect Inner {
  ping : Unit -> Unit
}

effect Outer {
  pong : Unit -> Unit
}

main : Unit -> Int
main () = handle (handle {
  let ignored = perform Inner.ping ()
  17
} with Inner {
  ping ignored => resume (perform Outer.pong ())
}) with Outer {
  pong ignored => resume ()
}
