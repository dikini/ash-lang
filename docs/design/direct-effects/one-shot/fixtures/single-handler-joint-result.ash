effect Number {
  get : Unit -> Int
}

main : Unit -> Int
main () = handle (perform Number.get ()) with Number {
  get ignored => resume 17
}
