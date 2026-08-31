type Ordinary = Ordinary(Ordinary<Int>)

newtype BadRepresentation = BadRepresentation(BadRepresentation<Int>)

newtype Left = Left(Right)
newtype Right = Right(Left)

main : Unit -> Int
main () = true
