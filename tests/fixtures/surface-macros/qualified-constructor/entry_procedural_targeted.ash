import procedural_targeted (syntax procedural)

type Fake = Wrap(Int)

unwrap : Int -> Int
unwrap value = value + 100

main : Unit -> Int
main () = procedural 41
