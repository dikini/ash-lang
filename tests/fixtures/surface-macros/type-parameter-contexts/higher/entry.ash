import forms (syntax emit)
emit Witness method witness
newtype Box<A> = Box(A)
impl Witness<Box> {
    witness (Box(value)) = value
}
main : Unit -> Int
main () = witness(Box(42))
