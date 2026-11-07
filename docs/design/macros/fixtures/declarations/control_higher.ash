pub interface Witness<F : Type -> Type> {
    witness : F<Int> -> Int
}

newtype Box<A> = Box(A)

impl Witness<Box> {
    witness (Box(value)) = value
}

main : Unit -> Int
main () = witness(Box(42))
