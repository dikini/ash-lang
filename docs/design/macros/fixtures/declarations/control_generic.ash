pub type Maybe<A> = Present(A)
    | Absent

pub newtype Box<A> = Box(A)

main : Unit -> Int
main () = match Box(Present(42)) {
    Box(Present(value)) => value
    Box(Absent) => 0
}
