import types (WrappedBox, Wrapped)
import applied_nested_forms (syntax accept)

type Package<A> = Other(A)
type Number = Decoy(Bool)

main : Unit -> Int
main () = accept (WrappedBox(WrappedBox(Wrapped(0))))
