import types (WrappedBox)
import applied_forms (syntax accept)

type Package<A> = Other(A)

main : Unit -> Int
main () = accept (WrappedBox(0))
