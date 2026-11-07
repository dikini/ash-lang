import types (Wrapped)
import facade_forms (syntax accept)

type Measure = Other(Bool)

main : Unit -> Int
main () = accept (Wrapped(0))
