import types (Wrapped)
import forms (syntax accept)

type Measure = Other(Bool)

main : Unit -> Int
main () = accept (Wrapped(0))
