import types (WrappedBox)
import decoy as T
import applied_qualified_forms (syntax accept)

main : Unit -> Int
main () = accept (WrappedBox(0))
