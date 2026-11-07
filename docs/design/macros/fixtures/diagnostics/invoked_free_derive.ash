import free_derive_forms (syntax missing_derive_free)

type Color = Red
deriving (missing_derive_free)

unknown_helper : Unit -> Bool
unknown_helper () = true

main : Unit -> Int
main () = 42
