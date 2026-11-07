import order_forms (syntax fail_derive, syntax fail_declaration)

fail_declaration

type Color = Red
    deriving (fail_derive)

main : Unit -> Int
main () = 42
