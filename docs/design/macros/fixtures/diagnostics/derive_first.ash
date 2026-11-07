import order_forms (syntax fail_derive, syntax fail_declaration)

type Color = Red
    deriving (fail_derive)

fail_declaration

main : Unit -> Int
main () = 42
