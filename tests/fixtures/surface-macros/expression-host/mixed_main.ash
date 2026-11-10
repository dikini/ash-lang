import mixed_forms (syntax emit_mixed)

value : Unit -> Int
value () = 0

emit_mixed identity matching value as Int yields value

main : Unit -> Int
main () = identity(42)
