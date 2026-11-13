import mixed_forms (syntax emit_repeated)

caller : Unit -> Int
caller () = 42

emit_repeated { identity matching input as Int yields caller(()) }

main : Unit -> Int
main () = identity(0)
