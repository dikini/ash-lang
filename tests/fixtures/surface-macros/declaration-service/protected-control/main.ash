import mixed_forms (syntax parse_protected)

caller : Unit -> Int
caller () = 42

parse_protected identity matching input as Int yields caller(())

main : Unit -> Int
main () = identity(0)
