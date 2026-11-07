import invalid_outer (syntax outer)

missing : Unit -> Int
missing () = 42

main : Unit -> Int
main () = outer 1
