import forms (syntax verify)

interface Check<Key> {
    check : Key -> Bool
}

main : Unit -> Int
main () = verify 40
