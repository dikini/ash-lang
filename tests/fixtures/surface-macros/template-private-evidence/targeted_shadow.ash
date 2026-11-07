import targeted_forms (syntax verify)

interface Measure<Key> {
    measure : Key -> Bool
}

main : Unit -> Int
main () = verify 40
