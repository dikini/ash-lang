import owner_generic_forms as Forms

main : Unit -> Int
main () = handle (perform Forms.Ask<Int>.ask 42) with Forms.Ask<Int> {
    ask value => resume value
}
