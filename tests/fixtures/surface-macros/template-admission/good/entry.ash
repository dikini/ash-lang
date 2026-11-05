import forms (syntax lookup, syntax through)

main : Unit -> Int
main () = {
    let value = 41
    through (lookup value then 0)
}
