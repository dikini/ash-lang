import forms (syntax escape)

main : Unit -> Int
main () = {
    let leaked : Unit -> Int = escape 0
    leaked ()
}
