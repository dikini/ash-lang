import outer (syntax outer)

main : Unit -> Int
main () = {
    let local = 10
    (outer 32) + local
}
