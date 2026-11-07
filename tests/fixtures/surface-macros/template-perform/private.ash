import private_forms (syntax local_ask)

effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = {
    let value = 10
    (local_ask 32) + value
}
