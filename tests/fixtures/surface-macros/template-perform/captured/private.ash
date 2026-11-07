import private_forms (syntax request)

effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = request ask from 40
