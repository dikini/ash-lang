import api (Ask as Alias)

main : Unit -> Int
main () = handle (perform Alias.ask 42) with Alias {
    ask value => resume value
}
