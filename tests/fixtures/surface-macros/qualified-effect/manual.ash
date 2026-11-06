import api as Caller

main : Unit -> Int
main () = handle (perform Caller.Ask.ask 42) with Caller.Ask {
    ask value => resume value
}
