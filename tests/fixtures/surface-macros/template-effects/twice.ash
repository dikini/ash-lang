import forms (syntax twice)
effect Ask {
    ask : Int -> Int
}
main : Unit -> Int
main () = (handle (twice (perform Ask.ask 1)) with Ask {
    ask value => (resume 0) * 10 + value
}) + 31
