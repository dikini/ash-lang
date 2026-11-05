import forms (syntax both)
effect Ask {
    ask : Int -> Int
}
main : Unit -> Int
main () = (handle (both (perform Ask.ask 1) then (perform Ask.ask 2)) with Ask {
    ask value => (resume 0) * 10 + value
}) + 21
