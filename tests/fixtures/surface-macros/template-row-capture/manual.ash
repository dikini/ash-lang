effect Ask {
    ask : Int -> Int
}

main : Unit -> Int
main () = handle ({
    let action : Unit -> Int ! {Ask} = fn(ignored) {
        perform Ask.ask 40
    }
    action ()
}) with Ask {
    ask value => resume (value + 2)
}
