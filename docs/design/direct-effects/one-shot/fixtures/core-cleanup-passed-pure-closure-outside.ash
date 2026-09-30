import @builtin.cell as Cell

effect Invoke {
    run : (Unit -> Unit) -> Unit
}

main : Unit -> Unit
main () = handle {
    resource cell<R> counter = 0 {
        perform Invoke.run (fn(ignored) {
            let retained = counter
            ()
        })
    }
} with Invoke {
    run action => {
        let called = action ()
        resume ()
    }
}
