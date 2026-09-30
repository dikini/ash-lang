effect Invoke {
    run : (Unit -> Unit) -> Unit
}

main : Unit -> Unit
main () = handle {
    let first = perform Invoke.run (fn(ignored) {
        ()
    })
    perform Invoke.run (fn(ignored) {
        let spare = ()
        ()
    })
} with Invoke {
    run action => {
        let called = action ()
        resume ()
    }
}
