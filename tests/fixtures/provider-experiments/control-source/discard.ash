import sqlite as Sqlite

effect Stop {
    stop : Unit -> Unit
}
main : Unit -> Int
main () = handle {
    let abandoned = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {
        resource Sqlite.Statement<S> stmt = (db, (Sqlite.select_parameter ())) {
            cleanup fn(ignored) {
                let diagnostic = Sqlite.diagnostic db
                ()
            } {
                let ignored = perform Stop.stop ()
                99
            }
        }
    }
    88
} with Stop {
    stop ignored => {
        let ignored = discard
        42
    }
}
