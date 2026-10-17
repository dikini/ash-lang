import @ffi.sqlite as Sqlite

effect Stop {
    stop : Unit -> Unit
}

main : Unit -> Int ! {Sqlite.Initialize}
main () = handle {
    let abandoned = resource Sqlite.Connection<C> db = Sqlite.InMemory {
        resource Sqlite.Statement<S, C> stmt = (db, "SELECT 'héllo 世界', x'00ff'") {
            cleanup fn(ignored) {
                let diagnostic = perform Sqlite.ConnectionOps<C>.diagnostic db
                ()
            } {
                let ignored = perform Stop.stop ()
                let abandoned_row = Sqlite.step stmt
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
