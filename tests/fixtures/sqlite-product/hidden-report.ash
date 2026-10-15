import @ffi.sqlite as Sqlite

main : Unit -> Int ! {Sqlite.Initialize}
main () = {
    let ignored = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {
        42
    }
    42
}
