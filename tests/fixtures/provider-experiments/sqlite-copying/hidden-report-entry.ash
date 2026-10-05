import sqlite as Sqlite

main : Unit -> Int
main () = {
let ignored = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {
42
}
42
}
