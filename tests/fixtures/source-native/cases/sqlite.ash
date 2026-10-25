import @builtin.foreign as F
import sqlite as SQLite

is_present : F.Address -> Bool
is_present address = match F.is_null address {
    true => false
    false => true
}

main : Unit -> (Bool, Bool, Bool, Bool) ! {SQLite.Libversion, SQLite.Sourceid}
main () = {
    let version = perform SQLite.Libversion.call ()
    let sourceid = perform SQLite.Sourceid.call ()
    let version_again = perform SQLite.Libversion.call ()
    let sourceid_again = perform SQLite.Sourceid.call ()
    (is_present version, is_present sourceid, F.equal (version, version_again), F.equal (sourceid, sourceid_again))
}
