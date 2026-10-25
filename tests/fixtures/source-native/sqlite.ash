import @builtin.foreign as F

pub foreign library SQLite {
    profile "x86_64-unknown-linux-gnu"
    symbol Libversion : Unit -> F.Address { name "sqlite3_libversion" }
    symbol Sourceid : Unit -> F.Address { name "sqlite3_sourceid" }
}
