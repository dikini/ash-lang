import @builtin.foreign as F

pub foreign library Fixture {
    profile "x86_64-unknown-linux-gnu"
    symbol Make : Unit -> F.Address { name "fixture_make" }
}

main : Unit -> Int
main () = 42
