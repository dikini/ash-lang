import @builtin.foreign as F

pub foreign library Fixture {
    profile "x86_64-unknown-linux-gnu"
    symbol Make : Unit -> F.Address { name "fixture_make" }
    symbol Fail : Unit -> F.Address { name "fixture_fail" }
    symbol Echo : F.Address -> F.Address { name "fixture_echo" }
    symbol Release : F.Address -> Unit { name "fixture_release" }
    symbol Pair : (F.Address, Bytes) -> F.Address { name "fixture_pair" }
    symbol EchoBytes : Bytes -> F.Address { name "fixture_echo_bytes" }
}
