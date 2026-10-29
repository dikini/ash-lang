pub foreign library Fixture {
    profile "x86_64-unknown-linux-gnu"
    symbol EchoBytes : Bytes -> Unit { name "fixture_network_bytes" }
}
