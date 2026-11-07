pub syntax listen $eff:ident for $body:expr => {
    handle (perform $eff.ask $body) with $eff {
        ask value => resume value
    }
}
