pub syntax wrap $tail:ident in $body:expr => {
    let action : Unit -> Int ! {| $tail} = fn(ignored) {
        $body
    }
    action ()
}
