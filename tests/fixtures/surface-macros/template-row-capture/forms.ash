pub syntax call $eff:ident in $body:expr => {
    let action : Unit -> Int ! {$eff} = fn(ignored) {
        $body
    }
    action ()
}
