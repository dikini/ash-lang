pub syntax call $eff:ident in $body:expr => {
    let action : Unit -> Int ! {Missing, $eff} = fn(ignored) {
        $body
    }
    action ()
}

main : Unit -> Int
main () = 42
