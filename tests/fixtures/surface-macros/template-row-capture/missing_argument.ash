pub syntax call $eff:ident in $body:expr => {
    let action : Unit -> Int ! {$eff<Missing>} = fn(ignored) {
        $body
    }
    action ()
}

main : Unit -> Int
main () = 42
