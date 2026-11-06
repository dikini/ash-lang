pub syntax unused $body:expr => {
    let action : Unit -> Int ! {| Missing} = fn(ignored) {
        $body
    }
    action ()
}

main : Unit -> Int
main () = 42
