effect Inner {
    ping : Unit -> Unit
}

effect Local {
    pong : Unit -> Unit
}

main : Unit -> Int
main () = handle {
    let ignored = perform Inner.ping ()
    17
} with Inner {
    ping ignored => handle (resume (perform Local.pong ())) with Local {
        pong ignored => resume ()
    }
}
