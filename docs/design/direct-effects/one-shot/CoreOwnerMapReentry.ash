effect E {
    request : Unit -> Unit
}
main : Unit -> Unit
main () = {
    let f : (Unit -> Unit) -> Unit = fn(k) {
        handle (perform E.request ()) with E {
            request ignored => {
                let called = k ()
                resume ()
            }
        }
    }
    let g : Unit -> Unit = fn(ignored) {
        f (fn(ignoredAgain) {
            ()
        })
    }
    f g
}
