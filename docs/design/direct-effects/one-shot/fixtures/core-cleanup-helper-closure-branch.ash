import @builtin.cell as Cell

main : Unit -> Unit
main () = resource cell<R> counter = 0 {
    let exercise : Bool -> Unit = fn(choice) {
        let apply : (Unit -> Unit) -> Unit = fn(action) {
            action ()
        }
        let first = apply (fn(ignored) {
            ()
        })
        let second = apply (fn(ignored) {
            let spare = ()
            ()
        })
        let retained = apply (fn(ignored) {
            let held = counter
            ()
        })
        let chosen : Unit -> Unit = match choice {
            true => fn(ignored) {
                ()
            }
            false => fn(ignored) {
                let held = counter
                ()
            }
        }
        apply chosen
    }
    let first = exercise true
    exercise false
}
