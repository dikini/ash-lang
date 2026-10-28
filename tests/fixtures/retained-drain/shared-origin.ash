import @builtin.generic_cell as Cell
import @builtin.retained_control as Control
effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}
type Step<N> = Done
    | Waiting(Control.Key<N>)
spin : Unit -> Unit
spin () = spin ()
drain<N> : (Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N>})>, Control.Key<N>) -> Unit ! {Control.Drive<N>, Control.Probe<N>}
drain (store, key) = {
    let quiet = perform Control.Probe<N>.quiescent ()
    match quiet {
        true => ()
        false => {
            let _ = Control.advance_with_drive (store, key)
            drain (store, key)
        }
    }
}
main : Unit -> Int
main () = resource Cell.Cell<R,Bool> flag = false {
    resource Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N>})> store = () {
        let step = handle {
            let _ = perform Checkpoint<N>.checkpoint ()
            Done
        } with Checkpoint<N> using store {
            checkpoint ignored => {
                let key = retain
                Waiting(key)
            }
        }
        let _ = match step {
            Done => ()
            Waiting(key) => {
                let old = (match (perform Cell.Ops<R,Bool>.read flag) {
                    true => true
                    false => false
                    }, ())
                let _ = perform Cell.Ops<R,Bool>.write (flag, true)
                let later = (match (perform Cell.Ops<R,Bool>.read flag) {
                    true => true
                    false => false
                    }, ())
                let current = match later {
                    (value, _) => value
                }
                let saved = match old {
                    (value, _) => value
                }
                match current {
                    true => match saved {
                        true => drain (store, key)
                        false => ()
                    }
                    false => spin ()
                }
            }
        }
        42
    }
}
