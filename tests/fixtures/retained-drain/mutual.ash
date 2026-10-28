import @builtin.retained_control as Control
effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}
type Step<N> = Done
    | Waiting(Control.Key<N>)
drain<N> : (Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N>})>, Control.Key<N>, Control.Key<N>) -> Unit ! {Control.Drive<N>, Control.Probe<N>}
drain (store, first, second) = {
    let quiet = perform Control.Probe<N>.quiescent ()
    match quiet {
        true => ()
        false => {
            let _ = Control.advance_with_drive (store, first)
            again (store, first, second)
        }
    }
}
again<N> : (Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N>})>, Control.Key<N>, Control.Key<N>) -> Unit ! {Control.Drive<N>, Control.Probe<N>}
again (store, first, second) = {
    let quiet = perform Control.Probe<N>.quiescent ()
    match quiet {
        true => ()
        false => {
            let _ = Control.advance_with_drive (store, second)
            drain (store, first, second)
        }
    }
}
main : Unit -> Int
main () = resource Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N>})> store = () {
    let p = handle {
        let _ = perform Checkpoint<N>.checkpoint ()
        Done
    } with Checkpoint<N> using store {
        checkpoint ignored => {
            let key = retain
            Waiting(key)
        }
    }
    let _ = match p {
        Done => ()
        Waiting(first) => {
            let q = handle {
                let _ = perform Checkpoint<N>.checkpoint ()
                Done
            } with Checkpoint<N> using store {
                checkpoint ignored => {
                    let key = retain
                    Waiting(key)
                }
            }
            match q {
                Done => ()
                Waiting(second) => drain (store, first, second)
            }
        }
    }
    42
}
