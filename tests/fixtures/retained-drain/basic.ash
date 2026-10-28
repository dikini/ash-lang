import @builtin.retained_control as Control
effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}
type Step<N> = Done
    | Waiting(Control.Key<N>)
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
main () = resource Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N>})> store = () {
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
        Waiting(key) => drain (store, key)
    }
    42
}
