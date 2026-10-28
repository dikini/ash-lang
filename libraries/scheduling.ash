import @builtin.retained_control as Control

pub type Step<N> = Finished(Int)
    | Suspended(Control.Key<N>)

pub type ReadyQueue<N> = Empty
    | Ready(Control.Key<N>, ReadyQueue<N>)

pub enqueue<N> : (ReadyQueue<N>, Control.Key<N>) -> ReadyQueue<N>
enqueue (queue, key) = match queue {
    Empty => Ready(key, Empty)
    Ready(first, rest) => Ready(first, enqueue (rest, key))
}

pub finish<N,E : EffectRow> : (Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N> | E})>, Control.Key<N>) -> Control.Option<Int> ! {Control.Drive<N> | E}
finish (store, key) = match Control.advance_with_drive (store, key) {
    Control.None => Control.None
    Control.Some(step) => match step {
        Finished(value) => Control.Some(value)
        Suspended(next) => finish (store, next)
    }
}

pub drain<N,E : EffectRow> : (Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N> | E})>, Control.Key<N>) -> Unit ! {Control.Drive<N>, Control.Probe<N> | E}
drain (store, key) = {
    let quiet = perform Control.Probe<N>.quiescent ()
    match quiet {
        true => ()
        false => {
            let next = match Control.advance_with_drive (store, key) {
                Control.None => key
                Control.Some(step) => match step {
                    Finished(value) => key
                    Suspended(next) => next
                }
            }
            drain (store, next)
        }
    }
}

pub turn<N,E : EffectRow> : (Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N> | E})>, ReadyQueue<N>) -> ReadyQueue<N> ! {Control.Drive<N> | E}
turn (store, queue) = match queue {
    Empty => Empty
    Ready(key, rest) => match Control.advance_with_drive (store, key) {
        Control.None => rest
        Control.Some(step) => match step {
            Finished(value) => rest
            Suspended(next) => enqueue (rest, next)
        }
    }
}

pub run_ready<N,E : EffectRow> : (Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N> | E})>, ReadyQueue<N>) -> Unit ! {Control.Drive<N>, Control.Probe<N> | E}
run_ready (store, queue) = {
    let quiet = perform Control.Probe<N>.quiescent ()
    match quiet {
        true => ()
        false => run_ready (store, turn (store, queue))
    }
}
