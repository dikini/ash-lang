import @builtin.cell as Cell
import @builtin.retained_control as Control
import @ash.scheduling as Scheduling

effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}

finish_value<N,E : EffectRow> : (Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N> | E})>, Control.Key<N>) -> Int ! {Control.Drive<N> | E}
finish_value (store, key) = match Scheduling.finish (store, key) {
    Control.None => 0
    Control.Some(value) => value
}

select<N,E : EffectRow> : (Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N> | E})>, Control.Key<N>, Control.Key<N>) -> Int ! {Control.Drive<N>, Control.Probe<N> | E}
select (store, p_key, q_key) = match Control.advance_with_drive (store, p_key) {
    Control.None => {
        let _ = Scheduling.drain (store, q_key)
        0
    }
    Control.Some(step) => match step {
        Scheduling.Finished(value) => {
            let _ = Scheduling.drain (store, q_key)
            value
        }
        Scheduling.Suspended(next) => {
            let _ = Scheduling.finish (store, q_key)
            finish_value (store, next)
        }
    }
}

main : Unit -> (Int, Int)
main () = resource cell<R> events = 0 {
    let answer = resource Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N>, Cell.Ops<R>})> store = () {
        let finished : Scheduling.Step<N> = Scheduling.Finished(42)
        let p = handle {
            cleanup fn(ignored) {
                let _ = Cell.write (events, Cell.read events * 10 + 4)
                let _ = perform Checkpoint<N>.checkpoint ()
                let _ = Cell.write (events, Cell.read events * 10 + 6)
                let _ = perform Checkpoint<N>.checkpoint ()
                Cell.write (events, Cell.read events * 10 + 7)
            } {
                let _ = perform Checkpoint<N>.checkpoint ()
                let _ = Cell.write (events, Cell.read events * 10 + 3)
                finished
            }
        } with Checkpoint<N> using store {
            checkpoint ignored => {
                let key = retain
                let _ = Cell.write (events, Cell.read events * 10 + 1)
                Scheduling.Suspended(key)
            }
        }
        let result = match p {
            Scheduling.Finished(value) => value
            Scheduling.Suspended(p_key) => {
                let q = handle {
                    let _ = perform Checkpoint<N>.checkpoint ()
                    let _ = Cell.write (events, Cell.read events * 10 + 5)
                    Scheduling.Finished(7)
                } with Checkpoint<N> using store {
                    checkpoint ignored => {
                        let key = retain
                        let _ = Cell.write (events, Cell.read events * 10 + 2)
                        Scheduling.Suspended(key)
                    }
                }
                match q {
                    Scheduling.Finished(value) => finish_value (store, p_key)
                    Scheduling.Suspended(q_key) => select (store, p_key, q_key)
                }
            }
        }
        let _ = Scheduling.run_ready (store, Scheduling.Empty)
        result
    }
    let _ = Cell.write (events, Cell.read events * 10 + 8)
    (answer, Cell.read events)
}
