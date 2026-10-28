import @builtin.cell as Cell
import @builtin.retained_control as Control
import @ash.scheduling as Scheduling

effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}

main : Unit -> (Int, Int)
main () = resource cell<R> events = 0 {
    let answer = resource Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N>, Cell.Ops<R>})> store = () {
        let p = handle {
            let _ = perform Checkpoint<N>.checkpoint ()
            let _ = Cell.write (events, Cell.read events * 10 + 3)
            Scheduling.Finished(42)
        } with Checkpoint<N> using store {
            checkpoint ignored => {
                let key = retain
                let _ = Cell.write (events, Cell.read events * 10 + 1)
                Scheduling.Suspended(key)
            }
        }
        match p {
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
                    Scheduling.Finished(ignored) => {
                        let _ = Scheduling.drain (store, p_key)
                        0
                    }
                    Scheduling.Suspended(q_key) => {
                        let selected = Scheduling.finish (store, p_key)
                        let pending = perform Control.Probe<N>.quiescent ()
                        let _ = match pending {
                            true => ()
                            false => Cell.write (events, Cell.read events * 10 + 4)
                        }
                        let _ = Scheduling.drain (store, q_key)
                        match selected {
                            Control.None => 0
                            Control.Some(value) => value
                        }
                    }
                }
            }
        }
    }
    let _ = Cell.write (events, Cell.read events * 10 + 6)
    (answer, Cell.read events)
}
