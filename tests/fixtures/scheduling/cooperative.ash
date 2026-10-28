import @builtin.cell as Cell
import @builtin.retained_control as Control
import @ash.scheduling as Scheduling

effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}

main : Unit -> Int
main () = resource cell<R> events = 0 {
    let _ = resource Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N>, Cell.Ops<R>})> store = () {
        let p = handle {
            let _ = perform Checkpoint<N>.checkpoint ()
            let _ = Cell.write (events, Cell.read events * 10 + 3)
            let _ = perform Checkpoint<N>.checkpoint ()
            let _ = Cell.write (events, Cell.read events * 10 + 5)
            Scheduling.Finished(10)
        } with Checkpoint<N> using store {
            checkpoint ignored => {
                let key = retain
                let _ = Cell.write (events, Cell.read events * 10 + 1)
                Scheduling.Suspended(key)
            }
        }
        match p {
            Scheduling.Finished(value) => ()
            Scheduling.Suspended(p_key) => {
                let q = handle {
                    let _ = perform Checkpoint<N>.checkpoint ()
                    let _ = Cell.write (events, Cell.read events * 10 + 4)
                    let _ = perform Checkpoint<N>.checkpoint ()
                    let _ = Cell.write (events, Cell.read events * 10 + 6)
                    Scheduling.Finished(20)
                } with Checkpoint<N> using store {
                    checkpoint ignored => {
                        let key = retain
                        let _ = Cell.write (events, Cell.read events * 10 + 2)
                        Scheduling.Suspended(key)
                    }
                }
                match q {
                    Scheduling.Finished(value) => Scheduling.drain (store, p_key)
                    Scheduling.Suspended(q_key) => {
                        let ready = Scheduling.Ready(p_key, Scheduling.Ready(q_key, Scheduling.Empty))
                        Scheduling.run_ready (store, ready)
                    }
                }
            }
        }
    }
    let _ = Cell.write (events, Cell.read events * 10 + 7)
    Cell.read events
}
