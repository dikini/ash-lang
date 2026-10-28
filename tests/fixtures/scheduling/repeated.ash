import @builtin.cell as Cell
import @builtin.retained_control as Control
import @ash.scheduling as Scheduling

effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}

main : Unit -> Int
main () = resource cell<R> events = 0 {
    let _ = resource Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N>, Cell.Ops<R>})> store = () {
        let step = handle {
            let _ = perform Checkpoint<N>.checkpoint ()
            let _ = Cell.write (events, Cell.read events * 10 + 2)
            let _ = perform Checkpoint<N>.checkpoint ()
            let _ = Cell.write (events, Cell.read events * 10 + 3)
            let _ = perform Checkpoint<N>.checkpoint ()
            let _ = Cell.write (events, Cell.read events * 10 + 4)
            Scheduling.Finished(42)
        } with Checkpoint<N> using store {
            checkpoint ignored => {
                let key = retain
                let _ = Cell.write (events, Cell.read events * 10 + 1)
                Scheduling.Suspended(key)
            }
        }
        match step {
            Scheduling.Finished(value) => ()
            Scheduling.Suspended(key) => Scheduling.drain (store, key)
        }
    }
    let _ = Cell.write (events, Cell.read events * 10 + 5)
    Cell.read events
}
