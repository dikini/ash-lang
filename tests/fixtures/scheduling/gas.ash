import @builtin.cell as Cell
import @builtin.retained_control as Control
import @ash.scheduling as Scheduling

effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}

main : Unit -> (Int, Int)
main () = resource cell<F> spent = 0 {
    resource cell<R> events = 0 {
        let answer = resource Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N>, Cell.Ops<F>, Cell.Ops<R>})> store = () {
            let p = handle {
                let first = Cell.read spent + 1
                let _ = Cell.write (spent, first)
                let _ = match first == 2 {
                    true => perform Checkpoint<N>.checkpoint ()
                    false => ()
                }
                let _ = Cell.write (events, Cell.read events * 10 + 1)
                let second = Cell.read spent + 1
                let _ = Cell.write (spent, second)
                let _ = match second == 2 {
                    true => perform Checkpoint<N>.checkpoint ()
                    false => ()
                }
                let _ = Cell.write (events, Cell.read events * 10 + 5)
                Scheduling.Finished(42)
            } with Checkpoint<N> using store {
                checkpoint ignored => {
                    let key = retain
                    let _ = Cell.write (events, Cell.read events * 10 + 2)
                    Scheduling.Suspended(key)
                }
            }
            let result = match p {
                Scheduling.Finished(value) => value
                Scheduling.Suspended(p_key) => {
                    let q = handle {
                        let _ = perform Checkpoint<N>.checkpoint ()
                        let marker = match Cell.read spent == 2 {
                            true => 4
                            false => 9
                        }
                        let _ = Cell.write (events, Cell.read events * 10 + marker)
                        Scheduling.Finished(7)
                    } with Checkpoint<N> using store {
                        checkpoint ignored => {
                            let key = retain
                            let _ = Cell.write (events, Cell.read events * 10 + 3)
                            Scheduling.Suspended(key)
                        }
                    }
                    match q {
                        Scheduling.Finished(value) => {
                            let _ = Scheduling.drain (store, p_key)
                            value
                        }
                        Scheduling.Suspended(q_key) => {
                            let _ = Scheduling.finish (store, q_key)
                            let selected = Scheduling.finish (store, p_key)
                            let _ = Scheduling.drain (store, p_key)
                            match selected {
                                Control.None => 0
                                Control.Some(value) => value
                            }
                        }
                    }
                }
            }
            let _ = Scheduling.run_ready (store, Scheduling.Empty)
            result
        }
        let _ = Cell.write (events, Cell.read events * 10 + 6)
        (answer, Cell.read events)
    }
}
