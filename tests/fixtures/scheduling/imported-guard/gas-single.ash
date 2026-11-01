import @builtin.cell as Cell
import @builtin.retained_control as Control
import @ash.scheduling as Scheduling

effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}

main : Unit -> (Int, Int)
main () = resource cell<F> spent = 0 {
    let answer = resource Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N>, Cell.Ops<F>})> store = () {
        let step = handle {
            let should_yield = Scheduling.gas_guard (spent, 1)
            let _ = match should_yield {
                true => perform Checkpoint<N>.checkpoint ()
                false => ()
            }
            Scheduling.Finished(42)
        } with Checkpoint<N> using store {
            checkpoint ignored => {
                let key = retain
                Scheduling.Suspended(key)
            }
        }
        let result = match step {
            Scheduling.Finished(value) => value
            Scheduling.Suspended(key) => {
                let selected = Scheduling.finish (store, key)
                match selected {
                    Control.None => 0
                    Control.Some(value) => value
                }
            }
        }
        let _ = Scheduling.run_ready (store, Scheduling.Empty)
        result
    }
    (answer, 123456)
}
