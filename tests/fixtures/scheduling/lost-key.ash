import @builtin.retained_control as Control
import @ash.scheduling as Scheduling

effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}

main : Unit -> Int
main () = region<O> outer {
    using outer {
        resource Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N>})> store = () {
            let step = handle {
                let _ = perform Checkpoint<N>.checkpoint ()
                Scheduling.Finished(42)
            } with Checkpoint<N> using store {
                checkpoint ignored => {
                    let key = retain
                    Scheduling.Suspended(key)
                }
            }
            match step {
                Scheduling.Finished(value) => value
                Scheduling.Suspended(key) => {
                    let ready = Scheduling.Ready(key, Scheduling.Empty)
                    let remaining = match ready {
                        Scheduling.Empty => Scheduling.Empty
                        Scheduling.Ready(ignored, rest) => rest
                    }
                    let _ = remaining
                    42
                }
            }
        }
    }
}
