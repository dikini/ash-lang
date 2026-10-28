import @builtin.retained_control as Control
import @ash.scheduling as Scheduling

main : Unit -> Int
main () = region<O> outer {
    using outer {
        resource Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N>})> store = () {
            let empty : Scheduling.ReadyQueue<N> = Scheduling.Empty
            let _ = Scheduling.turn (store, empty)
            42
        }
    }
}
