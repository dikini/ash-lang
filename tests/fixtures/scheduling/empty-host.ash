import @builtin.retained_control as Control
import @ash.scheduling as Scheduling

main : Unit -> Int
main () = resource Control.Store<N,(Unit -> Scheduling.Step<N> ! {Control.Drive<N>})> store = () {
    let _ = Scheduling.turn (store, Scheduling.Empty)
    42
}
