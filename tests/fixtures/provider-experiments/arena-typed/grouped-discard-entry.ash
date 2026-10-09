import @builtin.cell as Cell
import arena as Memory

effect Stop {
    stop : Unit -> Unit
}

cleanup_value : (Bool, Int) -> Int
cleanup_value (enabled, value) = match enabled {
    true => value
    false => 0
}

main : Unit -> (Int, Int)
main () = resource cell<O> trace = 0 {
    let result = handle {
        let abandoned = resource Memory.Arena<R> arena = (Memory.ArenaConfig (9, 2)) {
            match (Memory.allocate (arena, 41)) {
                Memory.Allocated(integer) => match (Memory.allocate (arena, true)) {
                    Memory.Allocated(boolean) => cleanup fn(ignored) {
                        let value = Memory.load (arena, integer)
                        let enabled = Memory.load (arena, boolean)
                        Cell.write (trace, cleanup_value (enabled, value))
                    } {
                        let ignored = perform Stop.stop ()
                        let unreachable_read = Memory.load (arena, integer)
                        99
                    }
                    Memory.AllocationRefused(error) => 0
                }
                Memory.AllocationRefused(error) => 0
            }
        }
        88
    } with Stop {
        stop ignored => {
            let ignored = discard
            42
        }
    }
    (result, Cell.read trace)
}
