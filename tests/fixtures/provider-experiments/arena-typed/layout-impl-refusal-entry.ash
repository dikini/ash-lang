import @foreign.memory as Native
import provider as Provider
import arena as Memory

impl Native.Layout<Int> {
    witness ignored = Native.witness ()
}

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Int>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
    match (Memory.allocate (arena, 41)) {
        Memory.Allocated(reference) => Memory.load (arena, reference)
        Memory.AllocationRefused(error) => 0
    }
}
