import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Unit, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (64, 2)) {
    match (Memory.allocate (arena, true)) {
        Memory.Allocated(first) => match (Memory.allocate_aligned (arena, 64, ())) {
            Memory.Allocated(second) => (Memory.load (arena, second), Memory.usage arena)
            Memory.AllocationRefused(error) => ((), Memory.usage arena)
        }
        Memory.AllocationRefused(error) => ((), Memory.usage arena)
    }
}
