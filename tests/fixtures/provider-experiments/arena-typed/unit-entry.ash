import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Unit, Unit, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (0, 2)) {
    match (Memory.allocate (arena, ())) {
        Memory.Allocated(first) => match (Memory.allocate (arena, ())) {
            Memory.Allocated(second) => (Memory.load (arena, first), Memory.load (arena, second), Memory.usage arena)
            Memory.AllocationRefused(error) => ((), (), Memory.usage arena)
        }
        Memory.AllocationRefused(error) => ((), (), Memory.usage arena)
    }
}
