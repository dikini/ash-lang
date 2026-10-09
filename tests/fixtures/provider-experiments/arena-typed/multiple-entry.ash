import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, Bool, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (9, 2)) {
    match (Memory.allocate (arena, 41)) {
        Memory.Allocated(integer) => match (Memory.allocate (arena, true)) {
            Memory.Allocated(boolean) => (Memory.load (arena, integer), Memory.load (arena, boolean), Memory.usage arena)
            Memory.AllocationRefused(error) => (0, false, Memory.usage arena)
        }
        Memory.AllocationRefused(error) => (0, false, Memory.usage arena)
    }
}
