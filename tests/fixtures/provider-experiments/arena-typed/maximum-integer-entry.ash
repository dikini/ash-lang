import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
    match (Memory.allocate (arena, 9223372036854775807)) {
        Memory.Allocated(reference) => (Memory.load (arena, reference), Memory.usage arena)
        Memory.AllocationRefused(error) => (0, Memory.usage arena)
    }
}
