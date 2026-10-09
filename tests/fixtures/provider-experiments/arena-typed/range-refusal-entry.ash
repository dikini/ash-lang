import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Memory.AllocError, Int, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (16, 2)) {
    match (Memory.allocate (arena, 41)) {
        Memory.Allocated(first) => match (Memory.allocate (arena, 9223372036854775808)) {
            Memory.Allocated(second) => (Memory.OutOfObjects, Memory.load (arena, first), Memory.usage arena)
            Memory.AllocationRefused(error) => (error, Memory.load (arena, first), Memory.usage arena)
        }
        Memory.AllocationRefused(error) => (error, 0, Memory.usage arena)
    }
}
