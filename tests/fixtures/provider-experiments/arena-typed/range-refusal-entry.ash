import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Memory.AllocError, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
match (Memory.allocate (arena, 9223372036854775808)) {
Memory.Allocated(reference) => (Memory.OutOfObjects, Memory.usage arena)
Memory.AllocationRefused(error) => (error, Memory.usage arena)
}
}
