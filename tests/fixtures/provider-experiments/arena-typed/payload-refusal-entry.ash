import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Memory.AllocError, Bool, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 2)) {
match (Memory.allocate (arena, true)) {
Memory.Allocated(first) => match (Memory.allocate (arena, 41)) {
Memory.Allocated(second) => (Memory.InvalidPayload, Memory.load (arena, first), Memory.usage arena)
Memory.AllocationRefused(error) => (error, Memory.load (arena, first), Memory.usage arena)
}
Memory.AllocationRefused(error) => (error, false, Memory.usage arena)
}
}
