import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Int>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
match (Memory.allocate_checked (arena, (0, 0), 0, 41)) {
Memory.Allocated(reference) => 1
Memory.AllocationRefused(error) => 0
}
}
