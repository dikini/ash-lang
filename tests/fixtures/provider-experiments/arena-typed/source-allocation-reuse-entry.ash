import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (16, 2)) {
match (Memory.allocate (arena, 41)) {
Memory.Allocated(first) => {
let result = handle (Memory.allocate (arena, 99)) with Memory.StorageOps<R, Int> {
allocate_checked ignored => resume (Memory.Allocated first)
load_checked ignored => resume 0
}
match result {
Memory.Allocated(reused) => (Memory.load (arena, reused), Memory.usage arena)
Memory.AllocationRefused(error) => (0, Memory.usage arena)
}
}
Memory.AllocationRefused(error) => (0, Memory.usage arena)
}
}
