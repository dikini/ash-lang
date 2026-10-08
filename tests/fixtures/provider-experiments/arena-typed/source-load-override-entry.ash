import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
match (Memory.allocate (arena, 41)) {
Memory.Allocated(reference) => {
let value = handle (Memory.load (arena, reference)) with Memory.StorageOps<R, Int> {
allocate_checked ignored => resume (Memory.AllocationRefused Memory.InvalidPayload)
load_checked ignored => resume 99
}
(value, Memory.usage arena)
}
Memory.AllocationRefused(error) => (0, Memory.usage arena)
}
}
