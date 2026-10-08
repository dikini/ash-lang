import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Int>>
main () = resource Memory.Arena<A> a = (Memory.ArenaConfig (0, 0)) {
resource Memory.Arena<B> b = (Memory.ArenaConfig (8, 1)) {
match (Memory.allocate (b, 41)) {
Memory.Allocated(refB) => {
let result = handle (Memory.allocate (a, refB)) with Memory.StorageOps<A, Memory.Ref<B, Int>> {
allocate_checked ignored => resume (Memory.AllocationRefused Memory.InvalidPayload)
load_checked ignored => resume refB
}
match result {
Memory.AllocationRefused(error) => 1
Memory.Allocated(reference) => 0
}
}
Memory.AllocationRefused(error) => 0
}
}
}
