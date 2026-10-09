import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Memory.AllocError, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
    let result = handle (Memory.allocate (arena, 41)) with Memory.StorageOps<R, Int> {
        allocate_checked ignored => resume (Memory.AllocationRefused Memory.InvalidPayload)
        load_checked ignored => resume 0
    }
    match result {
        Memory.AllocationRefused(error) => (error, Memory.usage arena)
        Memory.Allocated(reference) => (Memory.OutOfObjects, Memory.usage arena)
    }
}
