import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Unit -> Int)>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
    match (Memory.allocate (arena, 41)) {
        Memory.Allocated(reference) => {
            let aggregate = (reference, Memory.load (arena, reference))
            let later : Unit -> Int = fn(ignored) {
                match aggregate {
                    (saved, copied) => {
                        let held = saved
                        copied
                    }
                }
            }
            later
        }
        Memory.AllocationRefused(error) => fn(ignored) {
            0
        }
    }
}
