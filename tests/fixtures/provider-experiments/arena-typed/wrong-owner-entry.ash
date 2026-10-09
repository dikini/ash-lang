import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Int>
main () = resource Memory.Arena<A> a = (Memory.ArenaConfig (8, 1)) {
    match (Memory.allocate (a, 41)) {
        Memory.Allocated(reference) => {
            let nested = resource Memory.Arena<B> b = (Memory.ArenaConfig (0, 0)) {
                Memory.load (b, reference)
            }
            0
        }
        Memory.AllocationRefused(error) => 0
    }
}
