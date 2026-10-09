import @foreign.memory as Native
import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Int>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
    let original : Native.LayoutWitness<Int> = Native.witness ()
    with Native.Layout<Int> {
        witness ignored = original
    }
    match (Memory.allocate (arena, 41)) {
        Memory.Allocated(reference) => Memory.load (arena, reference)
        Memory.AllocationRefused(error) => 0
    }
}
