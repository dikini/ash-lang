import provider as Provider
import arena as Memory

main<X> : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Memory.AllocResult<Memory.Ref<X, Int>>>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
    Memory.allocate (arena, 41)
}
