import arena as Memory
import provider as Provider

main<X> : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Memory.Arena<X>>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (64, 4)) {
arena
}
