import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, Int, Int, Int)>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (0, 0)) {
Memory.usage arena
}
