import provider as Provider
import arena as Memory

main : Unit -> (Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, Int, Int, Int)>, Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, Int, Int, Int)>)
main () = (session (), session ())

session : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, Int, Int, Int)>
session () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (64, 4)) {
    Memory.usage arena
}
