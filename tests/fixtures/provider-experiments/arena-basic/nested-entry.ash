import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, ((Int, Int, Int, Int), (Int, Int, Int, Int))>>
main () = resource Memory.Arena<R> outer = (Memory.ArenaConfig (64, 4)) {
resource Memory.Arena<S> inner = (Memory.ArenaConfig (16, 2)) {
(Memory.usage outer, Memory.usage inner)
}
}
