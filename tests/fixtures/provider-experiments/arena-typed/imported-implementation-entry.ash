import provider as Provider
import arena as Memory
import scalar_implementation as Library
import scalar_implementation (impl RoundTrip)

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Memory.AllocResult<Int>, (Int, Int, Int, Int))>
main () = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
(Library.round_trip (arena, Library.Input 41), Memory.usage arena)
}
