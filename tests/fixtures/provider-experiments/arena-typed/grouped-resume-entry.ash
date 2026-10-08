import provider as Provider
import arena as Memory

effect Pause {
pause : Unit -> Unit
}

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, Bool)>
main () = handle (resource Memory.Arena<R> arena = (Memory.ArenaConfig (9, 2)) {
match (Memory.allocate (arena, 41)) {
Memory.Allocated(integer) => match (Memory.allocate (arena, true)) {
Memory.Allocated(boolean) => cleanup fn(ignored) {
let final_read = Memory.load (arena, integer)
()
} {
let before = Memory.load (arena, integer)
let ignored = perform Pause.pause ()
(before + (Memory.load (arena, integer)), Memory.load (arena, boolean))
}
Memory.AllocationRefused(error) => (0, false)
}
Memory.AllocationRefused(error) => (0, false)
}
}) with Pause {
pause ignored => resume ()
}
