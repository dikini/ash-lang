import arena as Memory

main : Unit -> Int
main () = {
let escaped = resource Memory.Arena<R> arena = (Memory.ArenaConfig (8, 1)) {
match (Memory.allocate (arena, 41)) {
Memory.Allocated(reference) => Memory.Allocated (reference, Memory.load (arena, reference))
Memory.AllocationRefused(error) => Memory.AllocationRefused error
}
}
42
}
