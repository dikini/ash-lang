import @foreign.memory as Native
import provider as Provider
pub import @foreign.memory (ArenaConfig, ArenaInitError, InvalidArenaConfig, ArenaAllocationFailed, ArenaFinishError, ArenaFinishInvariant)

pub import @foreign.memory (Ref, LayoutWitness, AllocResult, Allocated, AllocationRefused, AllocError, OutOfPayload, OutOfObjects, InvalidAlignment, InvalidPayload)

pub effect StorageOps<R, T> {
allocate_checked : (Arena<R>, Native.LayoutWitness<T>, Int, T) -> Native.AllocResult<Native.Ref<R, T>>
load_checked : (Arena<R>, Native.LayoutWitness<T>, Native.Ref<R, T>) -> T
}
pub interface StorageProvider<R, T> {
allocate_checked : (Arena<R>, Native.LayoutWitness<T>, Int, T) -> Native.AllocResult<Native.Ref<R, T>> ! {StorageOps<R, T>}
load_checked : (Arena<R>, Native.LayoutWitness<T>, Native.Ref<R, T>) -> T ! {StorageOps<R, T>}
}

pub allocate<R, T> : (Arena<R>, T) -> Native.AllocResult<Native.Ref<R, T>> ! {StorageOps<R, T>} where StorageProvider<R, T>, Native.Layout<T>
allocate (arena, value) = allocate_checked (arena, Native.witness (), 0, value)

pub allocate_aligned<R, T> : (Arena<R>, Int, T) -> Native.AllocResult<Native.Ref<R, T>> ! {StorageOps<R, T>} where StorageProvider<R, T>, Native.Layout<T>
allocate_aligned (arena, alignment, value) = allocate_checked (arena, Native.witness (), alignment, value)

pub load<R, T> : (Arena<R>, Native.Ref<R, T>) -> T ! {StorageOps<R, T>} where StorageProvider<R, T>, Native.Layout<T>
load (arena, reference) = load_checked (arena, Native.witness (), reference)

pub effect ArenaOps<R> {
usage : Arena<R> -> (Int, Int, Int, Int)
}
pub interface ArenaProvider<R> {
usage : Arena<R> -> (Int, Int, Int, Int) ! {ArenaOps<R>}
}

pub resource Arena<R> {
input Native.ArenaConfig
state Native.ArenaState<R>
result Provider.Scope<Native.ArenaInitError, Native.ArenaFinishError, T> for <T>
provider ArenaProvider<R>
effect ArenaOps<R>
interpret Native.Arena<R>
family<Payload> where Native.Layout<Payload> {
provider StorageProvider<R, Payload>
effect StorageOps<R, Payload>
interpret Native.Storage<R, Payload>
handlers state {
allocate_checked operand => match operand {
(arena, layout, alignment, value) => resume (perform Native.Storage<R, Payload>.store (state, layout, alignment, value))
}
load_checked operand => match operand {
(arena, layout, reference) => resume (perform Native.Storage<R, Payload>.load (state, layout, reference))
}
}
}
acquire config => perform Native.Arena<R>.acquire config
finish state => perform Native.Arena<R>.finish state
handlers state {
usage arena => resume (perform Native.Arena<R>.usage state)
}
}
