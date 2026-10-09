import @foreign.memory as Native
import provider as Provider
pub import @foreign.memory (ArenaConfig, ArenaInitError, InvalidArenaConfig, ArenaAllocationFailed, ArenaFinishError, ArenaFinishInvariant)

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
    acquire config => perform Native.Arena<R>.acquire config
    finish state => perform Native.Arena<R>.finish state
    handlers state {
        usage arena => resume (perform Native.Arena<R>.usage state)
    }
}
