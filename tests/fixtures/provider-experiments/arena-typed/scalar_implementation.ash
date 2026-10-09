import @foreign.memory as Native
import arena as Memory

pub type Input<T> = Input(T)

pub interface RoundTrip<R, Args> {
    round_trip : (Memory.Arena<R>, Args) -> Native.AllocResult<Int> ! {Memory.StorageOps<R, Int>}
}

pub impl<R> RoundTrip<R, Input<Int>> where Memory.StorageProvider<R, Int>, Native.Layout<Int> {
    round_trip (arena, Input(value)) = match (Memory.allocate (arena, value)) {
        Native.Allocated(reference) => Native.Allocated (Memory.load (arena, reference))
        Native.AllocationRefused(error) => Native.AllocationRefused error
    }
}
