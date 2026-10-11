import @builtin.foreign as Foreign
import arena as Memory

foreign library Inputs {
    profile "x86_64-unknown-linux-gnu"
    repr Signed = signed(64)
    symbol NegativeInput : Unit -> Foreign.Call<Int> {
        name "ash_arena_negative_input"
        abi () -> Signed
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol MinimumInput : Unit -> Foreign.Call<Int> {
        name "ash_arena_minimum_input"
        abi () -> Signed
        output result as scalar
        outcome otherwise { readable result }
    }
}

type Observation = Observed(Int, Int, Int, Int)
    | Invalid
    | AllocationRefused
    | CompletionFailed

observe : Memory.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, (Int, Int, Int, Int)> -> Observation
observe result = match result {
    Memory.NotAcquired(Memory.InvalidConfig) => Invalid
    Memory.NotAcquired(Memory.AllocationFailed) => AllocationRefused
    Memory.Completed(usage, Memory.Closed) => Observed usage
    Memory.Completed(_, Memory.ConsumedError(_)) => CompletionFailed
    Memory.Completed(_, Memory.RetainedError(_)) => CompletionFailed
}

usage : Memory.ArenaConfig -> Observation
usage config = observe (resource Memory.Arena<Fresh> arena = config {
    perform Memory.ArenaOps<Fresh>.usage ()
})

unreachable : Unit -> (Int, Int, Int, Int)
unreachable () = unreachable ()

refusal : Memory.ArenaConfig -> Observation
refusal config = observe (resource Memory.Arena<Fresh> arena = config {
    unreachable ()
})

main : Unit -> (
    Observation,
    Observation,
    Observation,
    Observation,
    Observation,
    Observation,
    Observation,
    Observation,
    Observation,
    Observation,
    Observation,
    Memory.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, ((Int, Int, Int, Int), Observation)>
) ! {NegativeInput, MinimumInput}
main () = {
    let negative = match perform NegativeInput.call () {
        Foreign.Returned(value) => value
        Foreign.ConversionFailed(_) => 0
    }
    let minimum = match perform MinimumInput.call () {
        Foreign.Returned(value) => value
        Foreign.ConversionFailed(_) => 0
    }
    let normal = usage (Memory.ArenaConfig (64, 4))
    let zero = usage (Memory.ArenaConfig (0, 0))
    let repeated = usage (Memory.ArenaConfig (64, 4))
    let maximum_slots = usage (Memory.ArenaConfig (1, 9223372036854775807))
    let negative_capacity = refusal (Memory.ArenaConfig (negative, 4))
    let negative_slots = refusal (Memory.ArenaConfig (64, negative))
    let minimum_capacity = refusal (Memory.ArenaConfig (minimum, 4))
    let minimum_slots = refusal (Memory.ArenaConfig (64, minimum))
    let oversized_capacity = refusal (Memory.ArenaConfig ((9223372036854775807 + 1), 4))
    let oversized_slots = refusal (Memory.ArenaConfig (64, (9223372036854775807 + 1)))
    let oversized_size = refusal (Memory.ArenaConfig (((9223372036854775807 + 1) * 2), 4))
    let nested = resource Memory.Arena<Outer> outer = (Memory.ArenaConfig (64, 4)) {
        let outer_usage = perform Memory.ArenaOps<Outer>.usage ()
        let inner_usage = usage (Memory.ArenaConfig (4, 1))
        (outer_usage, inner_usage)
    }
    (
        normal,
        zero,
        repeated,
        maximum_slots,
        negative_capacity,
        negative_slots,
        minimum_capacity,
        minimum_slots,
        oversized_capacity,
        oversized_slots,
        oversized_size,
        nested
    )
}
