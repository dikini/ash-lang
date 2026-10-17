import @builtin.foreign as Foreign

pub foreign library Counter {
    profile "x86_64-unknown-linux-gnu"
    repr I8 = signed(8)
    repr U64 = unsigned(64)
    symbol Echo<Before : EffectRow, T, After : EffectRow> : Int -> Foreign.Call<Int> {
        name "ash_counter_echo_i8"
        abi (I8) -> I8
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Maximum : Unit -> Foreign.Call<Int> {
        name "ash_counter_max_u64"
        abi () -> U64
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Stop : Unit -> Foreign.Call<Unit> {
        name "ash_counter_void"
        abi () -> void
        outcome otherwise {}
    }
}
