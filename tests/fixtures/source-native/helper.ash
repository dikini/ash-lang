import @builtin.foreign as Foreign
import facade as Native

pub sample<Before : EffectRow, T, After : EffectRow> : Int -> Foreign.Call<Int> ! {Native.Sample<{| Before}, T, {| After}>}
sample value = perform Native.Sample<{| Before}, T, {| After}>.call value
