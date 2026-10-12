import @builtin.foreign as Foreign
import native as Native
import facade as Facade
import helper as Helper

effect Left<T> {
    tick : T -> T
}
effect Right<T> {
    tick : T -> T
}

main : Unit -> (Int, Int, Int, Unit, Int) ! {Native.Echo<{}, Int, {}>, Native.Maximum, Native.Stop, Facade.Sample<{Left<Int>}, Int, {Right<Bool>}>, Facade.Sample<{Right<Bool>}, Bool, {Left<Int>}>}
main () = {
    let sample_left : Int -> Foreign.Call<Int> ! {Facade.Sample<{Left<Int>}, Int, {Right<Bool>}>} = Helper.sample
    let sample_right : Int -> Foreign.Call<Int> ! {Facade.Sample<{Right<Bool>}, Bool, {Left<Int>}>} = Helper.sample
    let success = match perform Native.Echo<{}, Int, {}>.call 127 {
        Foreign.Returned(value) => value
        Foreign.ConversionFailed(error) => 900
    }
    let refusal = match perform Native.Echo<{}, Int, {}>.call 128 {
        Foreign.Returned(value) => value
        Foreign.ConversionFailed(error) => 900
    }
    let maximum = match perform Native.Maximum.call () {
        Foreign.Returned(value) => value
        Foreign.ConversionFailed(error) => 900
    }
    let stopped = match perform Native.Stop.call () {
        Foreign.Returned(value) => value
        Foreign.ConversionFailed(error) => ()
    }
    let repeated = match sample_left 41 {
        Foreign.Returned(first) => match sample_right 42 {
            Foreign.Returned(second) => first + second
            Foreign.ConversionFailed(error) => 901
        }
        Foreign.ConversionFailed(error) => 900
    }
    (success, refusal, maximum, stopped, repeated)
}
