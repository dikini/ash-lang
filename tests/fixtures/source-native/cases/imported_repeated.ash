import @builtin.foreign as Foreign
import facade as Native
import helper as Helper

effect Left {
    tick : Unit -> Unit
}
effect Right {
    tick : Unit -> Unit
}

main : Unit -> Int ! {Native.Sample<{Left}, Int, {Right}>, Native.Sample<{Right}, Bool, {Left}>}
main () = match Helper.sample<{Left}, Int, {Right}> 41 {
    Foreign.Returned(first) => match Helper.sample<{Right}, Bool, {Left}> 42 {
        Foreign.Returned(second) => first + second
        Foreign.ConversionFailed(error) => 901
    }
    Foreign.ConversionFailed(error) => 900
}
