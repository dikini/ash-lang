import @builtin.foreign as Foreign
import native as Native

main : Unit -> Int ! {Native.Echo<{}, Int, {}>}
main () = match perform Native.Echo<{}, Int, {}>.call 127 {
    Foreign.Returned(value) => value
    Foreign.ConversionFailed(error) => 900
}
