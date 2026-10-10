import @builtin.foreign as Foreign
import native as Native

main : Unit -> Int ! {Native.Maximum}
main () = match perform Native.Maximum.call () {
    Foreign.Returned(value) => value
    Foreign.ConversionFailed(error) => 900
}
