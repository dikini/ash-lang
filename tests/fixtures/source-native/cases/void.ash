import @builtin.foreign as Foreign
import native as Native

main : Unit -> Unit ! {Native.Stop}
main () = match perform Native.Stop.call () {
    Foreign.Returned(value) => value
    Foreign.ConversionFailed(error) => ()
}
