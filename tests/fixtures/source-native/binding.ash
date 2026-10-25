import @builtin.foreign as F
import @builtin.bytes as B
import native as Raw

type Outcome = Success(Bool)
    | Failed(Int)

effect Stop {
    stop : Int -> Unit
}

pub normal : Unit -> Bool ! {Raw.Make, Raw.Echo, Raw.Release}
normal () = {
    let address = perform Raw.Make.call ()
    match F.is_null address {
        true => false
        false => cleanup fn(ignored) {
            perform Raw.Release.call address
        } {
            F.equal (address, perform Raw.Echo.call address)
        }
    }
}

pub null_path : Unit -> Bool ! {Raw.Fail}
null_path () = F.is_null (perform Raw.Fail.call ())

pub body_error : Unit -> Bool ! {Raw.Make, Raw.Release}
body_error () = {
    let address = perform Raw.Make.call ()
    match F.is_null address {
        true => false
        false => {
            let result : Outcome = handle (cleanup fn(ignored) {
                perform Raw.Release.call address
                } {
                let ignored = perform Stop.stop 7
                Success false
            }) with Stop {
                stop primary => {
                    let done = discard
                    Failed primary
                }
            }
            match result {
                Success(value) => false
                Failed(error) => error == 7
            }
        }
    }
}

pub echo_bytes : Bytes -> F.Address ! {Raw.EchoBytes}
echo_bytes bytes = match B.length bytes == 3 {
    true => perform Raw.EchoBytes.call bytes
    false => F.null ()
}
