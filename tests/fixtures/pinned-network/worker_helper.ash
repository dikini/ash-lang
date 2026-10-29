import network_native as Native

pub process : Bytes -> Unit ! {Native.EchoBytes}
process message = {
    let _ = perform Native.EchoBytes.call message
    ()
}
