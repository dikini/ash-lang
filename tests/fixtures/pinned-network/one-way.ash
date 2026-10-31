import @builtin.network as Network
import @builtin.bytes as ByteOps
import @builtin.retained_control as Control
import network_native as Native
import worker_helper as Helper

effect Checkpoint<S> {
    checkpoint : Unit -> Unit
}

receive_all<N> : Network.Worker<N> -> Bool ! {Network.IO<N>, Native.EchoBytes}
receive_all worker = match Network.try_receive worker {
    Network.Message(Network.Application, message) => {
        let _ = Helper.process message
        let _ = resource Control.Store<S,(Unit -> Unit ! {Control.Drive<S>})> store = () {
            handle {
                let _ = perform Checkpoint<S>.checkpoint ()
                ()
            } with Checkpoint<S> using store {
                checkpoint ignored => resume ()
            }
        }
        receive_all worker
    }
    Network.Message(Network.Control, _) => false
    Network.Empty => receive_all worker
    Network.End => true
    Network.ReceiveFailed(_) => false
}

consume<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>, Native.EchoBytes}
consume (worker, _) = {
    let _ = Network.finish_send worker
    match receive_all worker {
        true => {
            let _ = Network.finish_receive worker
            ()
        }
        false => ()
    }
}

await_end<N> : Network.Worker<N> -> Bool ! {Network.IO<N>}
await_end worker = match Network.try_receive worker {
    Network.Empty => await_end worker
    Network.End => true
    Network.Message(_, _) => false
    Network.ReceiveFailed(_) => false
}

produce<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
produce (worker, input) = match Network.try_send (worker, input) {
    Network.Sent => {
        let _ = Network.finish_send worker
        match await_end worker {
            true => {
                let _ = Network.finish_receive worker
                ()
            }
            false => ()
        }
    }
    Network.Full => produce (worker, input)
    Network.Closed => ()
    Network.SendFailed(_) => ()
}

main : Unit -> Int
main () = {
    let input = match ByteOps.append_byte (ByteOps.empty (), 42) {
        ByteOps.BytesAppended(bytes) => bytes
        ByteOps.InvalidByte => ByteOps.empty ()
    }
    resource Network.Pair<N> pair = (1, produce, consume, input, input) {
        match Network.settle pair {
            Network.Ok => 42
            Network.Failed(_) => 0
        }
    }
}
