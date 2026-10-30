import ledger_helper as LedgerMod
import network_types as LedgerTypes
import network_codec as Codec
import @builtin.network as Network
import @builtin.bytes as ByteOps

driver<N> : (Network.Worker<N>, LedgerMod.Ledger) -> Bool ! {Network.IO<N>}
driver (endpoint, ledger) = {
    let LedgerMod.Ledger(next, records, outputs) = ledger
    match outputs {
        LedgerMod.NoOutputs => true
        LedgerMod.OutputCons(head, tail) => match Codec.encode head {
            Codec.Encoded(bytes) => transmit (endpoint, ledger, next, records, head, tail, bytes)
            Codec.EncodeFailed => false
        }
    }
}

transmit<N> : (Network.Worker<N>, LedgerMod.Ledger, Int, LedgerMod.Records, LedgerTypes.Envelope, LedgerMod.Outputs, Bytes) -> Bool ! {Network.IO<N>}
transmit (endpoint, ledger, next, records, head, tail, bytes) = {
    let result = match head {
        LedgerTypes.WorkOut(_, _, _, _) => Network.try_send (endpoint, bytes)
        LedgerTypes.AckOut(_, _) => Network.send_control (endpoint, bytes)
    }
    match result {
        Network.Sent => {
            let successor = LedgerMod.Ledger(next, records, tail)
            driver (endpoint, successor)
        }
        Network.Full => driver (endpoint, ledger)
        Network.Closed => false
        Network.SendFailed(_) => false
    }
}

worker<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
worker (endpoint, payload) = {
    let original = LedgerMod.initial ()
    let (successor, status) = LedgerMod.reserve_job (original, 0, LedgerTypes.Root, 0, payload)
    let received = Network.try_receive endpoint
    let completed = driver (endpoint, successor)
    match completed {
        true => ()
        false => ()
    }
}

main : Unit -> Unit
main () = {
    resource Network.Pair<N> pair = (1, worker, worker, ByteOps.empty (), ByteOps.empty ()) {
        ()
    }
}
