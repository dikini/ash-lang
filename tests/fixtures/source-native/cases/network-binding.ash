import @builtin.generic_cell as Cell
import @builtin.retained_control as Control
import @builtin.foreign as Foreign
import @builtin.bytes as BytesOps
import @builtin.string as Text
import native as Raw
import binding as Binding
import network_protocol as Protocol

effect Checkpoint<N> {
    checkpoint : Unit -> Unit
}

type Step<N> = Done(Int)
    | Waiting(Control.Key<N>)

drain<N> : (Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N>})>, Control.Key<N>) -> Unit ! {Control.Drive<N>, Control.Probe<N>}
drain (store, key) = {
    let quiet = perform Control.Probe<N>.quiescent ()
    match quiet {
        true => ()
        false => {
            let _ = Control.advance_with_drive (store, key)
            drain (store, key)
        }
    }
}

main : Unit -> Int ! {Raw.EchoBytes}
main () = {
    let completed = resource Control.Store<N,(Unit -> Step<N> ! {Control.Drive<N>})> store = () {
        let step = handle {
            let _ = perform Checkpoint<N>.checkpoint ()
            Done(1)
        } with Checkpoint<N> using store {
            checkpoint ignored => {
                let key = retain
                Waiting(key)
            }
        }
        match step {
            Done(value) => 0
            Waiting(key) => {
                let value = match Control.advance_with_drive (store, key) {
                    Control.None => 0
                    Control.Some(next) => match next {
                        Done(result) => result
                        Waiting(other) => 0
                    }
                }
                let _ = drain (store, key)
                value
            }
        }
    }
    match completed == 1 {
        true => resource Cell.Cell<R,Int> result = 0 {
            let bytes = Text.to_utf8 "abc"
            let address = Binding.echo_bytes bytes
            match Foreign.is_null address {
                true => 0
                false => {
                    let reply = Protocol.run ()
                    let _ = Cell.write (result, reply)
                    match BytesOps.equal (bytes, Text.to_utf8 "abc") {
                        true => Cell.read result
                        false => 0
                    }
                }
            }
        }
        false => 0
    }
}
