mod support;

#[test]
fn validated_code_and_binding_tables_have_thread_safe_rust_ownership() {
    fn require_send_sync<T: Send + Sync>() {}

    require_send_sync::<ash::core::ValidatedEffectProgram>();
    require_send_sync::<ash::foreign::source_runtime::SourceNativeBindings>();
}

#[test]
fn network_entry_cannot_be_an_inline_callback() {
    let source = r#"
import @builtin.network as Network
import @builtin.bytes as ByteOps

start<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
start ignored = ()

main : Unit -> Unit
main () = resource Network.Pair<N> pair = (1, fn(ignored) {
    ()
}, start, ByteOps.empty (), ByteOps.empty ()) {
    ()
}
"#;
    let failure = support::run_module("inline-network-entry.ash", source)
        .expect_err("network entry must be a named top-level designator");
    assert_eq!(failure.reason_code(), "resolve.type-kind", "{failure:?}");
}

#[test]
fn network_entry_cannot_be_a_local_function_value() {
    let source = r#"
import @builtin.network as Network
import @builtin.bytes as ByteOps

start<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
start ignored = ()

main : Unit -> Unit
main () = {
    let local = fn(ignored) {
        ()
    }
    resource Network.Pair<N> pair = (1, local, start, ByteOps.empty (), ByteOps.empty ()) {
        ()
    }
}
"#;
    let failure = support::run_module("local-network-entry.ash", source)
        .expect_err("network entry cannot be a caller-owned closure");
    assert_eq!(failure.reason_code(), "resolve.type-kind", "{failure:?}");
}

#[test]
fn copied_message_reaches_the_other_worker_before_end() {
    let source = r#"
import @builtin.network as Network
import @builtin.bytes as ByteOps
import @builtin.retained_control as Control

effect Checkpoint<S> {
    checkpoint : Unit -> Unit
}

check_bytes : (Bytes, Bytes) -> Unit
check_bytes (actual, expected) = match ByteOps.equal (actual, expected) {
    true => ()
    false => check_bytes (actual, expected)
}

wait_end<N> : Network.Worker<N> -> Bool ! {Network.IO<N>}
wait_end worker = match Network.try_receive worker {
    Network.End => true
    Network.Empty => wait_end worker
    Network.Message(_, _) => false
    Network.ReceiveFailed(_) => false
}

produce<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
produce (worker, message) = match Network.try_send (worker, message) {
    Network.Sent => {
        let _ = Network.finish_send worker
        match wait_end worker {
            true => {
                let _ = Network.finish_receive worker
                ()
            }
            false => ()
        }
    }
    Network.Full => produce (worker, message)
    Network.Closed => ()
    Network.SendFailed(_) => ()
}

receive<N> : (Network.Worker<N>, Bytes) -> Bool ! {Network.IO<N>}
receive (worker, expected) = match Network.try_receive worker {
    Network.Empty => receive (worker, expected)
    Network.Message(Network.Application, message) => {
        let _ = resource Control.Store<S,(Unit -> Unit ! {Control.Drive<S>})> store = () {
            handle {
                let _ = perform Checkpoint<S>.checkpoint ()
                check_bytes (message, expected)
            } with Checkpoint<S> using store {
                checkpoint ignored => resume ()
            }
        }
        receive (worker, expected)
    }
    Network.Message(Network.Control, _) => false
    Network.End => true
    Network.ReceiveFailed(_) => false
}

consume<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
consume (worker, expected) = {
    let _ = Network.finish_send worker
    match receive (worker, expected) {
        true => {
            let _ = Network.finish_receive worker
            ()
        }
        false => ()
    }
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
"#;
    let observation = support::run_module("pinned-network.ash", source)
        .expect("two admitted workers exchange a copied message and observe End");
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn network_entry_requires_a_polymorphic_worker_and_bytes() {
    let source = r#"
import @builtin.network as Network
import @builtin.bytes as ByteOps

wrong : (Int, Bytes) -> Unit
wrong ignored = ()

main : Unit -> Unit
main () = resource Network.Pair<N> pair = (1, wrong, wrong, ByteOps.empty (), ByteOps.empty ()) {
    ()
}
"#;
    let failure = support::run_module("wrong-network-entry.ash", source)
        .expect_err("worker entry has the wrong domain and lacks network polymorphism");
    assert_eq!(failure.reason_code(), "type.network-entry", "{failure:?}");
}

#[test]
fn network_identity_cannot_escape_in_a_returned_closure() {
    let source = r#"
import @builtin.network as Network
import @builtin.bytes as ByteOps

start<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
start ignored = ()

main : Unit -> Unit
main () = {
    let leaked = resource Network.Pair<N> pair = (1, start, start, ByteOps.empty (), ByteOps.empty ()) {
        let local : Unit -> Unit ! {Network.Join<N>} = fn(ignored) {
            let _ = Network.settle pair
            ()
        }
        local
    }
    leaked ()
}
"#;
    let failure = support::run_module("escaped-network.ash", source)
        .expect_err("a coordinator closure cannot outlive its network owner");
    assert_eq!(failure.reason_code(), "type.resource-escape", "{failure:?}");
}

#[test]
fn network_io_and_join_cannot_be_performed_or_handled_directly() {
    for (effect, body) in [
        ("IO", "perform Network.IO<N>.internal ()"),
        ("Join", "perform Network.Join<N>.internal ()"),
        (
            "IO",
            "handle () with Network.IO<N> {\ninternal ignored => resume ()\n}",
        ),
        (
            "Join",
            "handle () with Network.Join<N> {\ninternal ignored => resume ()\n}",
        ),
    ] {
        let source = format!(
            "import @builtin.network as Network\nbad<N> : Network.Worker<N> -> Unit ! {{Network.{effect}<N>}}\nbad ignored = {body}\nmain : Unit -> Unit\nmain () = ()\n"
        );
        let failure = support::run_module("direct-network-effect.ash", &source)
            .expect_err("network effects cannot be directly performed or handled");
        assert_eq!(
            failure.reason_code(),
            "resolve.sealed-network",
            "{failure:?}"
        );
    }
}

#[test]
fn network_send_request_cannot_be_performed_directly() {
    let source = r#"
import @builtin.network as Network
start<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}
start (worker, bytes) = {
    let _ = perform Network.IO<N>.send (worker, bytes)
    ()
}
main : Unit -> Unit
main () = ()
"#;
    let failure = support::run_module("direct-network-send.ash", source)
        .expect_err("the sealed send request is private to its canonical wrapper");
    assert_eq!(
        failure.reason_code(),
        "resolve.sealed-network",
        "{failure:?}"
    );
}
