mod support;

fn run_paired_protocol(
    protocol: &str,
    entry_source: &str,
) -> Result<String, ash::driver::FileFailure> {
    use ash::{
        driver::{RunConfiguration, run_path},
        module::ModuleRoots,
    };
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    static NEXT: AtomicU64 = AtomicU64::new(0);
    struct FixtureDir(std::path::PathBuf);
    impl Drop for FixtureDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let directory = loop {
        let id = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "ash-paired-producing-cleanup-{}-{id}",
            std::process::id()
        ));
        match fs::create_dir(&path) {
            Ok(()) => break FixtureDir(path),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("fixture directory: {error}"),
        }
    };
    let entry = directory.0.join("paired-producing-cleanup.ash");
    for (path, source) in [
        (&entry, entry_source),
        (
            &directory.0.join("network_types.ash"),
            include_str!("../libraries/network_types.ash"),
        ),
        (
            &directory.0.join("network_codec.ash"),
            include_str!("../libraries/network_codec.ash"),
        ),
        (&directory.0.join("network_protocol.ash"), protocol),
    ] {
        fs::write(path, source).expect("write paired protocol fixture");
    }
    run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .map(|observation| observation.value_display())
}

#[test]
fn paired_producing_cleanup_reaches_settlement() {
    let result = run_paired_protocol(
        include_str!("../libraries/network_protocol.ash"),
        include_str!("fixtures/pinned-network/paired-producing-cleanup.ash"),
    )
    .expect("the paired producing-cleanup program completes");
    assert_eq!(result, "42");
}

#[test]
fn malformed_paired_frame_cannot_succeed() {
    let protocol = include_str!("../libraries/network_protocol.ash");
    assert_eq!(protocol.matches("Codec.encode head").count(), 1);
    let malformed = protocol.replace("Codec.encode head", "Codec.Encoded(ByteOps.empty ())");
    match run_paired_protocol(
        &malformed,
        include_str!("fixtures/pinned-network/paired-producing-cleanup.ash"),
    ) {
        Ok(value) => assert_ne!(value, "42"),
        Err(error) => assert!(
            matches!(
                error.pipeline_failure(),
                Some(ash::driver::PipelineFailure::Runtime(_))
            ),
            "expected runtime failure, got {error:?}"
        ),
    }
}

#[test]
fn acknowledgements_preserve_unmatched_obligations() {
    let protocol = format!(
        "{}\n{}",
        include_str!("../libraries/network_protocol.ash"),
        r#"
pub acknowledgement_cases : Unit -> Int
acknowledgement_cases () = {
    let (registered, status) = reserve_job (initial_root (), 0, LedgerTypes.Root, 1, ByteOps.empty ())
    match status {
        Rejected => 0
        Registered(child) => {
            let closed = close_record (registered, LedgerTypes.Root)
            let wrong_peer = acknowledge (closed, LedgerTypes.Root, child, 0)
            let missing_parent = acknowledge (wrong_peer, LedgerTypes.Work(9, 9), child, 1)
            let missing_child = acknowledge (missing_parent, LedgerTypes.Root, LedgerTypes.Work(0, 1), 1)
            let matched = acknowledge (missing_child, LedgerTypes.Root, child, 1)
            let duplicate = acknowledge (matched, LedgerTypes.Root, child, 1)
            match (root_quiet closed, root_quiet wrong_peer, root_quiet missing_parent, root_quiet missing_child, root_quiet matched, root_quiet duplicate) {
                (false, false, false, false, true, true) => 42
                _ => 0
            }
        }
    }
}
"#
    );
    let entry = "import network_protocol as Protocol\nmain : Unit -> Int\nmain () = Protocol.acknowledgement_cases ()\n";
    let result = run_paired_protocol(&protocol, entry).expect("ordinary acknowledgement cases run");
    assert_eq!(result, "42");
}

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
        let _ = check_bytes (message, expected)
        let _ = resource Control.Store<S,(Unit -> Unit ! {Control.Drive<S>})> store = () {
            handle {
                let _ = perform Checkpoint<S>.checkpoint ()
                ()
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
