//! Product resource admission and real native calls through the public build.

use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path},
    module::ModuleRoots,
};
use std::{
    fs,
    path::PathBuf,
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new(entry: &str) -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-source-owner-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(
            path.join("owner.ash"),
            include_str!("fixtures/source-owner/owner.ash"),
        )
        .unwrap();
        fs::write(path.join("entry.ash"), entry).unwrap();
        Self(path)
    }
    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        }
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn source_resource_lifecycle_compiles_from_original_checked_templates() {
    let fixture = Fixture::new(include_str!("fixtures/source-owner/entry.ash"));
    let compiled =
        compile_path(fixture.configuration()).expect("complete source owner/resource admission");
    println!(
        "source owner compilation work: {:?}",
        compiled.compilation_work()
    );
}

#[test]
fn initialized_owner_byte_read_compiles_through_public_source_admission() {
    let fixture = Fixture::new(include_str!("fixtures/source-owner/entry.ash"));
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes")
        .replace(
            "outcome result nonnull { readable result }",
            "outcome result nonnull { readable result, initialized_bytes result from 0 }",
        )
        .replace(
            "read access => resume data",
            "read access => match Foreign.byte_read (state, 0) {\n            Foreign.Returned(byte) => resume byte\n            Foreign.ConversionFailed(_) => resume 0\n        }",
        );
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    compile_path(fixture.configuration()).expect("initialized byte access source admission");
}

#[test]
fn byte_primitives_reject_arbitrary_state_arguments_in_independent_core() {
    for entry in [
        "import @builtin.foreign as Foreign\nmain : Unit -> Foreign.Call<Int>\nmain () = Foreign.byte_read (7, 0)\n",
        "import @builtin.foreign as Foreign\nmain : Unit -> Foreign.Call<Unit>\nmain () = Foreign.byte_write (7, 0, 255)\n",
        "import @builtin.foreign as Foreign\nhelper<S> : (S, Int) -> Foreign.Call<Int>\nhelper pair = Foreign.byte_read pair\nmain : Unit -> Int\nmain () = 42\n",
    ] {
        let fixture = Fixture::new(entry);
        let failure = compile_path(fixture.configuration()).unwrap_err();
        assert!(
            matches!(failure, ash::driver::FileFailure::Pipeline(ref diagnostic)
            if matches!(diagnostic.failure(), ash::driver::PipelineFailure::Validation(_))),
            "arbitrary S must reach independent Core rejection: {failure:?}"
        );
    }
}

#[test]
fn byte_callable_alias_compiles_with_original_call_lineage() {
    let fixture = Fixture::new(include_str!("fixtures/source-owner/byte_entry.ash"));
    fs::write(
        fixture.0.join("owner.ash"),
        include_str!("fixtures/source-owner/byte_owner.ash"),
    )
    .unwrap();
    compile_path(fixture.configuration())
        .expect("selected canonical alias and byte write admission");
}

#[test]
fn generated_byte_owner_reads_writes_and_refuses_without_mutation() {
    generated_owner_program_with_native(
        include_str!("fixtures/source-owner/byte_owner.ash"),
        include_str!("fixtures/source-owner/byte_entry.ash"),
        None,
        "Completed((5, 255, true, 255, false, 255, false, 255), Closed)",
        "acquire:42\nrelease:42\n",
        include_str!("fixtures/source-owner/native_bytes.c"),
    );
}

#[test]
fn generated_byte_owner_borrows_live_state_in_acquire_body_and_finish() {
    let owner = include_str!("fixtures/source-owner/byte_owner.ash")
        .replace("false => Acquired(state, size)", "false => match Foreign.byte_read (state, 0) {\n            Foreign.Returned(byte) => Acquired(state, byte)\n            Foreign.ConversionFailed(_) => Refused ()\n        }")
        .replace("finish (state, data) => match perform Free", "finish (state, data) => {\n        let restored = Foreign.byte_write (state, 0, data)\n        match perform Free")
        .replace("    handlers (state, data)", "    }\n    handlers (state, data)");
    let native = include_str!("fixtures/source-owner/native_bytes.c").replace(
        "record(\"release\", owner->identity);",
        "record(\"release\", owner->identity);\n    record(\"final-byte\", owner->bytes[0]);",
    );
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nimport @builtin.foreign as Foreign\nmain : Unit -> Owner.Scope<Unit, Unit, Foreign.Call<Int>>\nmain () = resource Owner.Probe<{}, R, {}> owner = (42, 7) {\n    let written = Owner.write (owner, 0, 255)\n    Owner.read (owner, 0)\n}\n",
        None,
        "Completed(Returned(255), Closed)",
        "acquire:42\nrelease:42\nfinal-byte:5\n",
        &native,
    );
}

#[test]
fn generated_byte_owner_complete_actuals_nested_aliases_and_override_precedence() {
    let owner = include_str!("fixtures/source-owner/byte_owner.ash")
        .replace(
            "Before : EffectRow, R, After : EffectRow",
            "Before : EffectRow, Phantom, R, After : EffectRow",
        )
        .replace(
            "<{| Before}, R, {| After}>",
            "<{| Before}, Phantom, R, {| After}>",
        );
    let entry = include_str!("fixtures/source-owner/byte_generic_rows_entry.ash")
        .replace("Before : EffectRow, R, After : EffectRow", "Before : EffectRow, Phantom, R, After : EffectRow")
        .replace("<{| Before}, R, {| After}>", "<{| Before}, Phantom, R, {| After}>")
        .replace("<{| Before}, Inner, {| After}>", "<{| Before}, Phantom, Inner, {| After}>")
        .replace("<{Tag}, Outer, {}>", "<{Tag}, Int, Outer, {}>")
        .replace("Foreign.Call<Int>", "(Foreign.Call<Int>, Foreign.Call<Int>, Foreign.Call<Int>)")
        .replace("    Owner.read (inner, 0)", "    let first = Owner.read (inner, 0)\n    let overridden = handle (Owner.read (inner, 0)) with Owner.ProbeOps<Owner.Probe<{| Before}, Phantom, Inner, {| After}>> {\n        read (access, index) => resume Foreign.Returned 84\n        write (access, index, byte) => resume Foreign.Returned ()\n    }\n    let last = Owner.read (inner, 1)\n    (first, overridden, last)");
    // Both selected canonical alias branches execute under two different
    // phantom Type/Row applications of the same defining helper and template.
    // Those arguments are absent from the byte callable's State value type.
    let nested = "Owner.Scope<Unit, Unit, Owner.Scope<Unit, Unit, (Foreign.Call<Int>, Foreign.Call<Int>, Foreign.Call<Int>)>>";
    let entry = format!(
        "{}main : Unit -> ({nested}, {nested})\nmain () = {{\n    let first = resource Owner.Probe<{{Tag}}, Int, Outer, {{}}> outer = (42, 7) {{\n        within outer\n    }}\n    let second = resource Owner.Probe<{{}}, Unit, Other, {{}}> outer = (44, 7) {{\n        within outer\n    }}\n    (first, second)\n}}\n",
        entry.split("main :").next().unwrap()
    );
    generated_owner_program_with_native(
        &owner,
        &entry,
        None,
        "(Completed(Completed((Returned(5), Returned(84), Returned(255)), Closed), Closed), Completed(Completed((Returned(5), Returned(84), Returned(255)), Closed), Closed))",
        "acquire:42\nacquire:43\nrelease:43\nrelease:42\nacquire:44\nacquire:43\nrelease:43\nrelease:44\n",
        include_str!("fixtures/source-owner/native_bytes.c"),
    );
}

#[test]
fn generated_byte_owner_acquired_only_null_and_zero_extent_keep_result_and_release_shape() {
    let owner = include_str!("fixtures/source-owner/byte_owner.ash")
        .replace(
            "pub type Scope<I, E, T> = NotAcquired(I)\n    | Completed(T, Completion<E>)",
            "pub type Outcome<T> = Success(T)\n    | Failure(Unit)",
        )
        .replace(
            "result Scope<Unit, Unit, Answer> for <Answer>",
            "result Outcome<Answer> for <Answer>",
        )
        .replace("codec scope", "codec acquired_only");
    generated_owner_program_with_native(
        &owner,
        "import owner as Owner\nimport @builtin.foreign as Foreign\nread_result : Foreign.Call<Int> -> Int\nread_result value = match value {\n    Foreign.Returned(byte) => byte\n    Foreign.ConversionFailed(_) => 999\n}\nmain : Unit -> (Owner.Outcome<Int>, Owner.Outcome<Int>)\nmain () = {\n    let null = resource Owner.Probe<{}, Null, {}> owner = (0, 7) {\n        read_result (Owner.read (owner, 0))\n    }\n    let zero = resource Owner.Probe<{}, Zero, {}> owner = (42, 0) {\n        read_result (Owner.read (owner, 0))\n    }\n    (null, zero)\n}\n",
        None,
        "(Failure(()), Success(999))",
        "acquire:0\nacquire:42\nrelease:42\n",
        include_str!("fixtures/source-owner/native_bytes.c"),
    );
}

#[test]
fn generated_owner_host_acquires_publishes_private_payload_and_releases_once() {
    generated_owner_case(include_str!("fixtures/source-owner/owner.ash"));
}

#[test]
fn generated_source_provider_methods_preserve_association_and_lexical_forwarding() {
    // Method and operation declaration orders differ. Ordinary interface calls
    // must select their exact checked operation and retain its typed operands.
    generated_owner_program(
        include_str!("fixtures/source-owner/forwarding_owner.ash"),
        include_str!("fixtures/source-owner/forwarding_entry.ash"),
        "Completed((42, 1), Closed)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn generated_source_provider_helpers_retain_evidence_and_ordinary_precedence() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash");
    let helpers = include_str!("fixtures/source-owner/forwarding_helpers.ash");
    generated_owner_program_with_helpers(
        owner,
        include_str!("fixtures/source-owner/forwarding_helper_entry.ash"),
        Some(helpers),
        "Completed((42, 5), Closed)",
        "acquire:42\nrelease:42\n",
    );
    generated_owner_program_with_helpers(
        owner,
        include_str!("fixtures/source-owner/forwarding_override_entry.ash"),
        Some(helpers),
        "Completed((42, (84, 105), 42), Closed)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn generated_source_provider_repeated_and_nested_activations_keep_unique_owners() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash");
    generated_owner_program(
        owner,
        include_str!("fixtures/source-owner/forwarding_repeated_entry.ash"),
        "(Completed((42, 5), Closed), Completed((8, 5), Closed), NotAcquired(()), NotAcquired(()))",
        "acquire:42\nrelease:42\nacquire:8\nrelease:8\nacquire:0\nacquire:9\nrelease:9\n",
    );
    generated_owner_program(
        owner,
        include_str!("fixtures/source-owner/forwarding_nested_entry.ash"),
        "Completed((64, Completed((4, 3), Closed), 64), Closed)",
        "acquire:64\nacquire:4\nrelease:4\nrelease:64\n",
    );
}

#[test]
fn generated_source_provider_wrapped_access_restores_through_generic_helpers() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash")
        .replace(
            "pub interface ProbeProvider",
            "pub type Wrapped<T> = Wrapped(T)\n\npub interface ProbeProvider",
        )
        .replace("read : Access -> Int", "read : Wrapped<Access> -> Int")
        .replace(
            "read access => resume data",
            "read Wrapped(access) => resume data",
        );
    generated_owner_program(
        &owner,
        include_str!("fixtures/source-owner/forwarding_wrapped_entry.ash"),
        "Completed((42, 5), Closed)",
        "acquire:42\nrelease:42\n",
    );
    generated_owner_program_with_helpers(
        &owner,
        include_str!("fixtures/source-owner/forwarding_helper_entry.ash"),
        Some(include_str!(
            "fixtures/source-owner/forwarding_wrapped_helpers.ash"
        )),
        "Completed((42, 5), Closed)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn generated_source_provider_forwarding_preserves_acquired_only_report() {
    let owner = include_str!("fixtures/source-owner/forwarding_owner.ash")
        .replace(
            "pub type Scope<I, E, T> = NotAcquired(I)\n    | Completed(T, Completion<E>)",
            "pub type Outcome<T> = Success(T)\n    | Failure(Unit)",
        )
        .replace(
            "result Scope<Unit, Unit, Answer> for <Answer>",
            "result Outcome<Answer> for <Answer>",
        )
        .replace("codec scope", "codec acquired_only");
    let entry = include_str!("fixtures/source-owner/forwarding_entry.ash").replace(
        "Owner.Scope<Unit, Unit, (Int, Int)>",
        "Owner.Outcome<(Int, Int)>",
    );
    generated_owner_program(
        &owner,
        &entry,
        // Constructor Display renders its tuple payload's fields inside the
        // constructor parentheses; the checked report still has one tuple field.
        "Success(42, 1)",
        "acquire:42\nrelease:42\n",
    );
}

#[test]
fn generated_source_provider_complete_rows_preserve_frozen_metadata() {
    generated_owner_program(
        include_str!("fixtures/source-owner/forwarding_owner.ash"),
        include_str!("fixtures/source-owner/forwarding_generic_rows_entry.ash"),
        "Completed(Completed((4, 5), Closed), Closed)",
        "acquire:42\nacquire:4\nrelease:4\nrelease:42\n",
    );
}

#[test]
fn generated_initialized_byte_owner_host_preserves_native_acquisition_and_release() {
    // The native fixture initializes one eight-byte size_t object. Seven bytes
    // therefore form a valid promised region, independent of its stored value.
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes")
        .replace(
            ": Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
            ": (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
        )
        .replace(
            "outcome result nonnull { readable result }",
            "outcome result nonnull { readable result, initialized_bytes result from 1 }",
        )
        .replace(".call size {", ".call (size, 7) {");
    generated_owner_case(&owner);
    // A zero initialized extent still owns a non-null native allocation.
    generated_owner_case(&owner.replace(".call (size, 7) {", ".call (size, 0) {"));
}

#[test]
fn initialized_byte_resource_without_initialization_fact_is_rejected() {
    let fixture = Fixture::new(include_str!("fixtures/source-owner/entry.ash"));
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes");
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    let failure = compile_path(fixture.configuration()).unwrap_err();
    assert_eq!(failure.reason_code(), "foreign.contract");
}

#[test]
fn generated_initialized_byte_extents_refuse_before_native_owner_entry() {
    let owner = include_str!("fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes")
        .replace(
            ": Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
            ": (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
        )
        .replace(
            "outcome result nonnull { readable result }",
            "outcome result nonnull { readable result, initialized_bytes result from 1 }",
        )
        .replace("input Int", "input (Int, Int)")
        .replace("acquire size =>", "acquire (size, extent) =>")
        .replace(".call size {", ".call (size, extent) {");
    let entry = r#"import @builtin.foreign as Foreign
import owner as Owner
foreign library Inputs {
    profile "x86_64-unknown-linux-gnu"
    repr Signed = signed(64)
    symbol NegativeInput : Unit -> Foreign.Call<Int> {
        name "ash_owner_negative_input"
        abi () -> Signed
        output result as scalar
        outcome otherwise { readable result }
    }
}
unreachable : Unit -> Int
unreachable () = unreachable ()
probe : Int -> Owner.Scope<Unit, Unit, Int>
probe extent = resource Owner.Probe<{}, Fresh, {}> owner = (42, extent) {
    unreachable ()
}
main : Unit -> (Owner.Scope<Unit, Unit, Int>, Owner.Scope<Unit, Unit, Int>) ! {NegativeInput}
main () = {
    let negative = match perform NegativeInput.call () {
        Foreign.Returned(value) => value
        Foreign.ConversionFailed(_) => 0
    }
    (probe negative, probe ((9223372036854775807 + 1) * 2))
}
"#;
    generated_owner_program(&owner, entry, "(NotAcquired(()), NotAcquired(()))", "");
}

fn generated_owner_case(owner: &str) {
    generated_owner_program(
        owner,
        include_str!("fixtures/source-owner/entry.ash"),
        "(Completed(42, Closed), Completed(8, Closed), NotAcquired(()), NotAcquired(()), Completed(Completed(4, Closed), Closed), Completed(84, Closed), NotAcquired(()))",
        "acquire:42\nrelease:42\nacquire:8\nrelease:8\nacquire:0\nacquire:9\nrelease:9\nacquire:64\nacquire:4\nrelease:4\nrelease:64\nacquire:7\nrelease:7\n",
    );
}

fn generated_owner_program(owner: &str, entry: &str, expected_result: &str, expected_trace: &str) {
    generated_owner_program_with_helpers(owner, entry, None, expected_result, expected_trace);
}

fn generated_owner_program_with_helpers(
    owner: &str,
    entry: &str,
    helpers: Option<&str>,
    expected_result: &str,
    expected_trace: &str,
) {
    generated_owner_program_with_native(
        owner,
        entry,
        helpers,
        expected_result,
        expected_trace,
        include_str!("fixtures/source-owner/native_owner.c"),
    );
}

fn generated_owner_program_with_native(
    owner: &str,
    entry: &str,
    helpers: Option<&str>,
    expected_result: &str,
    expected_trace: &str,
    native_source: &str,
) {
    let fixture = Fixture::new(entry);
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    if let Some(helpers) = helpers {
        fs::write(fixture.0.join("helpers.ash"), helpers).unwrap();
    }
    let compiled = compile_path(fixture.configuration()).unwrap();
    println!(
        "forwarding/native compilation work: {:?}",
        compiled.compilation_work()
    );
    let native = fixture.0.join("native_owner.c");
    let object = fixture.0.join("native_owner.o");
    let archive = fixture.0.join("libash_owner.a");
    fs::write(&native, native_source).unwrap();
    for output in [
        Command::new("cc")
            .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"])
            .arg(&native)
            .arg("-o")
            .arg(&object)
            .output()
            .unwrap(),
        Command::new("ar")
            .arg("crs")
            .arg(&archive)
            .arg(&object)
            .output()
            .unwrap(),
    ] {
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    // The generated host restores checked Core; it does not reopen Ash source.
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("owner.ash")).unwrap();
    if helpers.is_some() {
        fs::remove_file(fixture.0.join("helpers.ash")).unwrap();
    }
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    configuration.native_inputs = vec![NativeLinkInput::StaticArchive(archive)];
    let cache = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    configuration.cargo_target_directory = Some(cache.join("ffi-native-hosts"));
    let prepared = prepare_program(&compiled, configuration).unwrap();
    assert!(!prepared.generated_rust().contains("compile_path"));
    let rust_bytes = prepared.generated_rust().len();
    let preparation_work = prepared.preparation_work();
    let built = build_prepared(prepared).unwrap();
    let generated = built.generated_source().parent().unwrap();
    let image = generated.join("program-image.bin");
    let facts = generated.join("expected-facts.bin");
    println!(
        "owner/native preparation: rust_bytes={rust_bytes}, image_bytes={}, fact_bytes={}, work={preparation_work}",
        fs::metadata(&image).unwrap().len(),
        fs::metadata(&facts).unwrap().len(),
    );
    // Compilation embeds both exact payloads. Execution must require neither
    // Ash source nor files used to build the standalone host.
    fs::remove_file(image).unwrap();
    fs::remove_file(facts).unwrap();
    let trace = fixture.0.join("native-trace");
    let mut child = Command::new(executable)
        .env("ASH_OWNER_TRACE", &trace)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() > Duration::from_secs(30) {
            child.kill().unwrap();
            let _ = child.wait();
            panic!("owner fixture exceeded its 30-second execution deadline");
        }
        thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        expected_result
    );
    if expected_trace.is_empty() {
        assert!(
            !trace.exists(),
            "refused extents must not enter native owner code"
        );
    } else {
        assert_eq!(fs::read_to_string(trace).unwrap(), expected_trace);
    }
}
