//! Public C observations through authenticated generated scalar-native hosts.

use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path},
    module::ModuleRoots,
};

const NATIVE: &str = include_str!("fixtures/source-native/native.ash");
const FACADE: &str = include_str!("fixtures/source-native/facade.ash");
const HELPER: &str = include_str!("fixtures/source-native/helper.ash");
const C: &str = include_str!("fixtures/source-native/native_counter.c");

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        loop {
            let id = IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-native-public-e2e-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("native executable fixture: {error}"),
            }
        }
    }

    fn native_inputs(&self) -> [NativeLinkInput; 2] {
        let source = self.0.join("native_counter.c");
        let object = self.0.join("native_counter.o");
        let archive = self.0.join("libash_counter_fixture.a");
        let shared = self.0.join("libash_counter_fixture.so");
        fs::write(&source, C).unwrap();
        checked_tool(
            Command::new("cc")
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-fPIC", "-c"])
                .arg(&source)
                .arg("-o")
                .arg(&object),
        );
        checked_tool(Command::new("ar").arg("crs").arg(&archive).arg(&object));
        checked_tool(
            Command::new("cc")
                .args(["-shared", "-Wl,-soname,libash_counter_fixture.so"])
                .arg(&object)
                .arg("-o")
                .arg(&shared),
        );
        [
            NativeLinkInput::StaticArchive(archive),
            NativeLinkInput::SharedLibrary(shared),
        ]
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn checked_tool(command: &mut Command) {
    let output = command
        .output()
        .expect("native fixture tool must be installed");
    assert!(
        output.status.success(),
        "native fixture tool failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

// Reuse the first matrix program: no additional Ash compilation or successful
// native host is needed to observe public preparation and linker refusals.
fn verify_build_refusals(
    compiled: &ash::driver::CompiledProgram,
    directory: &Path,
    non_library: &Path,
    cache: &Path,
) {
    let output = directory.join("program");
    let mut unsupported = BuildConfiguration::new(output.clone());
    unsupported.target = "unsupported-profile".to_owned();
    assert_eq!(
        prepare_program(compiled, unsupported).unwrap_err().reason(),
        "build.unsupported-target"
    );
    for invalid in [
        NativeLinkInput::StaticArchive(non_library.to_path_buf()),
        NativeLinkInput::SharedLibrary(non_library.to_path_buf()),
    ] {
        let mut configuration = BuildConfiguration::new(output.clone());
        configuration.native_inputs = vec![invalid];
        let failure = prepare_program(compiled, configuration).unwrap_err();
        assert_eq!(failure.reason(), "build.native-input");
        assert_eq!(failure.responsibility(), "input");
    }
    assert!(!directory.join(".ash-build").exists());
    assert!(!output.exists());

    // The valid checked program requires unique ash_counter_* symbols, but no
    // linker input supplies them. Linking must refuse and retain its evidence;
    // it cannot replace an existing executable destination or invoke native code.
    let previous = b"preserved destination\n";
    fs::write(&output, previous).unwrap();
    let mut missing = BuildConfiguration::new(output.clone());
    missing.cargo_target_directory = Some(cache.to_path_buf());
    let prepared = prepare_program(compiled, missing).unwrap();
    let failure = build_prepared(prepared).unwrap_err();
    assert_eq!(failure.reason(), "build.native-tool");
    let log = failure.build_log().expect("link refusal retains its log");
    let diagnostic = fs::read_to_string(log).unwrap();
    assert!(diagnostic.contains("ash_counter_echo_i8"), "{diagnostic}");
    assert!(
        diagnostic.contains("undefined symbol") || diagnostic.contains("undefined reference"),
        "missing native symbol must be the linker failure: {diagnostic}"
    );
    assert!(log.parent().unwrap().join("src/main.rs").is_file());
    assert_eq!(fs::read(&output).unwrap(), previous);
}

// The test uses the public build phase, with no private image/descriptor edits or
// hand-installed callbacks. Sources disappear before host preparation/linkage.
fn build_case(fixture: &Fixture, name: &str, source: &str, native: NativeLinkInput) -> PathBuf {
    let directory = fixture.0.join(name);
    fs::create_dir(&directory).unwrap();
    for (file, text) in [
        ("entry.ash", source),
        ("native.ash", NATIVE),
        ("facade.ash", FACADE),
        ("helper.ash", HELPER),
    ] {
        fs::write(directory.join(file), text).unwrap();
    }
    let compiled = compile_path(RunConfiguration {
        entry: directory.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .unwrap();
    let compilation_work = *compiled.compilation_work();
    for file in ["entry.ash", "native.ash", "facade.ash", "helper.ash"] {
        fs::remove_file(directory.join(file)).unwrap();
    }
    let mut configuration = BuildConfiguration::new(directory.join("program"));
    configuration.native_inputs = vec![native];
    let cache = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    configuration.cargo_target_directory = Some(cache.join("ffi-native-hosts"));
    if matches!(
        configuration.native_inputs.as_slice(),
        [NativeLinkInput::StaticArchive(_)]
    ) {
        verify_build_refusals(
            &compiled,
            &directory,
            &fixture.0.join("native_counter.c"),
            configuration.cargo_target_directory.as_deref().unwrap(),
        );
    }
    let prepared = prepare_program(&compiled, configuration).unwrap();
    assert_eq!(*compiled.compilation_work(), compilation_work);
    assert!(!prepared.generated_rust().contains("compile_path"));
    let preparation_work = prepared.preparation_work();
    drop(compiled);
    let built = build_prepared(prepared).unwrap_or_else(|error| {
        let log = error
            .build_log()
            .and_then(|path| fs::read_to_string(path).ok())
            .unwrap_or_default();
        panic!("{error}\n{log}");
    });
    assert_eq!(built.compilation_work(), compilation_work);
    assert_eq!(built.preparation_work(), preparation_work);
    let generated = built.generated_source();
    let generated_text = fs::read_to_string(generated).unwrap();
    assert!(generated_text.contains("include_bytes!(\"program-image.bin\")"));
    assert!(generated_text.contains("include_bytes!(\"expected-facts.bin\")"));
    let image = generated.parent().unwrap().join("program-image.bin");
    let facts = generated.parent().unwrap().join("expected-facts.bin");
    let image_bytes = fs::metadata(&image).unwrap().len();
    let facts_bytes = fs::metadata(&facts).unwrap().len();
    let old_literal_work = 2
        * (5 * (image_bytes + facts_bytes)
            + 5 * (image_bytes.div_ceil(16) + facts_bytes.div_ceil(16)));
    eprintln!(
        "native packaging: Rust={} bytes, image={image_bytes}, facts={facts_bytes}, preparation={preparation_work}, former literal payload reserve/write={old_literal_work}",
        generated_text.len()
    );
    // Run from embedded bytes after the successful build inputs disappear.
    // The separate failed-link project retains its source and diagnostics.
    fs::remove_file(generated).unwrap();
    fs::remove_file(image).unwrap();
    fs::remove_file(facts).unwrap();
    built.executable().to_path_buf()
}

// LD_LIBRARY_PATH belongs only to this child; no global environment mutation or
// emitted rpath is required. The explicit SONAME makes ordinary lookup observable.
fn run_host(executable: &Path, fixture: &Fixture, supply_loader_path: bool) -> (Output, Vec<u8>) {
    let trace = fixture.0.join("calls.trace");
    fs::write(&trace, []).unwrap();
    let mut command = Command::new(executable);
    if supply_loader_path {
        let mut directories = vec![fixture.0.clone()];
        if let Some(previous) = std::env::var_os("LD_LIBRARY_PATH") {
            directories.extend(std::env::split_paths(&previous));
        }
        command.env(
            "LD_LIBRARY_PATH",
            std::env::join_paths(directories).unwrap(),
        );
    } else {
        command.env_remove("LD_LIBRARY_PATH");
    }
    command
        .current_dir(&fixture.0)
        .env("ASH_NATIVE_COUNTER_TRACE", &trace)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command.spawn().unwrap();
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() > Duration::from_secs(30) {
            child.kill().unwrap();
            let _ = child.wait();
            panic!("native fixture child exceeded its 30-second transport deadline");
        }
        thread::sleep(Duration::from_millis(20));
    }
    (child.wait_with_output().unwrap(), fs::read(trace).unwrap())
}

#[test]
fn generated_scalar_hosts_preserve_real_native_counts_and_exact_results_with_both_linkages() {
    let fixture = Fixture::new();
    let inputs = fixture.native_inputs();
    let mut row = "{}".to_owned();
    for _ in 0..43 {
        row = format!("{{Nest<{row}>}}");
    }
    // Exercise independent startup reconstruction past the former row-wire
    // depth cutoff using the existing two hosts and their real native calls.
    let template = include_str!("fixtures/source-native/cases/combined.ash");
    assert_eq!(template.matches("Echo<{}, Int, {}>").count(), 3);
    assert_eq!(template.matches("effect Left<T>").count(), 1);
    let source = template
        .replace("Echo<{}, Int, {}>", &format!("Echo<{row}, Int, {{}}>"))
        .replace(
            "effect Left<T>",
            "effect Nest<Rows : EffectRow> {\n    tick : Unit -> Unit\n}\n\neffect Left<T>",
        );
    // Keep the whole build matrix sequential: a single root Cargo window owns
    // connected verification. These are real C calls, not corrupted callbacks.
    for (linkage, input) in ["static", "shared"].into_iter().zip(inputs) {
        let name = "combined";
        let result = "(127, 900, 18446744073709551615, (), 83)\n";
        let trace = b"iuvii";
        let executable = build_case(&fixture, &format!("{linkage}-{name}"), &source, input);
        if linkage == "shared" {
            let (output, calls) = run_host(&executable, &fixture, false);
            assert!(
                !output.status.success(),
                "automatic rpath must not be emitted"
            );
            assert!(output.stdout.is_empty());
            assert!(
                calls.is_empty(),
                "loader refusal precedes every native call"
            );
            let diagnostic = String::from_utf8_lossy(&output.stderr);
            assert!(
                diagnostic.contains("libash_counter_fixture.so"),
                "{diagnostic}"
            );
            assert!(
                diagnostic.contains("error while loading shared libraries"),
                "{diagnostic}"
            );
        }
        // Repeat an independently restored host activation after source loss.
        for _ in 0..2 {
            let (output, calls) = run_host(&executable, &fixture, true);
            assert!(output.status.success(), "{linkage}/{name}: {output:?}");
            assert_eq!(output.stdout, result.as_bytes(), "{linkage}/{name}");
            assert!(output.stderr.is_empty(), "{linkage}/{name}: {output:?}");
            assert_eq!(calls, trace, "{linkage}/{name}: native call count/order");
        }
    }
}

#[test]
fn generated_native_constant_operands_keep_declared_signed_values() {
    let fixture = Fixture::new();
    let inputs = fixture.native_inputs();
    let contract = r#"import @builtin.foreign as Foreign
pub foreign library Counter {
    profile "x86_64-unknown-linux-gnu"
    repr I8 = signed(8)
    repr U64 = unsigned(64)
    const Negative : I8 = -7
    const Maximum : U64 = 18446744073709551615
    symbol Wide : Unit -> Foreign.Call<Int> {
        name "ash_counter_echo_u64"
        abi (U64) -> U64
        operand 0 from constant Maximum
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Fixed : Unit -> Foreign.Call<Int> {
        name "ash_counter_echo_i8"
        abi (I8) -> I8
        operand 0 from constant Negative
        output result as scalar
        outcome otherwise { readable result }
    }
}
"#;
    for (index, native) in inputs.into_iter().enumerate() {
        let directory = fixture.0.join(format!("constant-{index}"));
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("native.ash"), contract).unwrap();
        fs::write(directory.join("entry.ash"), "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> (Int, Int, Foreign.Call<Int>, Foreign.Call<Int>) ! {Native.Fixed, Native.Wide}\nmain () = (Native.Negative, Native.Maximum, perform Native.Fixed.call (), perform Native.Wide.call ())\n").unwrap();
        let compiled = compile_path(RunConfiguration {
            entry: directory.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        fs::remove_file(directory.join("entry.ash")).unwrap();
        fs::remove_file(directory.join("native.ash")).unwrap();
        let mut configuration = BuildConfiguration::new(directory.join("program"));
        configuration.native_inputs = vec![native];
        configuration.cargo_target_directory = Some(
            std::env::var_os("CARGO_TARGET_DIR")
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
                .join("ffi-native-hosts"),
        );
        let prepared = prepare_program(&compiled, configuration).unwrap();
        drop(compiled);
        let built = build_prepared(prepared).unwrap();
        let generated = built.generated_source();
        fs::remove_file(generated.parent().unwrap().join("program-image.bin")).unwrap();
        fs::remove_file(generated.parent().unwrap().join("expected-facts.bin")).unwrap();
        let (output, calls) = run_host(built.executable(), &fixture, true);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            output.stdout,
            b"(-7, 18446744073709551615, Returned(-7), Returned(18446744073709551615))\n"
        );
        assert_eq!(calls, b"iw");
    }
}

#[test]
fn generated_noncallable_sentinel_preserves_exact_bits_with_both_linkages() {
    let fixture = Fixture::new();
    let contract = r#"import @builtin.foreign as Foreign
pub foreign library Sentinels {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    repr Destructor = function_address
    sentinel Transient : Destructor = all_bits_one
    symbol Check<Before : EffectRow, T, After : EffectRow> : Unit -> Foreign.Call<Int> {
        name "ash_counter_noncallable_sentinel"
        abi (Destructor) -> I32
        operand 0 from constant Transient
        output result as scalar
        outcome otherwise { readable result }
    }
}
"#;
    for (index, native) in fixture.native_inputs().into_iter().enumerate() {
        let directory = fixture.0.join(format!("sentinel-{index}"));
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("native.ash"), contract).unwrap();
        fs::write(directory.join("entry.ash"), "import @builtin.foreign as Foreign\nimport native (Check as Inspect)\ninvoke<T> : T -> Foreign.Call<Int> ! {Inspect<{}, T, {}>}\ninvoke value = perform Inspect<{}, T, {}>.call ()\nmain : Unit -> (Foreign.Call<Int>, Foreign.Call<Int>) ! {Inspect<{}, Int, {}>, Inspect<{}, Unit, {}>}\nmain () = (invoke 1, invoke ())\n").unwrap();
        let compiled = compile_path(RunConfiguration {
            entry: directory.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        fs::remove_file(directory.join("entry.ash")).unwrap();
        fs::remove_file(directory.join("native.ash")).unwrap();
        let mut configuration = BuildConfiguration::new(directory.join("program"));
        configuration.native_inputs = vec![native];
        configuration.cargo_target_directory = Some(
            std::env::var_os("CARGO_TARGET_DIR")
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
                .join("ffi-native-hosts"),
        );
        let prepared = prepare_program(&compiled, configuration).unwrap();
        assert!(
            prepared
                .generated_rust()
                .contains("usize::MAX as *mut core::ffi::c_void")
        );
        assert!(!prepared.generated_rust().contains("transmute"));
        drop(compiled);
        let built = build_prepared(prepared).unwrap_or_else(|error| {
            let log = error
                .build_log()
                .and_then(|path| fs::read_to_string(path).ok())
                .unwrap_or_default();
            panic!("{error}\n{log}");
        });
        let generated = built.generated_source();
        fs::remove_file(generated.parent().unwrap().join("program-image.bin")).unwrap();
        fs::remove_file(generated.parent().unwrap().join("expected-facts.bin")).unwrap();
        let (output, calls) = run_host(built.executable(), &fixture, true);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, b"(Returned(7), Returned(7))\n");
        assert_eq!(calls, b"ss");
    }
}

/// One real public producer observation, without starting the generated image.
/// The limits are finite legacy debug-artifact observation bounds, not a strict
/// checked policy, native/header proof or protected deployment configuration.
#[test]
fn producer_receipt_observes_native_build_without_startup() {
    use ash::build::{
        ArtifactPin, ProducerReceipt, ProducerReceiptLimits, ReceiptFailure, ReceiptField,
    };
    use sha2::{Digest, Sha256};
    use std::io::Read;
    use std::os::unix::fs::{DirBuilderExt, MetadataExt};

    const ARTIFACT_CAP: usize = 1_073_741_824;
    let limits = ProducerReceiptLimits {
        artifact_bytes: ARTIFACT_CAP,
        receipt_bytes: 4096,
        records: 64,
        work: 2_147_483_648,
    };
    let cache = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    let cache = fs::canonicalize(cache).unwrap();
    let retain = std::env::var_os("ASH_RECEIPT_EVIDENCE_DIR").map(PathBuf::from);
    let base = retain
        .clone()
        .unwrap_or_else(|| cache.join("receipt-observation-tests"));
    fs::create_dir_all(&base).unwrap();
    let base = fs::canonicalize(base).unwrap();
    assert!(
        base.starts_with(&cache),
        "receipt fixture must use the selected existing cache disk"
    );
    struct Directory {
        path: PathBuf,
        retain: bool,
    }
    impl Drop for Directory {
        fn drop(&mut self) {
            if !self.retain {
                let _ = fs::remove_dir_all(&self.path);
            }
        }
    }
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let directory = loop {
        let path = base.join(format!(
            "case-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        match fs::DirBuilder::new().mode(0o700).create(&path) {
            Ok(()) => {
                break Directory {
                    path,
                    retain: retain.is_some(),
                };
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("receipt observation directory: {error}"),
        }
    };
    let root = &directory.path;
    for (name, bytes) in [
        (
            "entry.ash",
            include_str!("fixtures/source-native/cases/combined.ash"),
        ),
        ("native.ash", NATIVE),
        ("facade.ash", FACADE),
        ("helper.ash", HELPER),
        ("native_counter.c", C),
    ] {
        fs::write(root.join(name), bytes).unwrap();
    }
    let source = root.join("native_counter.c");
    let object = root.join("native_counter.o");
    let archive = root.join("libash_receipt_counter.a");
    let mut tool_records = Vec::new();
    // These are the unchanged scalar fixture's compile/archive commands. No
    // shared object, candidate query or generated executable is invoked.
    for (name, mut command) in [
        ("cc", {
            let mut c = Command::new("cc");
            c.args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-fPIC", "-c"])
                .arg(&source)
                .arg("-o")
                .arg(&object);
            c
        }),
        ("ar", {
            let mut c = Command::new("ar");
            c.arg("crs").arg(&archive).arg(&object);
            c
        }),
    ] {
        let argv: Vec<_> = std::iter::once(command.get_program())
            .chain(command.get_args())
            .map(|value| {
                value
                    .to_str()
                    .expect("the owned fixture path is UTF-8")
                    .to_owned()
            })
            .collect();
        let result = command.output().unwrap();
        fs::write(root.join(format!("{name}.stdout")), &result.stdout).unwrap();
        fs::write(root.join(format!("{name}.stderr")), &result.stderr).unwrap();
        tool_records.push(serde_json::json!({"argv": argv, "exit_code": result.status.code()}));
        assert!(
            result.status.success(),
            "receipt fixture {name}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
    let compiled = compile_path(RunConfiguration {
        entry: root.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .unwrap();
    let configuration = |output| {
        let mut configuration = BuildConfiguration::new(output);
        configuration.native_inputs = vec![NativeLinkInput::StaticArchive(archive.clone())];
        configuration.cargo_target_directory = Some(cache.clone());
        configuration
    };
    let ordinary =
        prepare_program(&compiled, configuration(root.join("ordinary-not-built"))).unwrap();
    assert!(ordinary.producer_receipt().is_none());
    let mut requested = configuration(root.join("program"));
    requested.producer_receipt = Some(limits);
    let prepared = prepare_program(&compiled, requested).unwrap();
    assert_eq!(ordinary.preparation_work(), prepared.preparation_work());
    assert_eq!(ordinary.generated_rust(), prepared.generated_rust());
    let initial = prepared.producer_receipt().unwrap().clone();
    assert_eq!(initial.pin(ReceiptField::FinalElf), None);
    let built = build_prepared(prepared).unwrap_or_else(|error| {
        let log = error.build_log().map(|path| path.display().to_string());
        panic!("receipt native build failed: {error}; retained log: {log:?}")
    });
    let receipt_path = built
        .producer_receipt()
        .expect("opt-in build retains a receipt");
    let receipt =
        ProducerReceipt::read(&mut fs::File::open(receipt_path).unwrap(), limits).unwrap();
    for field in [
        ReceiptField::ProgramImage,
        ReceiptField::ExpectedFacts,
        ReceiptField::GeneratedRust,
        ReceiptField::OriginalMappings,
        ReceiptField::RuntimeFingerprint,
        ReceiptField::DeclaredNativeInputs,
    ] {
        assert_eq!(receipt.pin(field), initial.pin(field), "{field:?}");
    }
    assert_eq!(
        receipt.check_checked_applicability(),
        Err(ReceiptFailure::IncompleteClosure)
    );
    assert_eq!(
        receipt.activate(),
        Err(ReceiptFailure::ProtectedAuthorityUnavailable)
    );
    fn observe(path: &Path, cap: usize) -> ArtifactPin {
        let mut file = fs::File::open(path).unwrap();
        let before = file.metadata().unwrap();
        assert!(before.is_file() && before.len() <= cap as u64);
        let mut count = 0_usize;
        let mut hash = Sha256::new();
        let mut buffer = [0_u8; 8192];
        loop {
            let read = file.read(&mut buffer).unwrap();
            if read == 0 {
                break;
            }
            count = count.checked_add(read).unwrap();
            assert!(count <= cap);
            hash.update(&buffer[..read]);
        }
        let after = file.metadata().unwrap();
        assert_eq!(
            (
                before.dev(),
                before.ino(),
                before.len(),
                before.mtime(),
                before.mtime_nsec(),
                before.ctime(),
                before.ctime_nsec()
            ),
            (
                after.dev(),
                after.ino(),
                after.len(),
                after.mtime(),
                after.mtime_nsec(),
                after.ctime(),
                after.ctime_nsec()
            )
        );
        assert_eq!(count as u64, before.len());
        ArtifactPin {
            bytes: count as u64,
            sha256: hash.finalize().into(),
        }
    }
    let generated = built.generated_source();
    let project = generated.parent().unwrap().parent().unwrap();
    let mut observations = Vec::new();
    for (field, path) in [
        (ReceiptField::FinalElf, built.executable().to_path_buf()),
        (ReceiptField::GeneratedRust, generated.to_path_buf()),
        (
            ReceiptField::ProgramImage,
            generated.parent().unwrap().join("program-image.bin"),
        ),
        (
            ReceiptField::ExpectedFacts,
            generated.parent().unwrap().join("expected-facts.bin"),
        ),
    ] {
        let observed = observe(&path, ARTIFACT_CAP);
        assert_eq!(receipt.pin(field), Some(observed));
        observations.push(serde_json::json!({"field": format!("{field:?}"), "path": path, "bytes": observed.bytes, "sha256": observed.sha256}));
    }
    let mut inputs = Vec::new();
    for path in [
        source,
        object,
        archive,
        root.join("entry.ash"),
        root.join("native.ash"),
        root.join("facade.ash"),
        root.join("helper.ash"),
        project.join("Cargo.toml"),
        project.join("Cargo.lock"),
        project.join("rust-toolchain.toml"),
        built.build_log().to_path_buf(),
        receipt_path.to_path_buf(),
    ] {
        let observed = observe(&path, ARTIFACT_CAP);
        inputs.push(
            serde_json::json!({"path": path, "bytes": observed.bytes, "sha256": observed.sha256}),
        );
    }
    let package = project.file_name().unwrap();
    let retired_root = cache
        .join(ash::build::NATIVE_TARGET)
        .join(if cfg!(debug_assertions) {
            "debug"
        } else {
            "release"
        })
        .join(package);
    assert!(!retired_root.exists());
    assert!(!retired_root.with_extension("d").exists());
    let seed_lock: [u8; 32] = Sha256::digest(include_bytes!("../Cargo.lock")).into();
    fs::write(root.join("observation.json"), serde_json::to_vec_pretty(&serde_json::json!({
        "status": "legacy native compile/link observation only; generated executable not started",
        "target": ash::build::NATIVE_TARGET, "tools": tool_records, "inputs": inputs, "observations": observations,
        "seed_cargo_lock": {"bytes": include_bytes!("../Cargo.lock").len(), "sha256": seed_lock},
        "resolved_cargo_lock": project.join("Cargo.lock"),
        "ordinary_preparation_work": ordinary.preparation_work(), "built_preparation_work": built.preparation_work(),
        "artifact_cap": ARTIFACT_CAP, "receipt_cap": limits.receipt_bytes, "records_cap": limits.records, "work_cap": limits.work,
        "protected_authority": "unavailable", "checked_closure": "incomplete", "immutable_execution": "not established",
        "loading_abi_native_behavior": "not established", "published_staging_retired": !project.join("linked-program").exists(),
        "retired_cargo_root": retired_root, "retired_cargo_root_and_depinfo_absent": true
    })).unwrap()).unwrap();
    assert!(!root.join("ordinary-not-built").exists());
    assert!(!project.join("linked-program").exists());
    eprintln!(
        "receipt build observation: {}",
        root.join("observation.json").display()
    );
}
