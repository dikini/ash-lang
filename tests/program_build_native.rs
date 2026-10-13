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
            PathBuf::from(std::env::var_os("CARGO_TARGET_DIR").unwrap()).join("ffi-native-hosts"),
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
