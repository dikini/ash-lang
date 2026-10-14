//! Imported Ash buffer library through the ordinary source and generated host path.

use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path},
    module::ModuleRoots,
};
use sha2::{Digest, Sha256};
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
    fn new() -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-buffer-source-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn imported_ash_buffer_zeroes_writes_and_preserves_nested_acquired_only_result() {
    generated_buffer(
        "import native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Buffer.Outcome<Int>>\nmain () = resource Buffer.Buffer<R> b = 2 {\n    match Buffer.read (b, 0) {\n        Buffer.Success(first) => match Buffer.write (b, 1, 255) {\n            Buffer.Success(()) => match Buffer.read (b, 1) {\n                Buffer.Success(last) => Buffer.Success (first + last)\n                Buffer.Failure(error) => Buffer.Failure error\n            }\n            Buffer.Failure(error) => Buffer.Failure error\n        }\n        Buffer.Failure(error) => Buffer.Failure error\n    }\n}\n",
        Link::Libc,
        "Success(Success(255))",
        "",
        false,
    );
}

#[derive(Clone, Copy)]
enum Link {
    Libc,
    Static,
    Shared,
}

fn checked_tool(command: &mut Command) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn generated_buffer(entry: &str, link: Link, expected: &str, expected_trace: &str, fail: bool) {
    generated_buffer_result(entry, link, Ok(expected), expected_trace, fail);
}

fn generated_buffer_result(
    entry: &str,
    link: Link,
    expected: Result<&str, &str>,
    expected_trace: &str,
    fail: bool,
) {
    let fixture = Fixture::new();
    let library = include_str!("../libraries/native_buffer.ash");
    // Counting wrappers delegate to the actual calloc/free functions. They
    // change only the declared C names; release identity is independent of the
    // requested size and bytes being tested.
    let library = if matches!(link, Link::Libc) {
        library.to_owned()
    } else {
        library
            .replace("name \"calloc\"", "name \"ash_buffer_calloc\"")
            .replace("name \"free\"", "name \"ash_buffer_free\"")
    };
    fs::write(fixture.0.join("native_buffer.ash"), library).unwrap();
    fs::write(fixture.0.join("entry.ash"), entry).unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
    })
    .unwrap_or_else(|error| panic!("imported Ash buffer: {error:?}"));
    println!("Ash buffer compilation: {:?}", compiled.compilation_work());
    let executable = fixture.0.join("program");
    let mut configuration = BuildConfiguration::new(executable.clone());
    if !matches!(link, Link::Libc) {
        let source = fixture.0.join("buffer.c");
        let object = fixture.0.join("buffer.o");
        fs::write(&source, NATIVE).unwrap();
        checked_tool(
            Command::new("cc")
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-fPIC", "-c"])
                .arg(&source)
                .arg("-o")
                .arg(&object),
        );
        configuration.native_inputs = vec![match link {
            Link::Static => {
                let archive = fixture.0.join("libash_buffer_fixture.a");
                checked_tool(Command::new("ar").arg("crs").arg(&archive).arg(&object));
                NativeLinkInput::StaticArchive(archive)
            }
            Link::Shared => {
                let shared = fixture.0.join("libash_buffer_fixture.so");
                checked_tool(
                    Command::new("cc")
                        .args(["-shared", "-Wl,-soname,libash_buffer_fixture.so"])
                        .arg(&object)
                        .arg("-o")
                        .arg(&shared),
                );
                NativeLinkInput::SharedLibrary(shared)
            }
            Link::Libc => unreachable!(),
        }];
    }
    configuration.cargo_target_directory = Some(
        std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"))
            .join("ffi-native-hosts"),
    );
    let prepared = prepare_program(&compiled, configuration).unwrap();
    println!(
        "Ash buffer preparation work: {}",
        prepared.preparation_work()
    );
    fs::remove_file(fixture.0.join("entry.ash")).unwrap();
    fs::remove_file(fixture.0.join("native_buffer.ash")).unwrap();
    let built = build_prepared(prepared).unwrap_or_else(|error| {
        let log = error
            .build_log()
            .and_then(|path| fs::read_to_string(path).ok())
            .unwrap_or_default();
        panic!("generated Ash buffer host: {error:?}\n{log}")
    });
    let generated = built.generated_source().parent().unwrap();
    // Retain one live proof per link mode when the owning verification asks;
    // ordinary test runs keep their existing temporary-fixture cleanup.
    let retained = std::env::var_os("ASH_NATIVE_BUFFER_EVIDENCE_DIR").and_then(|root| {
        let slot = PathBuf::from(root).join(match link {
            Link::Libc => "libc",
            Link::Static => "static",
            Link::Shared => "shared",
        });
        if slot.exists() {
            None
        } else {
            fs::create_dir_all(&slot).unwrap();
            Some(slot)
        }
    });
    for (role, path) in [
        ("generated_source", built.generated_source().to_path_buf()),
        ("private_image", generated.join("program-image.bin")),
        ("expected_facts", generated.join("expected-facts.bin")),
        ("executed_host", executable.clone()),
    ] {
        let bytes = fs::read(&path).unwrap();
        if let Some(directory) = &retained {
            fs::copy(&path, directory.join(role)).unwrap();
        }
        println!(
            "buffer/native artifact {role} bytes={} sha256={:x} path={}",
            bytes.len(),
            Sha256::digest(&bytes),
            path.display()
        );
    }
    fs::remove_file(generated.join("program-image.bin")).unwrap();
    fs::remove_file(generated.join("expected-facts.bin")).unwrap();
    let trace = fixture.0.join("trace");
    let mut command = Command::new(executable);
    command
        .env("ASH_BUFFER_TRACE", &trace)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if matches!(link, Link::Shared) {
        command.env("LD_LIBRARY_PATH", &fixture.0);
    }
    if fail {
        command.env("ASH_BUFFER_FAIL_ALLOCATION", "1");
    } else {
        command.env_remove("ASH_BUFFER_FAIL_ALLOCATION");
    }
    let mut child = command.spawn().unwrap();
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() > Duration::from_secs(30) {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("buffer fixture exceeded 30-second execution deadline");
        }
        thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().unwrap();
    let observed_trace = match fs::read_to_string(&trace) {
        Ok(trace) => trace,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(error) => panic!("buffer trace: {error}"),
    };
    println!("buffer/native actual trace:\n{observed_trace}");
    match expected {
        Ok(expected) => {
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(String::from_utf8(output.stdout).unwrap().trim(), expected);
        }
        Err(reason) => {
            assert!(!output.status.success());
            assert!(
                output.stdout.is_empty(),
                "terminal refusal fabricates no Outcome"
            );
            let error = String::from_utf8(output.stderr).unwrap();
            assert!(error.contains(reason), "{error}");
        }
    }
    assert_eq!(observed_trace, expected_trace);
    if let Some(directory) = retained {
        fs::write(directory.join("trace.txt"), observed_trace).unwrap();
        fs::write(
            directory.join("observation.txt"),
            match expected {
                Ok(value) => format!("success: {value}\n"),
                Err(reason) => format!("terminal: {reason}\n"),
            },
        )
        .unwrap();
        for name in [
            "buffer.c",
            "buffer.o",
            "libash_buffer_fixture.a",
            "libash_buffer_fixture.so",
        ] {
            let input = fixture.0.join(name);
            if input.exists() {
                fs::copy(input, directory.join(name)).unwrap();
            }
        }
    }
}

#[test]
fn imported_ash_buffer_evaluates_initializer_once_before_success_or_refusal() {
    for (length, fail, expected, trace) in [
        ("2", false, "(11, Success(2))", "allocate:1:2\nrelease:1\n"),
        ("0", false, "(1, Failure(InvalidLength))", ""),
        ("2", true, "(1, Failure(AllocationFailed))", "null:2\n"),
    ] {
        let entry = format!(
            r#"import native_buffer as Buffer
import @builtin.cell as Cell
main : Unit -> (Int, Buffer.Outcome<Int>)
main () = resource cell<S> trace = 0 {{
    let initialize : Unit -> Int ! {{Cell.Ops<S>}} = fn(ignored) {{
        let _ = Cell.write (trace, Cell.read trace + 1)
        {length}
    }}
    let result = resource Buffer.Buffer<R> b = (initialize ()) {{
        let _ = Cell.write (trace, Cell.read trace + 10)
        Buffer.length b
    }}
    (Cell.read trace, result)
}}
"#
        );
        generated_buffer(&entry, Link::Static, expected, trace, fail);
    }
}

#[test]
fn imported_ash_buffer_initialized_extent_does_not_impose_a_new_capacity_limit() {
    generated_buffer(
        "import native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource Buffer.Buffer<R> b = 327680 {\nBuffer.length b\n}\n",
        Link::Static,
        "Success(327680)",
        "allocate:1:327680\nrelease:1\n",
        false,
    );
}

#[test]
fn imported_ash_buffer_reentrant_deep_completion_releases_each_activation_once() {
    let expected_trace = (1..=21)
        .map(|id| format!("allocate:{id}:1\n"))
        .chain((1..=21).rev().map(|id| format!("release:{id}\n")))
        .collect::<String>();
    generated_buffer(
        r#"import native_buffer as Buffer
visit : Int -> Int
visit depth = match (resource Buffer.Buffer<R> b = 1 {
    match depth == 0 {
        true => 0
        false => visit (depth + Buffer.MinusOne)
    }
}) {
    Buffer.Success(value) => value + 1
    Buffer.Failure(error) => 999
}
main : Unit -> Int
main () = visit 20
"#,
        Link::Static,
        "21",
        &expected_trace,
        false,
    );
}

#[test]
fn imported_ash_buffer_accepts_deep_evaluated_length_input() {
    let mut length = "2".to_owned();
    for _ in 0..64 {
        length = format!("(0 + {length})");
    }
    generated_buffer(
        &format!(
            "import native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource Buffer.Buffer<R> b = {length} {{\nBuffer.length b\n}}\n"
        ),
        Link::Static,
        "Success(2)",
        "allocate:1:2\nrelease:1\n",
        false,
    );
}

#[test]
fn imported_ash_buffer_inner_cleanup_preserves_enclosing_cell_and_live_buffer_access() {
    generated_buffer(
        include_str!("fixtures/native-buffer/cell_cleanup.ash"),
        Link::Static,
        "42",
        "allocate:1:1\nrelease:1\n",
        false,
    );
}

#[test]
fn imported_ash_buffer_ordinary_operation_override_does_not_replace_native_state() {
    generated_buffer(
        r#"import native_buffer as Buffer
main : Unit -> Buffer.Outcome<(Buffer.Outcome<Int>, Buffer.Outcome<Int>)>
main () = resource Buffer.Buffer<R> b = 1 {
    let _ = Buffer.write (b, 0, 42)
    let overridden = handle (Buffer.read (b, 0)) with Buffer.Ops<Buffer.Buffer<R>> {
        length ignored => resume 9
        read ignored => resume Buffer.Success 7
        write ignored => resume Buffer.Success ()
    }
    (overridden, Buffer.read (b, 0))
}
"#,
        Link::Static,
        "Success(Success(7), Success(42))",
        "allocate:1:1\nrelease:1\n",
        false,
    );
}

#[test]
fn imported_ash_buffer_discard_runs_inner_cleanup_with_outer_cell_and_owner_live() {
    generated_buffer(
        r#"import native_buffer as Buffer
import @builtin.cell as Cell
effect Stop {
    stop : Unit -> Unit
}
main : Unit -> Int
main () = resource cell<S> trace = 0 {
    let result = handle (resource Buffer.Buffer<R> b = 1 {
        let _ = Buffer.write (b, 0, 2)
        cleanup fn(ignored) {
            match Buffer.read (b, 0) {
                Buffer.Success(value) => Cell.write (trace, (Cell.read trace) * 10 + value)
                Buffer.Failure(error) => ()
            }
        } {
            let _ = perform Stop.stop ()
            let _ = Cell.write (trace, 9)
            42
        }
    }) with Stop {
        stop ignored => {
            let _ = discard
            let _ = Cell.write (trace, (Cell.read trace) * 10 + 3)
            Buffer.Success 7
        }
    }
    Cell.read trace
}
"#,
        Link::Static,
        "23",
        "allocate:1:1\nrelease:1\n",
        false,
    );
}

#[test]
fn imported_ash_buffer_discard_cleanup_can_acquire_and_finish_an_inner_buffer() {
    generated_buffer(
        include_str!("fixtures/native-buffer/discard_cleanup.ash"),
        Link::Static,
        "42",
        "allocate:1:1\nallocate:2:1\nrelease:2\nrelease:1\n",
        false,
    );
}

#[test]
fn imported_ash_buffer_cells_registrations_and_cleanup_keep_structural_order() {
    generated_buffer(
        include_str!("fixtures/native-buffer/registration.ash"),
        Link::Static,
        "210",
        "allocate:1:1\nrelease:1\n",
        false,
    );
}

#[test]
fn imported_ash_buffer_static_and_shared_policy_refusals_precede_mutation() {
    for link in [Link::Static, Link::Shared] {
        generated_buffer(
            r#"import native_buffer as Buffer
main : Unit -> Buffer.Outcome<(Buffer.Outcome<Int>, Buffer.Outcome<Unit>, Buffer.Outcome<Unit>, Buffer.Outcome<Int>, Buffer.Outcome<Int>, Buffer.Outcome<Int>, Int)>
main () = resource Buffer.Buffer<R> b = 2 {
    let zero = Buffer.read (b, 0)
    let _ = Buffer.write (b, 0, 42)
    let index = Buffer.write (b, 2, 256)
    let byte = Buffer.write (b, 0, 256)
    let huge = Buffer.read (b, (9223372036854775807 * 10))
    let _ = Buffer.write (b, 1, 255)
    (zero, index, byte, huge, Buffer.read (b, 0), Buffer.read (b, 1), Buffer.length b)
}
"#,
            link,
            "Success(Success(0), Failure(InvalidIndex), Failure(InvalidByte), Failure(InvalidIndex), Success(42), Success(255), 2)",
            "allocate:1:2\nrelease:1\n",
            false,
        );
    }
}

#[test]
fn imported_ash_buffer_invalid_lengths_never_enter_c_and_null_skips_body() {
    for (length, fail, expected, trace) in [
        ("0", false, "Failure(InvalidLength)", ""),
        ("MinusOne", false, "Failure(InvalidLength)", ""),
        (
            "(9223372036854775807 + 1)",
            false,
            "Failure(InvalidLength)",
            "",
        ),
        ("2", true, "Failure(AllocationFailed)", "null:2\n"),
    ] {
        generated_buffer(
            &format!(
                "import native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource Buffer.Buffer<R> b = {} {{\nBuffer.length b + 99\n}}\n",
                length.replace("MinusOne", "Buffer.MinusOne")
            ),
            Link::Static,
            expected,
            trace,
            fail,
        );
    }
}

#[test]
fn imported_ash_buffer_captured_resume_and_owned_discard_release_once_in_order() {
    for (clause, expected) in [
        ("resume ()", "Success(Success(99))"),
        (
            "{\nlet _ = discard\nBuffer.Success (Buffer.Success 7)\n}",
            "Success(Success(7))",
        ),
    ] {
        generated_buffer(
            &format!(
                r#"import native_buffer as Buffer
effect Stop {{
    stop : Unit -> Unit
}}
main : Unit -> Buffer.Outcome<Buffer.Outcome<Int>>
main () = handle (resource Buffer.Buffer<R> outer = 2 {{
    resource Buffer.Buffer<S> inner = 3 {{
        let _ = Buffer.write (outer, 0, 42)
        let _ = Buffer.write (inner, 0, 57)
        let _ = perform Stop.stop ()
        match (Buffer.read (outer, 0), Buffer.read (inner, 0)) {{
            (Buffer.Success(a), Buffer.Success(b)) => a + b
            _ => 999
        }}
    }}
}}) with Stop {{
    stop ignored => {clause}
}}
"#
            ),
            Link::Static,
            expected,
            "allocate:1:2\nallocate:2:3\nrelease:2\nrelease:1\n",
            false,
        );
    }
}

const NATIVE: &str = r#"#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

struct allocation { void *address; unsigned identity; };
static struct allocation owners[128];
static unsigned next_identity;

static FILE *trace(void) {
    const char *path = getenv("ASH_BUFFER_TRACE");
    if (!path) abort();
    FILE *file = fopen(path, "a");
    if (!file) abort();
    return file;
}

void *ash_buffer_calloc(size_t length, size_t width) {
    if (width != 1 || length == 0 || next_identity == 128) abort();
    FILE *file = trace();
    if (getenv("ASH_BUFFER_FAIL_ALLOCATION")) {
        fprintf(file, "null:%zu\n", length);
        fclose(file);
        return NULL;
    }
    void *address = calloc(length, width);
    if (!address) abort();
    unsigned identity = ++next_identity;
    owners[identity - 1] = (struct allocation){ address, identity };
    fprintf(file, "allocate:%u:%zu\n", identity, length);
    fclose(file);
    return address;
}

void ash_buffer_free(void *address) {
    for (unsigned slot = 0; slot < next_identity; ++slot) {
        if (owners[slot].address == address) {
            FILE *file = trace();
            fprintf(file, "release:%u\n", owners[slot].identity);
            fclose(file);
            owners[slot].address = NULL;
            free(address);
            return;
        }
    }
    abort();
}
"#;
