//! Custom region backing through the existing generated native bridge.
use ash::{
    build::{BuildConfiguration, NativeLinkInput, build_prepared, prepare_program},
    driver::{RunConfiguration, compile_path},
    module::ModuleRoots,
};
use std::{fs, path::PathBuf, process::Command};

const NATIVE: &str = r#"import @builtin.foreign as F
pub foreign library RegionFixture {
    profile "x86_64-unknown-linux-gnu"
    symbol Make : Unit -> F.Address { name "region_make" }
    symbol Allocate : F.Address -> F.Address { name "region_allocate" }
    symbol Release : F.Address -> Unit { name "region_release" }
    symbol Inspect : Bytes -> Unit { name "region_inspect" }
    symbol InspectHost : Bytes -> Unit { name "region_inspect_host" }
}
"#;
const TUPLE_BODY: &str = "match (20, 22) {\n            (left, right) => match (left + right) == 42 {\n                true => 42\n                false => 0\n            }\n        }";
const INTEGER_BODY: &str = "let value = 9223372036854775808 * 9223372036854775808 * 4\n        match value == 340282366920938463463374607431768211456 {\n            true => 42\n            false => 0\n        }";
const ENTRY: &str = r#"import native as Raw
import @builtin.regions as Region
import @builtin.foreign as F
provider<R> : F.Address -> ((Region.Request -> Region.Storage<R> ! {Raw.Allocate}), (Unit -> Unit ! {Raw.Release}))
provider state = {
    let allocate : Region.Request -> Region.Storage<R> ! {Raw.Allocate} = fn(request) {
        let backing = perform Raw.Allocate.call state
        Region.from_backing (request, backing, 4096, 64)
    }
    let release : Unit -> Unit ! {Raw.Release} = fn(ignored) {
        let pair = (1, 2)
        let sum = match pair {
            (left, right) => left + right
        }
        perform Raw.Release.call state
    }
    (allocate, release)
}
main : Unit -> Int ! {Raw.Make, Raw.Allocate, Raw.Release}
main () = {
    let state = perform Raw.Make.call ()
    region<R> owner = (provider state) {
        match (20, 22) {
            (left, right) => match (left + right) == 42 {
                true => 42
                false => 0
            }
        }
    }
}
"#;
const C: &str = r#"#include <stdio.h>
#include <stdlib.h>
#include <string.h>
struct block { void *bytes; struct block *next; };
struct state { struct block *blocks; };
static struct state *current;
static void trace(char tag) {
    const char *path = getenv("ASH_REGION_TRACE");
    if (!path) abort();
    FILE *file = fopen(path, "ab");
    if (!file || fputc(tag, file) == EOF || fclose(file)) abort();
}
void *region_make(void) {
    struct state *state = calloc(1, sizeof *state);
    if (!state) abort();
    current = state;
    trace('m');
    return state;
}
void *region_allocate(void *opaque) {
    struct state *state = opaque;
    struct block *block = malloc(sizeof *block);
    if (!block) abort();
    block->bytes = aligned_alloc(64, 4096);
    if (!block->bytes) abort();
    memset(block->bytes, 0xa5, 4096);
    block->next = state->blocks;
    state->blocks = block;
    trace('a');
    return block->bytes;
}
void region_inspect_host(const unsigned char *bytes) {
    if (bytes[0] != 42 || bytes[1] != 42) abort();
    trace('b');
}
void region_inspect(const unsigned char *bytes) {
    int found = 0;
    for (struct block *block = current->blocks; block; block = block->next)
        found |= block->bytes == bytes;
    if (!found || bytes[0] != 42 || bytes[1] != 42) abort();
    trace('b');
}
void region_release(void *opaque) {
    struct state *state = opaque;
    /* The fixed pair also releases an owner abandoned before its first block. */
    while (state->blocks) {
        struct block *block = state->blocks;
        unsigned char *bytes = block->bytes;
        /* Persistent tuple initialization must touch the supplied block. */
        int changed = 0;
        for (size_t i = 0; i < 4096; ++i) changed |= bytes[i] != 0xa5;
        if (!changed) abort();
        state->blocks = block->next;
        free(block->bytes);
        free(block);
    }
    trace('r');
    free(state);
    current = NULL;
}
"#;

#[test]
fn custom_region_initializes_and_reads_its_native_backing_before_paired_release() {
    run_native("tuple", ENTRY, b"mar");
}

#[test]
fn custom_region_stores_ordinary_closure_captures_in_supplied_backing() {
    let source = ENTRY.replace(
        TUPLE_BODY,
        "let captured = 42\n        let callback : Unit -> Int = fn(ignored) {\n            captured\n        }\n        callback ()",
    );
    run_native("closure", &source, b"mar");
}

#[test]
fn custom_region_stores_nullary_and_payload_nominal_records_in_supplied_backing() {
    let source = ENTRY
        .replace("provider<R> :", "type Item =\nEmpty\n| Full(Int)\nprovider<R> :")
        .replace(TUPLE_BODY, "let empty = Empty\n        match Full 42 {\n            Full(value) => value\n            Empty => 0\n        }");
    run_native("nominal", &source, b"maar");
}

#[test]
fn custom_region_stores_string_bytes_in_supplied_backing() {
    let source = ENTRY
        .replace(
            "import native as Raw",
            "import native as Raw\nimport @builtin.string as Text",
        )
        .replace(
            TUPLE_BODY,
            "Text.byte_length \"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\"",
        );
    run_native("string", &source, b"mar");
}

#[test]
fn custom_region_initializes_buffer_payloads_before_intrinsic_result_records() {
    let source = ENTRY
        .replace(
            "import native as Raw",
            "import native as Raw\nimport @builtin.string as Text\nimport @builtin.bytes as B",
        )
        .replace(
            TUPLE_BODY,
            r#"let original = Text.to_utf8 "*"
        match B.append_byte (original, 42) {
            B.BytesAppended(joined) => match Text.from_utf8 joined {
                Text.Decoded(text) => match B.at (Text.to_utf8 text, 1) {
                    B.ByteAt(value) => value
                    B.InvalidIndex => 0
                }
                Text.InvalidUtf8 => 0
            }
            B.InvalidByte => 0
        }"#,
        );
    run_native("buffer-results", &source, b"maaaaaaaaaar");
}

#[test]
fn foreign_bytes_payload_cannot_cross_an_unprotected_region_request() {
    let source = ENTRY
        .replace(
            "import native as Raw",
            "import native as Raw\nimport @builtin.string as Text",
        )
        .replace(
            "! {Raw.Make, Raw.Allocate, Raw.Release}",
            "! {Raw.Make, Raw.Allocate, Raw.Release, Raw.Inspect}",
        )
        .replace(
            TUPLE_BODY,
            r#"let packed = Text.to_utf8 "**"
        let _ = perform Raw.Inspect.call packed
        42"#,
        );
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!("ash-region-native-outward-{nonce}"));
    fs::create_dir(&directory).unwrap();
    fs::write(directory.join("native.ash"), NATIVE).unwrap();
    fs::write(directory.join("entry.ash"), source).unwrap();
    let failure = compile_path(RunConfiguration {
        entry: directory.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .unwrap_err();
    fs::remove_dir_all(directory).unwrap();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("source lifetime rejection");
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("{diagnostic:?}");
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn foreign_bytes_argument_borrows_live_root_host_backing() {
    run_native(
        "root-byte-borrow",
        r#"import native as Raw
import @builtin.string as Text
main : Unit -> Int ! {Raw.InspectHost}
main () = {
    let packed = Text.to_utf8 "**"
    let _ = perform Raw.InspectHost.call packed
    42
}
"#,
        b"b",
    );
}

fn suspended_buffer_entry(discard_at: Option<usize>) -> String {
    let body = r#"let original = Text.to_utf8 "*"
        match B.append_byte (original, 42) {
            B.BytesAppended(joined) => match ((B.length joined) + 40) == 42 {
                true => 42
                false => 0
            }
            B.InvalidByte => 0
        }"#;
    suspended_entry(body, 5, discard_at)
}

fn suspended_entry(body: &str, allocations: usize, discard_at: Option<usize>) -> String {
    let handler = if let Some(at) = discard_at {
        format!(
            "match next == {at} {{\ntrue => {{\nlet done = discard\n42\n}}\nfalse => resume ()\n}}"
        )
    } else {
        "resume ()".to_owned()
    };
    let expected = discard_at.unwrap_or(allocations);
    ENTRY
        .replace("import native as Raw", "import native as Raw\nimport @builtin.string as Text\nimport @builtin.bytes as B\nimport @builtin.cell as Cell")
        .replace("provider<R> :", "effect Pause {\nnext : Unit -> Unit\n}\nprovider<R> :")
        .replace("! {Raw.Allocate}", "! {Raw.Allocate, Pause}")
        .replace("let backing = perform Raw.Allocate.call state", "let _ = perform Pause.next ()\n        let backing = perform Raw.Allocate.call state")
        .replace(TUPLE_BODY,body)
        .replace("    region<R> owner =", "    resource cell<C> ticks = 0 {\n    let result = handle (region<R> owner =")
        .replace("\n    }\n}\n", &format!("\n    }}) with Pause {{\nnext ignored => {{\nlet next = (Cell.read ticks) + 1\nlet _ = Cell.write (ticks, next)\n{handler}\n}}\n}}\nmatch (Cell.read ticks) == {expected} {{\ntrue => result\nfalse => 0\n}}\n}}\n}}\n"))
}

const CLOSURE_GROUP_BODY: &str = "let first : Unit -> Int = fn(ignored) {\n42\n}\n        let second : Unit -> Int = fn(ignored) {\nfirst ()\n}\n        second ()";

#[test]
fn closure_creation_resume_keeps_completed_capture_records() {
    run_native(
        "closure-resume",
        &suspended_entry(CLOSURE_GROUP_BODY, 2, None),
        b"maar",
    );
}

#[test]
fn closure_creation_discard_at_second_record_does_not_replay_the_first() {
    run_native(
        "closure-discard",
        &suspended_entry(CLOSURE_GROUP_BODY, 2, Some(2)),
        b"mar",
    );
}

#[test]
fn buffer_allocation_suspension_retains_payload_and_envelope_progress() {
    run_native("buffer-resume", &suspended_buffer_entry(None), b"maaaaar");
}

#[test]
fn buffer_allocation_discard_at_envelope_releases_initialized_payload_backing() {
    run_native(
        "buffer-discard",
        &suspended_buffer_entry(Some(5)),
        b"maaaar",
    );
}

#[test]
fn buffer_allocation_discard_before_first_backing_never_calls_allocate() {
    run_native(
        "buffer-first-discard",
        &suspended_buffer_entry(Some(1)),
        b"mr",
    );
}

#[test]
fn buffer_allocation_discard_before_payload_does_not_replay_earlier_operands() {
    run_native(
        "buffer-payload-discard",
        &suspended_buffer_entry(Some(4)),
        b"maaar",
    );
}

fn run_native(name: &str, entry: &str, expected_trace: &[u8]) {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "ash-region-native-{name}-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&directory).unwrap();
    fs::write(directory.join("native.ash"), NATIVE).unwrap();
    fs::write(directory.join("entry.ash"), entry).unwrap();
    fs::write(directory.join("region.c"), C).unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: directory.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .unwrap();
    let object = directory.join("region.o");
    let archive = directory.join("libregion.a");
    assert!(
        Command::new("cc")
            .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"])
            .arg(directory.join("region.c"))
            .arg("-o")
            .arg(&object)
            .status()
            .unwrap()
            .success()
    );
    assert!(
        Command::new("ar")
            .arg("crs")
            .arg(&archive)
            .arg(object)
            .status()
            .unwrap()
            .success()
    );
    let mut config = BuildConfiguration::new(directory.join("program"));
    config.native_inputs = vec![NativeLinkInput::StaticArchive(archive)];
    config.cargo_target_directory = Some(
        std::env::var_os("CARGO_TARGET_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target")),
    );
    let built =
        build_prepared(prepare_program(&compiled, config).unwrap()).unwrap_or_else(|error| {
            let log = error
                .build_log()
                .and_then(|path| fs::read_to_string(path).ok())
                .unwrap_or_default();
            panic!("{error}\n{log}")
        });
    let trace = directory.join("trace");
    let output = Command::new(built.executable())
        .env("ASH_REGION_TRACE", &trace)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap().trim(), "42");
    assert_eq!(fs::read(trace).unwrap(), expected_trace);
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn custom_region_stores_large_integer_digits_in_supplied_backing() {
    let source = ENTRY.replace(TUPLE_BODY, INTEGER_BODY);
    run_native("integer", &source, b"maar");
}

#[test]
fn integer_pending_digits_resume_without_replaying_arithmetic() {
    run_native(
        "integer-resume",
        &suspended_entry(INTEGER_BODY, 2, None),
        b"maar",
    );
}

#[test]
fn integer_pending_digits_refuse_before_backing_without_replay() {
    run_native(
        "integer-refuse-first",
        &suspended_entry(INTEGER_BODY, 2, Some(1)),
        b"mr",
    );
}

#[test]
fn integer_pending_digits_refuse_after_an_initialized_value() {
    run_native(
        "integer-refuse-second",
        &suspended_entry(INTEGER_BODY, 2, Some(2)),
        b"mar",
    );
}
