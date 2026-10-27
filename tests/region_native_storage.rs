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
    // Empty and Full are two records; evaluating Full's ordinary constructor
    // wrapper creates its own supplied closure record before the payload record.
    run_native("nominal", &source, b"maaar");
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
fn recursive_closure_group_resume_keeps_completed_member_records() {
    let body = CLOSURE_GROUP_BODY
        .replace("let first", "let rec first")
        .replace("let second", "and second");
    run_native(
        "recursive-closure-resume",
        &suspended_entry(&body, 2, None),
        b"maar",
    );
}

#[test]
fn recursive_closure_group_discard_at_second_record_does_not_replay_first() {
    let body = CLOSURE_GROUP_BODY
        .replace("let first", "let rec first")
        .replace("let second", "and second");
    run_native(
        "recursive-closure-discard",
        &suspended_entry(&body, 2, Some(2)),
        b"mar",
    );
}

#[test]
fn supplied_generic_closure_views_share_their_capture_record() {
    run_native("generic-closure-views", &ENTRY.replace(TUPLE_BODY,
        "let captured = 42\nlet identity = fn(value) {\nlet copied = captured\nvalue\n}\nlet answer = identity 42\nmatch identity true {\ntrue => answer\nfalse => 0\n}"), b"mar");
}

#[test]
fn supplied_mixed_recursive_closures_keep_the_guarded_cycle() {
    run_native("mixed-recursive-closure", &ENTRY.replace(TUPLE_BODY,
        "let rec first : Stream = Next(42, read, again)\nand read : Unit -> Int = fn(ignored) {\nmatch first {\nNext(value, ignored, also_ignored) => value\n}\n}\nand again : Unit -> Int = fn(ignored) {\nread ()\n}\nlet alias = first\nmatch alias {\nNext(value, head, tail) => match (head ()) == 42 {\ntrue => match (tail ()) == value {\ntrue => 42\nfalse => 0\n}\nfalse => 0\n}\n}")
        .replace("provider<R> :", "type Stream = Next(Int, Unit -> Int, Unit -> Int)\nprovider<R> :"), b"maaaaar");
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

fn allocating_cleanup_entry(discard: bool) -> String {
    let completion = if discard { "discard" } else { "resume ()" };
    format!(
        r#"import @builtin.cell as Cell
{provider}
effect Stop {{
    stop : Unit -> Unit
}}
main : Unit -> Int ! {{Raw.Make, Raw.Allocate, Raw.Release}}
main () = resource cell<C> completed = 0 {{
    let state = perform Raw.Make.call ()
    let _ = region<A> owner = (provider state) {{
        region<B> other {{
            handle (using owner {{
                cleanup fn(ignored) {{
                    match (20, 22) {{
                        (left, right) => match (left + right) == 42 {{
                            true => Cell.write (completed, 42)
                            false => Cell.write (completed, 0)
                        }}
                    }}
                }} {{
                    perform Stop.stop ()
                }}
            }}) with Stop {{
                stop ignored => {completion}
            }}
        }}
    }}
    Cell.read completed
}}
"#,
        provider = ENTRY.split_once("main :").unwrap().0,
    )
}

#[test]
fn allocating_cleanup_finishes_before_its_owner_releases() {
    // B's allocate/release adapters (2), cleanup closure (1), cleanup tuple
    // (1), and Cell.write argument tuple (1) all use A before its single close.
    run_native(
        "cleanup-normal",
        &allocating_cleanup_entry(false),
        b"maaaaar",
    );
}

#[test]
fn allocating_cleanup_discard_retains_saved_owner_under_another_default() {
    run_native(
        "cleanup-discard",
        &allocating_cleanup_entry(true),
        b"maaaaar",
    );
}

fn provider_effect_cleanup_entry(discard: bool) -> String {
    let provider = ENTRY.split_once("main :").unwrap().0
        .replace("provider<R> :", "effect Console {\n    origin : Int -> Bool\n}\nprovider<R> :")
        .replace("! {Raw.Allocate}", "! {Raw.Allocate, Console}")
        .replace("let backing = perform Raw.Allocate.call state", "let origin = perform Console.origin 1\n        let backing = perform Raw.Allocate.call state\n        let extent = match origin {\n            true => 4096\n            false => 0\n        }")
        .replace("Region.from_backing (request, backing, 4096, 64)", "Region.from_backing (request, backing, extent, 64)");
    let completion = if discard { "discard" } else { "resume ()" };
    format!(
        r#"import @builtin.cell as Cell
{provider}
effect Stop {{
    stop : Unit -> Unit
}}
exercise<C> : (Cell.Handle<C>, Int) -> Unit ! {{Cell.Ops<C>, Console, Stop}} where Cell.Provider<C>
exercise writeback = cleanup fn(ignored) {{
    let pair = (20, 22)
    let sum = match pair {{
        (left, right) => left + right
    }}
    match sum == 42 {{
        true => Cell.write writeback
        false => ()
    }}
}} {{
    let _ = (1, 2)
    let _ = perform Console.origin 0
    perform Stop.stop ()
}}
within<C, D> : (F.Address, (Cell.Handle<C>, Int), (Cell.Handle<D>, Int)) -> Unit ! {{Raw.Allocate, Raw.Release, Console, Cell.Ops<C>, Cell.Ops<D>}} where Cell.Provider<C>, Cell.Provider<D>
within (state, writeback, wrongback) = region<A> owner = (provider state) {{
    handle (handle (exercise writeback) with Console {{
        origin tag => match tag == 0 {{
            true => resume false
            false => {{
                let _ = Cell.write wrongback
                resume false
            }}
        }}
    }}) with Stop {{
        stop ignored => {completion}
    }}
}}
main : Unit -> Int ! {{Raw.Make, Raw.Allocate, Raw.Release}}
main () = resource cell<C> completed = 0 {{
    resource cell<D> wrong = 0 {{
        let state = perform Raw.Make.call ()
        let _ = handle (within (state, (completed, 42), (wrong, 1))) with Console {{
            origin ignored => resume true
        }}
        match (Cell.read wrong) == 0 {{
            true => Cell.read completed
            false => 0
        }}
    }}
}}
"#
    )
}

#[test]
fn provider_effects_use_owner_position_for_normal_and_cleanup_allocation() {
    run_native(
        "cleanup-provider-normal",
        &provider_effect_cleanup_entry(false),
        b"maaaaar",
    );
}

#[test]
fn provider_effects_skip_discarded_inner_handler_during_cleanup_allocation() {
    run_native(
        "cleanup-provider-discard",
        &provider_effect_cleanup_entry(true),
        b"maaaaar",
    );
}

fn removed_backend_cleanup_entry(action_local: bool, release_backend: bool) -> String {
    let mut provider = ENTRY.split_once("main :").unwrap().0.to_owned();
    let request = if action_local {
        "handle (perform Console.origin ()) with Console {\n            origin ignored => resume ()\n        }"
    } else {
        "perform Console.origin ()"
    };
    if release_backend {
        if !action_local {
            provider = provider.replace("! {Raw.Release}", "! {Raw.Release, Console}");
        }
        provider = provider.replace(
            "perform Raw.Release.call state",
            &format!("let _ = {request}\n        perform Raw.Release.call state"),
        );
    } else {
        if !action_local {
            provider = provider.replace("! {Raw.Allocate}", "! {Raw.Allocate, Console}");
        }
        provider = provider.replace(
            "let backing = perform Raw.Allocate.call state",
            &format!("let _ = {request}\n        let backing = perform Raw.Allocate.call state"),
        );
    }
    format!(
        r#"import @builtin.cell as Cell
{provider}
effect Console {{
    origin : Unit -> Unit
}}
effect Stop {{
    stop : Unit -> Unit
}}
within<C> : (F.Address, (Cell.Handle<C>, Int)) -> Unit ! {{Raw.Allocate, Raw.Release, Console, Cell.Ops<C>, Stop}} where Cell.Provider<C>
within (state, writeback) = region<A> owner = (provider state) {{
    cleanup fn(ignored) {{
        let pair = (20, 22)
        let sum = match pair {{
            (left, right) => left + right
        }}
        match sum == 42 {{
            true => Cell.write writeback
            false => ()
        }}
    }} {{
        perform Stop.stop ()
    }}
}}
main : Unit -> Int ! {{Raw.Make, Raw.Allocate, Raw.Release}}
main () = resource cell<C> completed = 0 {{
    let state = perform Raw.Make.call ()
    let _ = handle {{
        let _ = perform Console.origin ()
        handle (handle {{
            let _ = perform Console.origin ()
            within (state, (completed, 42))
        }} with Console {{
            origin ignored => resume ()
        }}) with Stop {{
            stop ignored => discard
        }}
    }} with Console {{
        origin ignored => resume ()
    }}
    Cell.read completed
}}
"#
    )
}

fn assert_removed_backend_rejected(source: &str) {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!("ash-region-removed-backend-{nonce}"));
    fs::create_dir(&directory).unwrap();
    fs::write(directory.join("native.ash"), NATIVE).unwrap();
    fs::write(directory.join("entry.ash"), source).unwrap();
    let error = compile_path(RunConfiguration {
        entry: directory.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .unwrap_err();
    fs::remove_dir_all(directory).unwrap();
    assert_eq!(error.reason_code(), "effect.cleanup-context", "{error:?}");
}

#[test]
fn discarded_owner_cannot_replace_removed_allocate_backend_with_outer_handler() {
    assert_removed_backend_rejected(&removed_backend_cleanup_entry(false, false));
}

#[test]
fn discarded_owner_cannot_replace_removed_release_backend_with_outer_handler() {
    assert_removed_backend_rejected(&removed_backend_cleanup_entry(false, true));
}

#[test]
fn discarded_owner_allocate_backend_can_be_handled_action_locally() {
    run_native(
        "cleanup-allocate-local",
        &removed_backend_cleanup_entry(true, false),
        b"maar",
    );
}

#[test]
fn owner_allocate_backend_handles_normal_and_cleanup_action_locally() {
    let source = removed_backend_cleanup_entry(true, false)
        .replace("stop ignored => discard", "stop ignored => resume ()");
    run_native("cleanup-allocate-local-normal", &source, b"maar");
}

#[test]
fn discarded_owner_release_backend_can_be_handled_action_locally() {
    run_native(
        "cleanup-release-local",
        &removed_backend_cleanup_entry(true, true),
        b"maar",
    );
}

fn shared_backend_c() -> String {
    C.replace(
        "struct state { struct block *blocks; };",
        "struct backend { size_t owners; size_t created; };\nstatic struct backend *shared;\nstruct state { struct block *blocks; struct backend *backend; char tag; };",
    )
    .replace(
        "    current = state;",
        "    if (!shared) {\n        shared = calloc(1, sizeof *shared);\n        if (!shared) abort();\n        trace('s');\n    }\n    state->backend = shared;\n    shared->owners++;\n    state->tag = ++shared->created == 1 ? 'b' : 'a';\n    current = state;",
    )
    .replace(
        "    struct state *state = opaque;",
        "    struct state *state = opaque;\n    if (state->backend != shared || !shared->owners) abort();",
    )
    .replace("    trace('a');", "    trace(state->tag);")
    .replace(
        "    free(state);\n    current = NULL;",
        "    if (--state->backend->owners == 0) {\n        trace('x');\n        free(shared);\n        shared = NULL;\n    }\n    if (current == state) current = NULL;\n    free(state);",
    )
}

#[test]
fn shared_backend_close_preserves_other_region_reads_and_later_allocation() {
    let source = format!(
        r#"{provider}
check_old : (Int, Int) -> Bool
check_old (left, right) = (left + right) == 42
check_later : (Int, Int) -> Int
check_later (first, second) = match (first + second) == 3 {{
    true => 42
    false => 0
}}
main : Unit -> Int ! {{Raw.Make, Raw.Allocate, Raw.Release}}
main () = {{
    let b_state = perform Raw.Make.call ()
    region<B> b = (provider b_state) {{
        let kept = (20, 22)
        let a_state = perform Raw.Make.call ()
        let _ = region<A> a = (provider a_state) {{
            let temporary = (1, 2)
            match temporary {{
                (left, right) => ()
            }}
        }}
        match check_old kept {{
            true => check_later (1, 2)
            false => 0
        }}
    }}
}}
"#,
        provider = ENTRY.split_once("main :").unwrap().0
    );
    // B keeps one tuple, then prepares A's provider closures/pair (3) and
    // preceding-context adapters (2). A owns its temporary; its backing-envelope
    // argument and release bookkeeping allocate in preceding B (2). After A's
    // r, B reads its old tuple and allocates/reads one more. The sole backend x
    // follows both per-handle releases.
    run_native_with_c(
        "shared-backend",
        &source,
        concat!("sm", "b", "m", "bbbbb", "a", "bb", "r", "b", "rx").as_bytes(),
        &shared_backend_c(),
    );
}

fn run_native(name: &str, entry: &str, expected_trace: &[u8]) {
    run_native_with_c(name, entry, expected_trace, C);
}

fn run_native_with_c(name: &str, entry: &str, expected_trace: &[u8], c: &str) {
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
    fs::write(directory.join("region.c"), c).unwrap();
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

const FIXED_REFUSAL_ENTRY: &str = r#"import native as Raw
import @builtin.regions as Region
import @builtin.foreign as F
import @builtin.cell as Cell
import @builtin.string as Text

effect Refused {
    out : Unit -> Unit
}

provider<R> : F.Address -> ((Region.Request -> Region.Storage<R> ! {Raw.Allocate, Refused}), (Unit -> Unit ! {Raw.Release}))
provider state = {
    let allocate : Region.Request -> Region.Storage<R> ! {Raw.Allocate, Refused} = fn(request) {
        let backing = perform Raw.Allocate.call state
        let _ = match F.is_null backing {
            true => perform Refused.out ()
            false => ()
        }
        Region.from_backing (request, backing, 4096, 64)
    }
    let release : Unit -> Unit ! {Raw.Release} = fn(ignored) {
        perform Raw.Release.call state
    }
    (allocate, release)
}

old_is_expected : (Int, Int) -> Bool
old_is_expected pair = match pair {
    (left, right) => match left == 20 {
        true => right == 22
        false => false
    }
}

main : Unit -> Int ! {Raw.Make, Raw.Allocate, Raw.Release, Raw.InspectHost}
main () = resource cell<C> completed = 0 {
    let state = perform Raw.Make.call ()
    let writeback = (completed, 42)
    let inspection = Text.to_utf8 "**"
    let _ = handle (region<R> owner = (provider state) {
        let old = (20, 22)
        cleanup fn(ignored) {
            match old_is_expected old {
                true => {
                    let _ = perform Raw.InspectHost.call inspection
                    Cell.write writeback
                }
                false => ()
            }
        } {
            let _ = (1, 2)
            ()
        }
    }) with Refused {
        out ignored => discard
    }
    Cell.read completed
}
"#;

#[test]
fn fixed_capacity_refusal_preserves_initialized_values_until_cleanup_and_release() {
    // The same Source succeeds with three requests: the old tuple, cleanup
    // record, then the body tuple. Two real blocks preserve the first two and
    // force the body request to refuse, before cleanup reads either old field.
    const BLOCKS: usize = 2;
    let c = format!("#define REGION_CAPACITY_BLOCKS {BLOCKS}\n{C}")
        .replace(
            "struct state { struct block *blocks; };",
            "struct state { struct block *blocks; struct block *next; size_t used; unsigned refusals; unsigned cleanup_seen; };\nstatic unsigned releases;",
        )
        .replace(
            r#"void *region_make(void) {
    struct state *state = calloc(1, sizeof *state);
    if (!state) abort();
    current = state;
    trace('m');
    return state;
}"#,
            r#"void *region_make(void) {
    if (current || releases || REGION_CAPACITY_BLOCKS == 0) abort();
    struct state *state = calloc(1, sizeof *state);
    if (!state) abort();
    for (size_t i = 0; i < REGION_CAPACITY_BLOCKS; ++i) {
        struct block *block = malloc(sizeof *block);
        if (!block) abort();
        block->bytes = aligned_alloc(64, 4096);
        if (!block->bytes) abort();
        memset(block->bytes, 0xa5, 4096);
        block->next = state->blocks;
        state->blocks = block;
    }
    state->next = state->blocks;
    current = state;
    trace('m');
    return state;
}"#,
        )
        .replace(
            r#"void *region_allocate(void *opaque) {
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
}"#,
            r#"void *region_allocate(void *opaque) {
    struct state *state = opaque;
    if (releases || state != current || state->refusals) abort();
    if (!state->next) {
        if (state->used != REGION_CAPACITY_BLOCKS) abort();
        state->refusals++;
        trace('f');
        return NULL;
    }
    struct block *block = state->next;
    state->next = block->next;
    state->used++;
    trace('a');
    return block->bytes;
}"#,
        )
        .replace(
            r#"void region_inspect_host(const unsigned char *bytes) {
    if (bytes[0] != 42 || bytes[1] != 42) abort();
    trace('b');
}"#,
            r#"void region_inspect_host(const unsigned char *bytes) {
    if (releases || !current || current->next ||
        current->used != REGION_CAPACITY_BLOCKS || current->refusals != 1 ||
        current->cleanup_seen || bytes[0] != 42 || bytes[1] != 42) abort();
    for (struct block *block = current->blocks; block; block = block->next) {
        unsigned char *backing = block->bytes;
        int changed = 0;
        for (size_t i = 0; i < 4096; ++i) changed |= backing[i] != 0xa5;
        if (!changed) abort();
    }
    current->cleanup_seen = 1;
    trace('c');
}"#,
        )
        .replace(
            "void region_release(void *opaque) {\n    struct state *state = opaque;",
            "void region_release(void *opaque) {\n    if (++releases != 1 || opaque != current) abort();\n    struct state *state = opaque;\n    if (state->next || state->used != REGION_CAPACITY_BLOCKS || state->refusals != 1 || state->cleanup_seen != 1) abort();",
        );
    let mut expected = vec![b'm'];
    expected.extend(std::iter::repeat_n(b'a', BLOCKS));
    expected.extend_from_slice(b"fcr");
    run_native_with_c("fixed-refusal", FIXED_REFUSAL_ENTRY, &expected, &c);
}
