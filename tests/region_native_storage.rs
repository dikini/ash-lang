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
}
"#;
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
            (left, right) => left + right
        }
    }
}
"#;
const C: &str = r#"#include <stdio.h>
#include <stdlib.h>
#include <string.h>
struct block { void *bytes; struct block *next; };
struct state { struct block *blocks; };
static void trace(char tag) {
    const char *path = getenv("ASH_REGION_TRACE");
    if (!path) abort();
    FILE *file = fopen(path, "ab");
    if (!file || fputc(tag, file) == EOF || fclose(file)) abort();
}
void *region_make(void) {
    struct state *state = calloc(1, sizeof *state);
    if (!state) abort();
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
void region_release(void *opaque) {
    struct state *state = opaque;
    if (!state->blocks) abort();
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
}
"#;

#[test]
fn custom_region_initializes_and_reads_its_native_backing_before_paired_release() {
    let directory = std::env::temp_dir().join(format!("ash-region-native-{}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    fs::write(directory.join("native.ash"), NATIVE).unwrap();
    fs::write(directory.join("entry.ash"), ENTRY).unwrap();
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
    assert_eq!(fs::read(trace).unwrap(), b"mar");
    fs::remove_dir_all(directory).unwrap();
}
