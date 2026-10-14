#[path = "support/source_buffer.rs"]
mod source_buffer;

use ash::{
    driver::{RunConfiguration, compile_path},
    source::SourceFile,
};

fn validate_pipeline(source: &str, modules: &[(&str, &str)]) {
    let directory = std::env::temp_dir().join(format!(
        "ash-buffer-core-{}-{}",
        std::process::id(),
        SourceFile::new("buffer", "").unwrap().id().value()
    ));
    std::fs::create_dir(&directory).unwrap();
    for (name, text) in modules {
        std::fs::write(directory.join(name), text).unwrap();
    }
    let entry = directory.join("entry.ash");
    std::fs::write(&entry, source).unwrap();
    let compiled = compile_path(RunConfiguration {
        entry,
        roots: source_buffer::roots(&directory),
    })
    .map_err(|error| format!("{}: {:?}", error.reason_code(), error.pipeline_failure()));
    std::fs::remove_dir_all(&directory).unwrap();
    assert!(
        compiled
            .unwrap()
            .compilation_work()
            .independent_core
            .unwrap()
            .completed
    );
}

#[test]
fn source_buffer_methods_and_nested_results_cross_independent_core() {
    validate_pipeline(
        "import @ffi.native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Buffer.Outcome<Int>>\nmain () = resource Buffer.Buffer<R> b = 4 {\nlet size = Buffer.length b\nmatch Buffer.write (b, 0, 42) {\nBuffer.Success(()) => Buffer.read (b, 0)\nBuffer.Failure(error) => Buffer.Failure error\n}\n}\n",
        &[],
    );
}

#[test]
fn facade_helpers_preserve_original_source_resource_operations() {
    validate_pipeline(
        "import @ffi.native_buffer as Buffer\nimport facade (size)\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource Buffer.Buffer<R> b = 4 {\nsize b\n}\n",
        &[
            (
                "helper.ash",
                "import @ffi.native_buffer as Buffer\npub size<R> : Buffer.Buffer<R> -> Int ! {Buffer.Ops<Buffer.Buffer<R>>} where Buffer.Provider<Buffer.Buffer<R>>\nsize b = Buffer.length b\n",
            ),
            ("facade.ash", "pub import helper (size)\n"),
        ],
    );
}

#[test]
fn native_success_projection_keeps_outer_values_usable_inside_their_owner() {
    validate_pipeline(
        "import @builtin.cell as Cell\nimport @ffi.native_buffer as Buffer\nmain : Unit -> Int\nmain () = resource cell<S> c = 42 {\nmatch resource Buffer.Buffer<R> b = 4 {\nc\n} {\nBuffer.Success(outer) => Cell.read outer\nBuffer.Failure(error) => 0\n}\n}\n",
        &[],
    );
}
