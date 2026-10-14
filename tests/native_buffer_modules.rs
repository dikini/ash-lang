#[path = "support/source_buffer.rs"]
mod source_buffer;

use source_buffer::run_module;

#[test]
fn targeted_renamed_source_import_authorizes_buffer_acquisition() {
    let value = run_module("buffer.ash", "import @ffi.native_buffer (Buffer as BytesOwner, Outcome as Result, length as size)\nmain : Unit -> Result<Int>\nmain () = resource BytesOwner<R> b = 4 {\nsize b\n}\n").unwrap();
    assert_eq!(value.value().to_string(), "Success(4)");
}

#[test]
fn cell_import_does_not_declare_source_buffer_family() {
    let source = "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource Buffer.Buffer<R> b = 4 {\n42\n}\n";
    let failure = run_module("buffer.ash", source).unwrap_err();
    assert!(failure.reason_code().starts_with("resolve."), "{failure:?}");
}

#[test]
fn native_buffer_import_does_not_authorize_cell_acquisition() {
    let failure = run_module("buffer.ash", "import @ffi.native_buffer as Buffer\nmain : Unit -> Int\nmain () = resource cell<R> c = 4 {\n42\n}\n").unwrap_err();
    assert_eq!(failure.reason_code(), "resolve.resource-builtin-required");
}

#[test]
fn result_constructors_run_without_native_acquisition() {
    let value = run_module("buffer.ash", "import @ffi.native_buffer as Buffer\nmain : Unit -> Int\nmain () = match Buffer.Success 42 {\nBuffer.Success(value) => value\nBuffer.Failure(error) => 0\n}\n").unwrap();
    assert_eq!(value.value().to_string(), "42");
}

#[test]
fn source_buffer_access_has_no_published_hidden_constructor() {
    let failure = run_module(
        "buffer.ash",
        "import @ffi.native_buffer as Buffer\nmain : Unit -> Int\nmain () = Buffer.Hidden\n",
    )
    .unwrap_err();
    assert!(failure.reason_code().starts_with("resolve."), "{failure:?}");
}

#[test]
fn retired_builtin_native_buffer_import_has_no_authority() {
    let error = source_buffer::compile_modules(
        "entry.ash",
        &[(
            "entry.ash",
            "import @builtin.native_buffer as Buffer\nmain : Unit -> Int\nmain () = 42\n",
        )],
    )
    .unwrap_err();
    assert_eq!(error.reason_code(), "module.unknown-builtin");
}
