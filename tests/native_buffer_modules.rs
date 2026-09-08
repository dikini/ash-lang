mod support;

use support::run_module;

#[test]
fn cell_import_does_not_authorize_native_buffer_acquisition() {
    let source = "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource native_buffer<R> b = 4 {\n42\n}\n";
    let failure = run_module("buffer.ash", source).unwrap_err();
    assert_eq!(failure.reason_code(), "resolve.resource-builtin-required");
}

#[test]
fn native_buffer_import_does_not_authorize_cell_acquisition() {
    let failure = run_module("buffer.ash", "import @builtin.native_buffer as Buffer\nmain : Unit -> Int\nmain () = resource cell<R> c = 4 {\n42\n}\n").unwrap_err();
    assert_eq!(failure.reason_code(), "resolve.resource-builtin-required");
}

#[test]
fn result_constructors_run_without_native_acquisition() {
    let value = run_module("buffer.ash", "import @builtin.native_buffer as Buffer\nmain : Unit -> Int\nmain () = match Buffer.Success 42 {\nBuffer.Success(value) => value\nBuffer.Failure(error) => 0\n}\n").unwrap();
    assert_eq!(value.value().to_string(), "42");
}

#[test]
fn hidden_handle_constructor_is_not_exported() {
    let failure = run_module(
        "buffer.ash",
        "import @builtin.native_buffer as Buffer\nmain : Unit -> Int\nmain () = Buffer.Hidden\n",
    )
    .unwrap_err();
    assert_eq!(failure.reason_code(), "resolve.opaque-constructor");
}
