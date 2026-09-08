mod support;

use support::run_module;

#[test]
fn cell_import_does_not_authorize_native_buffer_acquisition() {
    let source = "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource native_buffer<R> b = 4 {\n42\n}\n";
    let failure = run_module("buffer.ash", source).unwrap_err();
    assert_eq!(failure.reason_code(), "resolve.resource-builtin-required");
}
