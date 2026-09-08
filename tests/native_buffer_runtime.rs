mod support;

use support::run_module;

#[test]
fn exact_proposal_source_retains_constructor_identity_and_rendering() {
    let source = r#"import @builtin.native_buffer as Buffer

main : Unit -> Buffer.Outcome<Buffer.Outcome<Int>>
main () = resource native_buffer<R> b = 4 {
match Buffer.write (b, 0, 42) {
Buffer.Success(()) => Buffer.read (b, 0)
Buffer.Failure(error) => Buffer.Failure error
}
}
"#;
    assert_eq!(
        run_module("buffer.ash", source).unwrap().value_display(),
        "Success(Success(42))"
    );
}

fn run_body(body: &str) -> String {
    let source = format!(
        "import @builtin.native_buffer as Buffer\nmain : Unit -> Int\nmain () = match (resource native_buffer<R> b = 2 {{\n{body}\n}}) {{\nBuffer.Success(value) => value\nBuffer.Failure(error) => 999\n}}\n"
    );
    run_module("buffer.ash", &source).unwrap().value_display()
}

#[test]
fn successful_allocation_has_zero_bytes_and_fixed_length() {
    assert_eq!(
        run_body(
            "match Buffer.read (b, 0) {\nBuffer.Success(first) => match Buffer.read (b, 1) {\nBuffer.Success(second) => first + second + Buffer.length b\nBuffer.Failure(error) => 888\n}\nBuffer.Failure(error) => 777\n}"
        ),
        "2"
    );
}

#[test]
fn aliases_access_the_same_owned_allocation() {
    assert_eq!(
        run_body(
            "let alias = b\nlet _ = Buffer.write (alias, 1, 255)\nmatch Buffer.read (b, 1) {\nBuffer.Success(value) => value\nBuffer.Failure(error) => 888\n}"
        ),
        "255"
    );
}

#[test]
fn reentrant_same_site_keeps_a_captured_outer_handles_activation() {
    let source = r#"import @builtin.native_buffer as Buffer
effect Pause {
ask : Unit -> Unit
}
visit : Int -> Int ! {Pause}
visit depth = match (resource native_buffer<R> b = (depth + 1) {
let observe : Unit -> Int ! {Buffer.Ops<R>} = fn(ignored) {
Buffer.length b
}
match depth == 0 {
true => {
let _ = perform Pause.ask ()
Buffer.length b
}
false => handle (visit 0) with Pause {
ask ignored => {
let outer = observe ()
let inner = resume ()
outer + inner
}
}
}
}) {
Buffer.Success(value) => value
Buffer.Failure(error) => 999
}
main : Unit -> Int
main () = handle (visit 1) with Pause {
ask ignored => resume ()
}
"#;
    assert_eq!(
        run_module("buffer.ash", source).unwrap().value_display(),
        "3"
    );
}

#[test]
fn invalid_index_precedes_invalid_byte_and_leaves_storage_unchanged() {
    for index in ["2", "184467440737095516160"] {
        let body = format!(
            "let _ = Buffer.write (b, 0, 42)\nmatch Buffer.write (b, {index}, 256) {{\nBuffer.Failure(Buffer.InvalidIndex) => match Buffer.read (b, 0) {{\nBuffer.Success(value) => value\nBuffer.Failure(error) => 888\n}}\n_ => 777\n}}"
        );
        assert_eq!(run_body(&body), "42", "index {index}");
    }
}

#[test]
fn invalid_byte_leaves_the_previous_byte_unchanged() {
    for byte in ["256", "184467440737095516160"] {
        let body = format!(
            "let _ = Buffer.write (b, 0, 42)\nmatch Buffer.write (b, 0, {byte}) {{\nBuffer.Failure(Buffer.InvalidByte) => match Buffer.read (b, 0) {{\nBuffer.Success(value) => value\nBuffer.Failure(error) => 888\n}}\n_ => 777\n}}"
        );
        assert_eq!(run_body(&body), "42", "byte {byte}");
    }
}

#[test]
fn allocation_wraps_the_body_outcome_without_flattening() {
    let source = r#"import @builtin.native_buffer as Buffer
main : Unit -> Int
main () = match (resource native_buffer<R> b = 4 {
match Buffer.write (b, 0, 42) {
Buffer.Success(()) => Buffer.read (b, 0)
Buffer.Failure(error) => Buffer.Failure error
}
}) {
Buffer.Success(result) => match result {
Buffer.Success(value) => value
Buffer.Failure(error) => 1
}
Buffer.Failure(error) => 2
}
"#;
    assert_eq!(
        run_module("buffer.ash", source).unwrap().value_display(),
        "42"
    );
}

#[test]
fn invalid_length_skips_the_body_and_introduces_no_authority() {
    let source = r#"import @builtin.native_buffer as Buffer
import @builtin.cell as Cell
main : Unit -> Int
main () = resource cell<S> c = 0 {
let outcome = resource native_buffer<R> b = 0 {
let _ = Cell.write (c, 99)
Buffer.length b
}
match outcome {
Buffer.Success(value) => 1
Buffer.Failure(error) => match error {
Buffer.InvalidLength => Cell.read c
Buffer.AllocationFailed => 2
Buffer.InvalidIndex => 3
Buffer.InvalidByte => 4
}
}
}
"#;
    for length in ["0", "184467440737095516160"] {
        let source = source.replace("b = 0", &format!("b = {length}"));
        assert_eq!(
            run_module("buffer.ash", &source).unwrap().value_display(),
            "0",
            "length {length}"
        );
    }
}

#[test]
fn body_failure_is_a_successfully_acquired_body_value() {
    let source = r#"import @builtin.native_buffer as Buffer
main : Unit -> Int
main () = match (resource native_buffer<R> b = 1 {
Buffer.read (b, 1)
}) {
Buffer.Success(result) => match result {
Buffer.Success(value) => 1
Buffer.Failure(error) => match error {
Buffer.InvalidIndex => 42
Buffer.InvalidLength => 2
Buffer.AllocationFailed => 3
Buffer.InvalidByte => 4
}
}
Buffer.Failure(error) => 5
}
"#;
    assert_eq!(
        run_module("buffer.ash", source).unwrap().value_display(),
        "42"
    );
}
