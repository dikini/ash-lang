#[path = "support/source_buffer.rs"]
mod source_buffer;

use source_buffer::run_module;

#[test]
fn inner_cleanup_can_read_a_still_enclosing_native_buffer() {
    let source = r#"import @ffi.native_buffer as Buffer
import @builtin.cell as Cell
main : Unit -> Int
main () = resource cell<S> trace = 0 {
let result = resource Buffer.Buffer<R> b = 1 {
cleanup fn(ignored) {
match Buffer.read (b, 0) {
Buffer.Success(value) => Cell.write (trace, value)
Buffer.Failure(error) => ()
}
} {
let _ = Buffer.write (b, 0, 42)
7
}
}
Cell.read trace
}
"#;
    assert_eq!(
        run_module("buffer.ash", source).unwrap().value_display(),
        "42"
    );
}

#[test]
fn captured_native_owner_resumes_or_closes_before_the_discard_clause_continues() {
    for (clause, expected) in [
        ("resume ()", "92"),
        (
            "{\nlet _ = discard\nlet _ = Cell.write (trace, (Cell.read trace) * 10 + 3)\nBuffer.Success 7\n}",
            "23",
        ),
    ] {
        let source = format!(
            r#"import @ffi.native_buffer as Buffer
import @builtin.cell as Cell
effect Stop {{
stop : Unit -> Unit
}}
main : Unit -> Int
main () = resource cell<S> trace = 0 {{
let result = handle (resource Buffer.Buffer<R> b = 1 {{
let _ = Buffer.write (b, 0, 2)
cleanup fn(ignored) {{
match Buffer.read (b, 0) {{
Buffer.Success(value) => Cell.write (trace, (Cell.read trace) * 10 + value)
Buffer.Failure(error) => ()
}}
}} {{
let _ = perform Stop.stop ()
let _ = Cell.write (trace, 9)
42
}}
}}) with Stop {{
stop ignored => {clause}
}}
Cell.read trace
}}
"#
        );
        assert_eq!(
            run_module("buffer.ash", &source).unwrap().value_display(),
            expected
        );
    }
}

#[test]
fn removed_buffer_override_cannot_fall_back_to_the_live_builtin() {
    let action = "fn(ignored) {\nlet _ = Buffer.write (b, 0, 2)\n()\n}";
    let body = "let read = Buffer.length b\nlet stopped = perform Stop.stop ()\n42";
    let clauses = "length ignored => resume 41\nread ignored => resume (Buffer.Success 1)\nwrite ignored => resume (Buffer.Success ())";
    for (computation, rejected) in [
        (
            format!(
                "handle (cleanup {action} {{\n{body}\n}}) with Buffer.Ops<Buffer.Buffer<R>> {{\n{clauses}\n}}"
            ),
            true,
        ),
        (
            format!(
                "cleanup {action} {{\nhandle {{\n{body}\n}} with Buffer.Ops<Buffer.Buffer<R>> {{\n{clauses}\n}}\n}}"
            ),
            false,
        ),
    ] {
        let source = format!(
            r#"import @ffi.native_buffer as Buffer
effect Stop {{
stop : Unit -> Unit
}}
main : Unit -> Int
main () = match (resource Buffer.Buffer<R> b = 1 {{
let result = handle ({computation}) with Stop {{
stop ignored => {{
let _ = discard
7
}}
}}
match Buffer.read (b, 0) {{
Buffer.Success(value) => result * 10 + value
Buffer.Failure(error) => 888
}}
}}) {{
Buffer.Success(value) => value
Buffer.Failure(error) => 999
}}
"#
        );
        let result = run_module("buffer.ash", &source);
        if rejected {
            assert_eq!(result.unwrap_err().reason_code(), "effect.cleanup-context");
        } else {
            assert_eq!(result.unwrap().value_display(), "72");
        }
    }
}

#[test]
fn recursive_owned_discard_skips_all_body_suffixes() {
    let source = r#"import @ffi.native_buffer as Buffer
import @builtin.cell as Cell
effect Record {
digit : Int -> Unit
}
effect Stop {
stop : Unit -> Unit
}
visit : Int -> Unit ! {Record, Stop}
visit depth = match (resource Buffer.Buffer<R> b = depth {
let _ = match depth == 2 {
true => perform Stop.stop ()
false => visit (depth + 1)
}
perform Record.digit 9
}) {
Buffer.Success(value) => value
Buffer.Failure(error) => ()
}
main : Unit -> Int
main () = resource cell<S> trace = 0 {
let _ = handle (handle (visit 1) with Stop {
stop ignored => discard
}) with Record {
digit value => {
let _ = Cell.write (trace, (Cell.read trace) * 10 + value)
resume ()
}
}
Cell.read trace
}
"#;
    assert_eq!(
        run_module("buffer.ash", source).unwrap().value_display(),
        "0"
    );
}

#[test]
fn acquisition_inside_a_discard_cleanup_still_produces_its_success_wrapper() {
    let source = include_str!("fixtures/native-buffer/discard_cleanup.ash");
    assert_eq!(
        run_module("buffer.ash", source).unwrap().value_display(),
        "42"
    );
}

#[test]
fn native_ownership_does_not_allow_skipping_a_running_cleanup() {
    let source = r#"import @ffi.native_buffer as Buffer
effect Stop {
stop : Unit -> Unit
}
main : Unit -> Buffer.Outcome<Int>
main () = handle (resource Buffer.Buffer<R> b = 1 {
cleanup fn(ignored) {
perform Stop.stop ()
} {
42
}
}) with Stop {
stop ignored => {
let _ = discard
Buffer.Success 7
}
}
"#;
    assert_eq!(
        run_module("buffer.ash", source).unwrap_err().reason_code(),
        "effect.discard-unsafe"
    );
}

#[test]
fn native_owner_outside_a_nested_capture_cannot_be_abandoned() {
    let source = r#"import @ffi.native_buffer as Buffer
effect A {
ask : Unit -> Unit
}
effect B {
ask : Unit -> Unit
}
main : Unit -> Buffer.Outcome<Unit>
main () = handle (resource Buffer.Buffer<R> b = 1 {
perform A.ask ()
}) with A {
ask ignored => {
let _ = handle ({
let _ = perform B.ask ()
resume ()
}) with B {
ask ignored => {
let _ = discard
Buffer.Success ()
}
}
Buffer.Success ()
}
}
"#;
    assert_eq!(
        run_module("buffer.ash", source).unwrap_err().reason_code(),
        "effect.discard-unsafe"
    );
}

#[test]
fn cells_registrations_cleanup_and_native_owners_keep_structural_order() {
    let source = r#"import @ffi.native_buffer as Buffer
import @builtin.cell as Cell
effect Record {
digit : Int -> Unit
}
effect Adjust {
publish : Int -> Int
}
visit : Int -> Unit ! {Record, Adjust}
visit depth = resource cell<R> local = depth {
let _ = resource Buffer.Buffer<S> b = depth {
cleanup fn(ignored) {
perform Record.digit (perform Adjust.publish 0)
} {
register Adjust (fn(value) {
value + depth
}) {
cleanup fn(ignored) {
let _ = perform Record.digit (Cell.read local + Buffer.length b)
perform Record.digit (perform Adjust.publish 0)
} {
()
}
}
}
}
()
}
main : Unit -> Int
main () = resource cell<T> trace = 0 {
let _ = handle (hook Adjust {
visit 1
}) with Record {
digit value => {
let _ = Cell.write (trace, (Cell.read trace) * 10 + value)
resume ()
}
}
Cell.read trace
}
"#;
    assert_eq!(
        run_module("buffer.ash", source).unwrap().value_display(),
        "210"
    );
}
