#[path = "support/source_buffer.rs"]
mod source_buffer;

fn run_imported(helper: &str, entry: &str) -> Result<String, String> {
    source_buffer::run_modules("entry.ash", &[("helper.ash", helper), ("entry.ash", entry)])
        .map(|observed| observed.value_display())
        .map_err(|error| {
            format!(
                "{}: {:?} {:?}",
                error.reason_code(),
                error.pipeline_failure(),
                error.graph_failure()
            )
        })
}

#[test]
fn facade_reexports_original_source_buffer_acquisition() {
    assert_eq!(run_imported(
        "pub import @ffi.native_buffer (Buffer, Outcome, length)\n",
        "import helper (Buffer, Outcome, length)\nmain : Unit -> Outcome<Int>\nmain () = resource Buffer<R> b = 4 {\nlength b\n}\n",
    ).unwrap(), "Success(4)");
}

#[test]
fn copied_source_api_does_not_authorize_native_buffer_acquisition() {
    let helper = r#"pub opaque type Handle<R> = Hidden
pub type Error = InvalidLength
| AllocationFailed
| InvalidIndex
| InvalidByte
pub type Outcome<A> = Success(A)
| Failure(Error)
pub effect Ops<R> {
length : Handle<R> -> Int
read : (Handle<R>, Int) -> Outcome<Int>
write : (Handle<R>, Int, Int) -> Outcome<Unit>
}
pub interface Provider<R> {
length : Handle<R> -> Int ! {Ops<R>}
read : (Handle<R>, Int) -> Outcome<Int> ! {Ops<R>}
write : (Handle<R>, Int, Int) -> Outcome<Unit> ! {Ops<R>}
}
"#;
    assert_eq!(
        run_imported(
            helper,
            "import helper as Buffer\nmain : Unit -> Int\nmain () = 42\n"
        )
        .unwrap(),
        "42"
    );
    let failure = run_imported(helper, "import helper as Buffer\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource Buffer.Buffer<R> b = 4 {\nBuffer.length b\n}\n").unwrap_err();
    assert!(
        failure.starts_with("resolve.unavailable-export:"),
        "{failure}"
    );
}

#[test]
fn imported_generic_callback_retains_native_authority_inside_its_owner() {
    let helper = r#"import @ffi.native_buffer as Buffer
pub reader<R> : Buffer.Buffer<R> -> (Int -> Int ! {Buffer.Ops<Buffer.Buffer<R>>}) where Buffer.Provider<Buffer.Buffer<R>>
reader b = fn(value) {
value + Buffer.length b
}
"#;
    let entry = r#"import @ffi.native_buffer as Buffer
import helper (reader)
effect Adjust {
publish : Int -> Int
}
main : Unit -> Int
main () = match (resource Buffer.Buffer<R> b = 2 {
hook Adjust {
register Adjust (reader b) {
perform Adjust.publish 40
}
}
}) {
Buffer.Success(value) => value
Buffer.Failure(error) => 999
}
"#;
    assert_eq!(run_imported(helper, entry).unwrap(), "42");
}

#[test]
fn imported_open_row_cleanup_helper_accepts_a_native_operation_row() {
    let helper = r#"pub scoped<E : EffectRow> : (Unit -> Unit ! {| E}) -> Int ! {| E}
scoped action = cleanup action {
42
}
"#;
    let entry = r#"import @ffi.native_buffer as Buffer
import @builtin.cell as Cell
import helper (scoped)
main : Unit -> Int
main () = resource cell<S> trace = 0 {
let _ = resource Buffer.Buffer<R> b = 2 {
let action : Unit -> Unit ! {Buffer.Ops<Buffer.Buffer<R>>, Cell.Ops<S>} = fn(ignored) {
Cell.write (trace, Buffer.length b + 40)
}
scoped action
}
Cell.read trace
}
"#;
    assert_eq!(run_imported(helper, entry).unwrap(), "42");
}

#[test]
fn imported_generic_capture_is_usable_inside_but_cannot_escape_native_owner() {
    let helper = r#"pub keep<T> : T -> (Unit -> Int)
keep value = fn(ignored) {
let retained = value
42
}
"#;
    let inside = r#"import @ffi.native_buffer as Buffer
import helper (keep)
main : Unit -> Buffer.Outcome<Int>
main () = resource Buffer.Buffer<R> b = 2 {
let action = keep b
action ()
}
"#;
    assert_eq!(run_imported(helper, inside).unwrap(), "Success(42)");

    let escaping = r#"import @ffi.native_buffer as Buffer
import helper (keep)
main : Unit -> Buffer.Outcome<Unit -> Int>
main () = resource Buffer.Buffer<R> b = 2 {
keep b
}
"#;
    let error = run_imported(helper, escaping).unwrap_err();
    assert!(error.contains("ResourceEscape"), "{error}");
}

#[test]
fn imported_constrained_call_retains_selected_native_capture() {
    let helper = r#"pub interface Read<A> {
read : A -> Int
}
pub invoke<A> : A -> Int where Read<A>
invoke value = read value
"#;
    for body in ["let retained = b\n42", "copied"] {
        let entry = format!(
            r#"import @ffi.native_buffer as Buffer
import helper (Read, read, invoke)
main : Unit -> Int
main () = {{
let escaped = resource Buffer.Buffer<R> b = 2 {{
let copied = Buffer.length b
newtype Token = Token(Unit)
let saved = Token(())
with Read<Token> {{
read ignored = {{
{body}
}}
}}
let later : Unit -> Int = fn(ignored) {{
invoke saved
}}
later
}}
42
}}
"#
        );
        let result = source_buffer::compile_modules(
            "entry.ash",
            &[("helper.ash", helper), ("entry.ash", &entry)],
        );
        if body == "copied" {
            let compiled = result.unwrap();
            assert!(
                compiled
                    .compilation_work()
                    .independent_core
                    .unwrap()
                    .completed
            );
            // This pre-existing generic native-build exclusion is not buffer
            // permission. Preserve the exact source/Core capture witness rather
            // than adding general local-newtype/dictionary image support here.
            let output =
                std::env::temp_dir().join(format!("ash-buffer-unsupported-{}", std::process::id()));
            let error =
                ash::build::prepare_program(&compiled, ash::build::BuildConfiguration::new(output))
                    .unwrap_err();
            assert!(
                format!("{error:?}").contains("Unsupported(RegistryMetadata)"),
                "{error:?}"
            );
        } else {
            let error = result.unwrap_err();
            assert!(format!("{error:?}").contains("ResourceEscape"), "{error:?}");
        }
    }
}

#[test]
fn imported_native_cleanup_row_requires_existing_hook_lacks_authority() {
    let entry = r#"import @ffi.native_buffer as Buffer
import helper (Adjust, scoped)
main : Unit -> Buffer.Outcome<Int>
main () = resource Buffer.Buffer<R> b = 2 {
let action : Unit -> Unit ! {Buffer.Ops<Buffer.Buffer<R>>} = fn(ignored) {
let length = Buffer.length b
()
}
hook Adjust {
scoped action
}
}
"#;
    for row in ["Adjust | E", "| E"] {
        let helper = format!(
            r#"pub effect Adjust {{
publish : Int -> Int
}}
pub scoped<E : EffectRow> : (Unit -> Unit ! {{| E}}) -> Int ! {{{row}}}
scoped action = hook Adjust {{
cleanup action {{
42
}}
}}
"#
        );
        let result = run_imported(&helper, entry);
        if row == "Adjust | E" {
            assert_eq!(result.unwrap(), "Success(42)");
        } else {
            let error = result.unwrap_err();
            assert!(error.contains("AmbiguousEffectRow"), "{error}");
        }
    }
}

#[test]
fn generic_hook_coincidence_preserves_imported_native_capture() {
    let helper = r#"pub keep<T> : T -> (Unit -> Int)
keep value = fn(ignored) {
let retained = value
42
}
"#;
    for (second, expected) in [("()", "Success(42)"), ("true", "Success(13)")] {
        let entry = format!(
            r#"import @ffi.native_buffer as Buffer
import helper (keep)
effect Mark<T> {{
publish : (Unit -> Int) -> (Unit -> Int)
}}
probe<T, U> : (T, U, (Unit -> Int)) -> (Unit -> Int) ! {{Mark<T>}}
probe (first, second, payload) = hook Mark<U> {{
perform Mark<T>.publish payload
}}
main : Unit -> Buffer.Outcome<Int>
main () = resource Buffer.Buffer<R> b = 2 {{
let restored = handle (probe ((), {second}, keep b)) with Mark<Unit> {{
publish input => resume (fn(ignored) {{
13
}})
}}
restored ()
}}
"#
        );
        assert_eq!(run_imported(helper, &entry).unwrap(), expected);
        if second == "()" {
            let escaping = entry
                .replace("Buffer.Outcome<Int>", "Buffer.Outcome<Unit -> Int>")
                .replace("restored ()\n", "restored\n");
            let error = run_imported(helper, &escaping).unwrap_err();
            assert!(error.contains("ResourceEscape"), "{error}");
        }
    }
}

#[test]
fn imported_opaque_request_payload_cannot_export_native_capture() {
    let helper = r#"pub opaque type Box<A> = Hidden(A)
pub pack<A> : A -> Box<A>
pack value = Hidden value
"#;
    for body in ["let retained = b\ncopied", "copied"] {
        let entry = format!(
            r#"import @ffi.native_buffer as Buffer
import helper (Box, pack)
effect Send {{
send : Box<Unit -> Int> -> Unit
}}
main : Unit -> Buffer.Outcome<Int>
main () = handle (resource Buffer.Buffer<R> b = 2 {{
let copied = Buffer.length b
let later : Unit -> Int = fn(ignored) {{
{body}
}}
let sent = perform Send.send (pack later)
42
}}) with Send {{
send payload => resume ()
}}
"#
        );
        let result = run_imported(helper, &entry);
        if body == "copied" {
            assert_eq!(result.unwrap(), "Success(42)");
        } else {
            let error = result.unwrap_err();
            assert!(error.contains("ResourceEscape"), "{error}");
        }
    }
}
