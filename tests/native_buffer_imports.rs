use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

fn run_imported(helper: &str, entry: &str) -> Result<String, String> {
    let directory = std::env::temp_dir().join(format!(
        "ash-native-imports-{}-{}",
        std::process::id(),
        SourceFile::new("native-imports", "").unwrap().id().value()
    ));
    std::fs::create_dir(&directory).unwrap();
    std::fs::write(directory.join("helper.ash"), helper).unwrap();
    let path = directory.join("entry.ash");
    std::fs::write(&path, entry).unwrap();
    let result = run_path(RunConfiguration {
        entry: path,
        roots: ModuleRoots::empty(),
    });
    std::fs::remove_dir_all(&directory).unwrap();
    result
        .map(|observation| observation.value_display())
        .map_err(|error| format!("{error:?}"))
}

#[test]
fn imported_generic_callback_retains_native_authority_inside_its_owner() {
    let helper = r#"import @builtin.native_buffer as Buffer
pub reader<R> : Buffer.Handle<R> -> (Int -> Int ! {Buffer.Ops<R>}) where Buffer.Provider<R>
reader b = fn(value) {
value + Buffer.length b
}
"#;
    let entry = r#"import @builtin.native_buffer as Buffer
import helper (reader)
effect Adjust {
publish : Int -> Int
}
main : Unit -> Int
main () = match (resource native_buffer<R> b = 2 {
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
    let entry = r#"import @builtin.native_buffer as Buffer
import @builtin.cell as Cell
import helper (scoped)
main : Unit -> Int
main () = resource cell<S> trace = 0 {
let _ = resource native_buffer<R> b = 2 {
let action : Unit -> Unit ! {Buffer.Ops<R>, Cell.Ops<S>} = fn(ignored) {
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
    let inside = r#"import @builtin.native_buffer as Buffer
import helper (keep)
main : Unit -> Buffer.Outcome<Int>
main () = resource native_buffer<R> b = 2 {
let action = keep b
action ()
}
"#;
    assert_eq!(run_imported(helper, inside).unwrap(), "Success(42)");

    let escaping = r#"import @builtin.native_buffer as Buffer
import helper (keep)
main : Unit -> Buffer.Outcome<Unit -> Int>
main () = resource native_buffer<R> b = 2 {
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
            r#"import @builtin.native_buffer as Buffer
import helper (Read, read, invoke)
main : Unit -> Int
main () = {{
let escaped = resource native_buffer<R> b = 2 {{
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
        let result = run_imported(helper, &entry);
        if body == "copied" {
            assert_eq!(result.unwrap(), "42");
        } else {
            let error = result.unwrap_err();
            assert!(error.contains("ResourceEscape"), "{error}");
        }
    }
}

#[test]
fn imported_native_cleanup_row_requires_existing_hook_lacks_authority() {
    let entry = r#"import @builtin.native_buffer as Buffer
import helper (Adjust, scoped)
main : Unit -> Buffer.Outcome<Int>
main () = resource native_buffer<R> b = 2 {
let action : Unit -> Unit ! {Buffer.Ops<R>} = fn(ignored) {
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
            r#"import @builtin.native_buffer as Buffer
import helper (keep)
effect Mark<T> {{
publish : (Unit -> Int) -> (Unit -> Int)
}}
probe<T, U> : (T, U, (Unit -> Int)) -> (Unit -> Int) ! {{Mark<T>}}
probe (first, second, payload) = hook Mark<U> {{
perform Mark<T>.publish payload
}}
main : Unit -> Buffer.Outcome<Int>
main () = resource native_buffer<R> b = 2 {{
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
            r#"import @builtin.native_buffer as Buffer
import helper (Box, pack)
effect Send {{
send : Box<Unit -> Int> -> Unit
}}
main : Unit -> Buffer.Outcome<Int>
main () = handle (resource native_buffer<R> b = 2 {{
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
