use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};
static NEXT: AtomicU64 = AtomicU64::new(0);
fn run(source: &str) -> String {
    let path: PathBuf = std::env::temp_dir().join(format!(
        "ash-packed-{}-{}.ash",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::write(&path, source).unwrap();
    let result = run_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    let _ = fs::remove_file(path);
    result
        .unwrap_or_else(|e| panic!("{e:?}"))
        .value_display()
        .to_owned()
}
#[test]
fn ordinary_packed_values_use_imported_functions_captures_and_results() {
    assert_eq!(
        run(r#"import @builtin.bytes as ByteOps
import @builtin.string as TextOps
main : Unit -> (Bool, Int, Int, Bool)
main () = {
let original = "héllo 世界\0"
let bytes = TextOps.to_utf8 original
let capture : Unit -> Bool = fn(ignored) {
TextOps.equal (original, original)
}
match TextOps.from_utf8 bytes {
TextOps.Decoded(text) => (TextOps.equal (text, original), TextOps.byte_length text, ByteOps.length bytes, capture ())
TextOps.InvalidUtf8 => (false, 0, 0, false)
}
}
"#),
        "(true, 14, 14, true)"
    );
}
#[test]
fn invalid_bytes_and_utf8_are_ordinary_result_alternatives() {
    assert_eq!(
        run(r#"import @builtin.bytes as B
import @builtin.string as T
main : Unit -> (Bool, Bool, Bool)
main () = {
let empty = B.empty ()
match B.append_byte (empty, 255) {
B.BytesAppended(bytes) => match T.from_utf8 bytes {
T.InvalidUtf8 => match B.append_byte (empty, 256) {
B.InvalidByte => (B.equal (empty, T.to_utf8 ""), true, true)
B.BytesAppended(unexpected) => (false, false, false)
}
T.Decoded(unexpected) => (false, false, false)
}
B.InvalidByte => (false, false, false)
}
}
"#),
        "(true, true, true)"
    );
}
#[test]
fn intrinsics_execute_in_effect_core_with_strict_operands() {
    assert_eq!(
        run(r#"import @builtin.bytes as B
import @builtin.string as T
effect Read {
value : Unit -> String
}
main : Unit -> Bool
main () = handle (T.equal ((perform Read.value ()), "世界")) with Read {
value ignored => resume "世界"
}
"#),
        "true"
    );
}
#[test]
fn callable_aliases_preserve_function_then_tuple_operand_order() {
    assert_eq!(
        run(r#"import @builtin.string as T
import @builtin.cell as Cell
effect Read {
choose : Unit -> ((String, String) -> Bool)
left : Unit -> String
right : Unit -> String
}
main : Unit -> Int
main () = resource cell<R> trace = 0 {
let result = handle ((perform Read.choose ()) ((perform Read.left ()), (perform Read.right ()))) with Read {
choose ignored => {
let _ = Cell.write (trace, (Cell.read trace) * 10 + 1)
resume (fn(pair) {
T.equal pair
})
}
left ignored => {
let _ = Cell.write (trace, (Cell.read trace) * 10 + 2)
resume "世界"
}
right ignored => {
let _ = Cell.write (trace, (Cell.read trace) * 10 + 3)
resume "世界"
}
}
Cell.read trace
}
"#),
        "123"
    );
}
#[test]
fn byte_boundaries_preserve_the_original_alias() {
    assert_eq!(
        run(r#"import @builtin.bytes as B
import @builtin.string as T
main : Unit -> (Bool, Int, Bool)
main () = {
let original = B.empty ()
match B.append_byte (original, 0) {
B.BytesAppended(zero) => match B.append_byte (zero, 255) {
B.BytesAppended(bytes) => match B.append_byte (bytes, 999999999999999999999999999999999) {
B.InvalidByte => (B.equal (original, T.to_utf8 ""), B.length bytes, B.equal (zero, T.to_utf8 "\0"))
B.BytesAppended(unexpected) => (false, 0, false)
}

B.InvalidByte => (false, 0, false)
}
B.InvalidByte => (false, 0, false)
}
}
"#),
        "(true, 2, true)"
    );
}

#[test]
fn ordinary_byte_lookup_copies_unsigned_values_and_refuses_invalid_indices() {
    assert_eq!(
        run(r#"import @builtin.bytes as B
import @builtin.string as T
main : Unit -> (B.ReadResult, B.ReadResult, B.ReadResult, B.ReadResult, B.ReadResult)
main () = match B.append_byte (T.to_utf8 "\0", 255) {
    B.BytesAppended(bytes) => (B.at (bytes, 0), B.at (bytes, 1), B.at (bytes, 2), B.at (bytes, 999999999999999999999999999999999), B.at (B.empty (), 0))
    B.InvalidByte => (B.InvalidIndex, B.InvalidIndex, B.InvalidIndex, B.InvalidIndex, B.InvalidIndex)
}
"#),
        "(ByteAt(0), ByteAt(255), InvalidIndex, InvalidIndex, InvalidIndex)"
    );
}
