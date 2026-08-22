use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{PipelineFailure, run_source},
    elaborate::{TypeError, TypeReason},
    lexer::LexReason,
    resolve::ResolveReason,
    source::SourceFile,
};

const V001: &str = include_str!("fixtures/first-stratum/valid/v001-precedence.ash");
const V002_EQUATIONAL: &str = include_str!("fixtures/first-stratum/valid/v002-equational.ash");
const V002_OPERATIONAL: &str = include_str!("fixtures/first-stratum/valid/v002-operational.ash");
const V003: &str = include_str!("fixtures/first-stratum/valid/v003-local-shadowing.ash");
const V004: &str = include_str!("fixtures/first-stratum/valid/v004-capture.ash");
const V008: &str = include_str!("fixtures/first-stratum/valid/v008-mixed.ash");
const RECURSIVE_GLOBAL: &str = include_str!("fixtures/recursion/valid/global-mutual.ash");
const RECURSIVE_LOCAL: &str = include_str!("fixtures/recursion/valid/local-mutual.ash");
const UNSAFE_RECURSIVE_INITIALIZER: &str =
    include_str!("fixtures/recursion/type/unsafe-initializer.ash");
const CURRIED_EQUATIONAL: &str =
    "add : Int -> Int -> Int\nadd left = fn(right) {\n    left + right\n}\n\nadd 20 22\n";
const CONTEXTUAL_BLOCK: &str = "{\n    let constant : Unit -> Int = {\n        fn(ignored) {\n            1\n        }\n    }\n    constant ()\n}\n";
const HIGHER_ORDER_OPERATIONAL: &str = "fn add(left : Int) -> Int -> Int {\n    fn(right) {\n        left + right\n    }\n}\n\nadd 20 22\n";
const FUNCTION_RESULT: &str = "identity : Int -> Int\nidentity value = value\n\nidentity\n";
const COMMENT_REJECTION: &str = "// comments are not in Mini-Ash\n1\n";
const UNKNOWN_NAME_REJECTION: &str = "missing 1\n";
const TYPE_REJECTION: &str = "true + 1\n";
const IRREFUTABLE_TUPLE: &str = "{\n    let (left, right) = (20, 22)\n    left + right\n}\n";
const CONTEXTUAL_MATCH: &str = "fn choose(flag : Bool) -> Int -> Int {\n    match flag {\n        true => fn(value) {\n            value + 1\n        }\n        false => fn(value) {\n            value * 2\n        }\n    }\n}\n\nchoose true 41\n";
const TREE_PRESENTATIONS: &str = "type Tree =\n    Tip(Int)\n    | Fork(Tree, Tree)\n\nsize : Tree -> Int\nsize (Tip value) = 1\nsize (Fork(left, right)) = size left + size right\n\nfn size_match(tree : Tree) -> Int {\n    match tree {\n        Tip(value) => 1\n        Fork(left, right) => size_match left + size_match right\n    }\n}\n\nsize (Fork(Tip(0), Tip(0))) + size_match (Fork(Tip(0), Tip(0)))\n";
const HIGHER_ORDER_CONSTRUCTOR: &str = "type Wrapped =\n    Wrap(Int)\n\nfn build(make : Int -> Wrapped) -> Wrapped {\n    make 42\n}\n\nmatch build Wrap {\n    Wrap(value) => value\n}\n";
const CYCLIC_STREAM: &str = "type Stream =\n    Next(Int, Stream)\n\n{\n    let rec ones : Stream = Next(1, ones)\n    ones\n}\n";

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempDirectory(PathBuf);

impl TempDirectory {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("ash-spec-examples-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("test directory should be creatable: {error}"),
            }
        }
    }
}

impl Drop for TempDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir(&self.0);
    }
}

struct TempFile {
    _directory: TempDirectory,
    path: PathBuf,
}

impl TempFile {
    fn write(text: &str) -> Self {
        let directory = TempDirectory::create();
        let path = directory.0.join("source.ash");
        let owned = Self {
            _directory: directory,
            path,
        };
        fs::write(&owned.path, text).expect("the tool example should be writable");
        owned
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn run(name: &str, text: &str) -> Result<ash::driver::Observation, PipelineFailure> {
    let source = SourceFile::new(name, text).expect("a specification example should fit");
    run_source(source)
}

fn assert_observation(name: &str, text: &str, value: &str, ty: &str) {
    let observation = run(name, text).expect("the documented example should be accepted");
    assert_eq!(observation.value_display(), value);
    assert_eq!(observation.type_display(), ty);
}

fn assert_documented(path: &str, source: &str) {
    let document = fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("missing documentation harness data {path}: {error}"));
    assert!(
        document.contains(source.trim_end()),
        "{path} must contain its executable source example"
    );
}

#[test]
fn syntax_equational_global_example_v002_is_executable() {
    assert_observation("spec-v002-equational.ash", V002_EQUATIONAL, "42", "Int");
    assert_documented("spec/syntax.md", V002_EQUATIONAL);
}

#[test]
fn syntax_inline_operational_global_example_v002_is_executable() {
    assert_observation("spec-v002-operational.ash", V002_OPERATIONAL, "42", "Int");
    assert_documented("spec/syntax.md", V002_OPERATIONAL);
}

#[test]
fn syntax_local_recursive_group_example_is_executable() {
    assert_observation("spec-local-recursion.ash", RECURSIVE_LOCAL, "42", "Int");
    assert_documented("spec/syntax.md", RECURSIVE_LOCAL);
}

#[test]
fn resolution_global_recursive_scope_example_is_executable() {
    assert_observation("spec-global-recursion.ash", RECURSIVE_GLOBAL, "42", "Int");
    assert_documented("spec/name-resolution.md", RECURSIVE_GLOBAL);
}

#[test]
fn static_semantics_rejects_unsafe_recursive_initialization() {
    let failure = run("spec-unsafe-recursion.ash", UNSAFE_RECURSIVE_INITIALIZER)
        .expect_err("recursive values require direct function initialization");
    let PipelineFailure::Typing(TypeError::Source(actual)) = failure else {
        panic!("unsafe recursive initialization should fail during typing")
    };
    assert_eq!(actual.reason, TypeReason::UnsafeRecursiveRoot);
    assert_documented("spec/static-semantics.md", UNSAFE_RECURSIVE_INITIALIZER);
}

#[test]
fn dynamic_recursive_group_example_is_executable() {
    assert_observation("spec-dynamic-recursion.ash", RECURSIVE_LOCAL, "42", "Int");
    assert_documented("spec/dynamic-semantics.md", RECURSIVE_LOCAL);
}

#[test]
fn tool_recursive_example_has_exact_cli_observation() {
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg("tests/fixtures/recursion/valid/global-mutual.ash")
        .output()
        .expect("the documented executable should start");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", RECURSIVE_GLOBAL);
}

#[test]
fn syntax_curried_equational_example_is_executable() {
    assert_observation(
        "spec-curried-equational.ash",
        CURRIED_EQUATIONAL,
        "42",
        "Int",
    );
    assert_documented("spec/elaboration.md", CURRIED_EQUATIONAL);
}

#[test]
fn lexical_comment_rejection_example_has_its_documented_reason() {
    let failure = run("spec-comment-rejection.ash", COMMENT_REJECTION)
        .expect_err("comments are outside this lexical structure");
    let PipelineFailure::Syntax(actual) = failure else {
        panic!("the comment example should fail during syntax processing");
    };
    assert_eq!(
        actual
            .lexical
            .iter()
            .map(|item| item.reason)
            .collect::<Vec<_>>(),
        vec![LexReason::Comment]
    );
    assert_documented("spec/lexical-structure.md", COMMENT_REJECTION);
}

#[test]
fn resolution_unknown_name_example_has_its_documented_reason() {
    let failure = run("spec-unknown-name.ash", UNKNOWN_NAME_REJECTION)
        .expect_err("an unresolved occurrence should be rejected");
    let PipelineFailure::Resolution(actual) = failure else {
        panic!("the unknown-name example should fail during resolution");
    };
    assert_eq!(actual.reason, ResolveReason::UnknownName);
    assert_documented("spec/name-resolution.md", UNKNOWN_NAME_REJECTION);
}

#[test]
fn static_semantics_operand_example_has_its_documented_reason() {
    let failure = run("spec-operator-operand.ash", TYPE_REJECTION)
        .expect_err("a Boolean addition operand should be rejected");
    let PipelineFailure::Typing(TypeError::Source(actual)) = failure else {
        panic!("the operand example should fail during typing");
    };
    assert_eq!(actual.reason, TypeReason::OperatorOperand);
    assert_documented("spec/static-semantics.md", TYPE_REJECTION);
}

#[test]
fn static_semantics_contextual_block_example_is_executable() {
    assert_observation("spec-contextual-block.ash", CONTEXTUAL_BLOCK, "1", "Int");
    assert_documented("spec/static-semantics.md", CONTEXTUAL_BLOCK);
}

#[test]
fn static_semantics_higher_order_operational_example_is_executable() {
    assert_observation(
        "spec-higher-order-operational.ash",
        HIGHER_ORDER_OPERATIONAL,
        "42",
        "Int",
    );
    assert_documented("spec/static-semantics.md", HIGHER_ORDER_OPERATIONAL);
}

#[test]
fn static_semantics_irrefutable_tuple_binding_is_executable() {
    assert_observation("spec-irrefutable-tuple.ash", IRREFUTABLE_TUPLE, "42", "Int");
    assert_documented("spec/static-semantics.md", IRREFUTABLE_TUPLE);
}

#[test]
fn static_semantics_contextual_match_checks_function_arms() {
    assert_observation("spec-contextual-match.ash", CONTEXTUAL_MATCH, "42", "Int");
    assert_documented("spec/static-semantics.md", CONTEXTUAL_MATCH);
}

#[test]
fn elaboration_tree_presentations_are_equivalent() {
    assert_observation(
        "spec-tree-presentations.ash",
        TREE_PRESENTATIONS,
        "4",
        "Int",
    );
    assert_documented("spec/elaboration.md", TREE_PRESENTATIONS);
}

#[test]
fn elaboration_payload_constructor_is_higher_order() {
    assert_observation(
        "spec-higher-order-constructor.ash",
        HIGHER_ORDER_CONSTRUCTOR,
        "42",
        "Int",
    );
    assert_documented("spec/elaboration.md", HIGHER_ORDER_CONSTRUCTOR);
}

#[test]
fn dynamic_cyclic_data_observation_is_finite() {
    assert_observation(
        "spec-cyclic-stream.ash",
        CYCLIC_STREAM,
        "Next(1, <cycle>)",
        "Stream",
    );
    assert_documented("spec/dynamic-semantics.md", CYCLIC_STREAM);
}

#[test]
fn dynamic_binding_derivation_example_v003_is_executable() {
    assert_observation("spec-v003.ash", V003, "2", "Int");
    assert_documented("spec/dynamic-semantics.md", V003);
}

#[test]
fn dynamic_primitive_derivation_example_v001_is_executable() {
    assert_observation("spec-v001.ash", V001, "7", "Int");
    assert_documented("spec/dynamic-semantics.md", V001);
}

#[test]
fn dynamic_application_derivation_example_v002_is_executable() {
    assert_observation("spec-v002.ash", V002_EQUATIONAL, "42", "Int");
    assert_documented("spec/dynamic-semantics.md", V002_EQUATIONAL);
}

#[test]
fn dynamic_capture_derivation_example_v004_is_executable() {
    assert_observation("spec-v004.ash", V004, "42", "Int");
    assert_documented("spec/dynamic-semantics.md", V004);
}

#[test]
fn dynamic_nested_application_derivation_example_v008_is_executable() {
    assert_observation("spec-v008.ash", V008, "42", "Int");
    assert_documented("spec/dynamic-semantics.md", V008);
}

#[test]
fn tool_success_example_has_exact_cli_observation() {
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg("tests/fixtures/first-stratum/valid/v008-mixed.ash")
        .output()
        .expect("the documented executable should start");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", V008);
}

#[test]
fn tool_example_temp_source_requires_exclusive_directory_ownership() {
    let harness = include_str!("spec_examples.rs");
    let exclusive_creation = ["match fs::", "create_dir(&path)"].concat();
    let process_only_path = ["\"ash-spec-function-result-", "{}.ash\""].concat();
    let file_guard = ["let owned = Self ", "{"].concat();
    let guarded_write = ["fs::", "write(&owned.path"].concat();
    assert!(
        harness.contains(&exclusive_creation),
        "the documentation harness must acquire a unique temporary directory"
    );
    assert!(
        !harness.contains(&process_only_path),
        "a process-only filename can overwrite an unowned shared-temp path"
    );
    let guard_position = harness
        .find(&file_guard)
        .expect("the temporary file needs an RAII cleanup guard");
    let write_position = harness
        .find(&guarded_write)
        .expect("the guarded temporary source should be written");
    assert!(
        guard_position < write_position,
        "the cleanup guard must exist before a partial write can fail"
    );
}

#[test]
fn tool_function_result_uses_opaque_rendering() {
    let source = TempFile::write(FUNCTION_RESULT);
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(source.path())
        .output()
        .expect("the documented executable should start");

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"<function> : Int -> Int\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", FUNCTION_RESULT);
}

#[test]
fn tool_cyclic_data_uses_structural_rendering() {
    let source = TempFile::write(CYCLIC_STREAM);
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(source.path())
        .output()
        .expect("the documented executable should start");

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"Next(1, <cycle>) : Stream\n");
    assert!(output.stderr.is_empty());
    assert_documented("docs/tools/ash.md", CYCLIC_STREAM);
}

#[test]
fn tool_source_rejection_uses_status_one_and_stderr() {
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(Path::new(
            "tests/fixtures/first-stratum/type/t002-operator-operand.ash",
        ))
        .output()
        .expect("the documented executable should start");
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).starts_with("type.operator-operand\n"));
    assert_documented("docs/tools/ash.md", TYPE_REJECTION);
}

#[test]
fn normative_document_manifest_is_complete() {
    for path in [
        "spec/README.md",
        "spec/lexical-structure.md",
        "spec/syntax.md",
        "spec/name-resolution.md",
        "spec/static-semantics.md",
        "spec/elaboration.md",
        "spec/dynamic-semantics.md",
        "docs/tools/README.md",
        "docs/tools/ash.md",
    ] {
        assert!(
            Path::new(path).is_file(),
            "missing documentation harness datum {path}"
        );
    }
}
