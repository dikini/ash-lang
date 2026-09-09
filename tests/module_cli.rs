use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{PipelineFailure, RunConfiguration, run_path},
    elaborate::{TypeError, TypeReason},
    interface::InterfaceReason,
    kind::{KindFailure, KindReason},
    module::ModuleRoots,
    types::Kind,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("ash-module-cli-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("test tree should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.path(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be creatable");
        }
        fs::write(&path, text).expect("fixture should be writable");
        path
    }

    fn directory(&self, relative: &str) -> PathBuf {
        let path = self.path(relative);
        fs::create_dir_all(&path).expect("fixture directory should be creatable");
        path
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.0.join(relative)
    }
}

impl Drop for TempTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn root_argument(name: &str, path: &Path) -> OsString {
    OsString::from(format!("{name}={}", path.display()))
}

fn ash(arguments: impl IntoIterator<Item = OsString>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ash"))
        .env("LC_ALL", "C")
        .args(arguments)
        .output()
        .expect("the Ash executable should start")
}

fn human_diagnostic(failure: &ash::driver::FileFailure) -> String {
    let catalogue = ash::message::Catalogue::new(ash::message::Locale::English).unwrap();
    let mut output = Vec::new();
    for diagnostic in ash::presentation::compile_file_diagnostics(failure).unwrap() {
        ash::presentation::write_human(&mut output, &diagnostic, &catalogue).unwrap();
    }
    String::from_utf8(output).unwrap()
}

fn canonicalize_source_ids(rendered: &str) -> String {
    let mut source_ids = Vec::new();
    let mut canonical = String::with_capacity(rendered.len());
    for line in rendered.split_inclusive('\n') {
        let Some(marker) = line.find("source ") else {
            canonical.push_str(line);
            continue;
        };
        let id_start = marker + "source ".len();
        let id_end = id_start
            + line[id_start..]
                .bytes()
                .take_while(u8::is_ascii_digit)
                .count();
        let source_id = &line[id_start..id_end];
        let ordinal = source_ids
            .iter()
            .position(|known| *known == source_id)
            .unwrap_or_else(|| {
                source_ids.push(source_id);
                source_ids.len() - 1
            });
        canonical.push_str(&line[..id_start]);
        canonical.push('_');
        canonical.push_str(&ordinal.to_string());
        canonical.push_str(&line[id_end..]);
    }
    canonical
}

fn occurrence_range(text: &str, needle: &str) -> (u32, u32) {
    let start = text
        .find(needle)
        .unwrap_or_else(|| panic!("the fixture should contain {needle:?}"));
    let end = start + needle.len();
    (
        u32::try_from(start).expect("the fixture start should fit a source offset"),
        u32::try_from(end).expect("the fixture end should fit a source offset"),
    )
}

#[test]
fn canonical_source_ids_preserve_repeated_source_relationships() {
    let first = concat!(
        "primary: source 41 bytes 0..1: first\n",
        "related: source 7 bytes 2..3: second\n",
        "related: source 41 bytes 4..5: third\n",
    );
    let second = concat!(
        "primary: source 9 bytes 0..1: first\n",
        "related: source 12 bytes 2..3: second\n",
        "related: source 12 bytes 4..5: third\n",
    );

    assert_eq!(
        canonicalize_source_ids(first),
        concat!(
            "primary: source _0 bytes 0..1: first\n",
            "related: source _1 bytes 2..3: second\n",
            "related: source _0 bytes 4..5: third\n",
        )
    );
    assert_ne!(
        canonicalize_source_ids(first),
        canonicalize_source_ids(second),
    );
}

#[test]
fn evaluates_an_entry_through_a_named_absolute_import() {
    let tree = TempTree::create();
    let entry = tree.write(
        "app/entry.ash",
        concat!(
            "import @std.answer as Answer\n",
            "main : Unit -> Int\n",
            "main () = Answer.value(())\n",
        ),
    );
    let standard = tree.directory("standard");
    tree.write(
        "standard/answer.ash",
        "pub value : Unit -> Int\nvalue () = 42\n",
    );

    let output = ash([
        OsString::from("--root"),
        root_argument("std", &standard),
        entry.into_os_string(),
    ]);

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn accepts_repeated_root_options_with_distinct_names() {
    let tree = TempTree::create();
    let entry = tree.write(
        "app/entry.ash",
        concat!(
            "import @left.value as Left\n",
            "import @right.value as Right\n",
            "main : Unit -> Int\n",
            "main () = Left.read(()) + Right.read(())\n",
        ),
    );
    let left = tree.directory("left-root");
    let right = tree.directory("right-root");
    tree.write(
        "left-root/value.ash",
        "pub read : Unit -> Int\nread () = 20\n",
    );
    tree.write(
        "right-root/value.ash",
        "pub read : Unit -> Int\nread () = 22\n",
    );

    let output = ash([
        OsString::from("--root"),
        root_argument("left", &left),
        OsString::from("--root"),
        root_argument("right", &right),
        entry.into_os_string(),
    ]);

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn same_spelled_imported_effects_are_handled_independently() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import left as Left\n",
            "import right as Right\n\n",
            "main : Unit -> Int\n",
            "main () = handle (\n",
            "handle ({\n",
            "let left = perform Left.Signal.read ()\n",
            "let right = perform Right.Signal.read ()\n",
            "left + right\n",
            "}) with Right.Signal {\n",
            "read ignored => resume 22\n",
            "}\n",
            ") with Left.Signal {\n",
            "read ignored => resume 20\n",
            "}\n",
        ),
    );
    let effect = "pub effect Signal {\nread : Unit -> Int\n}\n";
    tree.write("left.ash", effect);
    tree.write("right.ash", effect);

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn malformed_root_options_are_usage_failures() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : Unit -> Unit\nmain value = value\n");
    let usage = b"Expected: ash [--message-format human|short|json] [--locale NAME] [--root name=path]... <entry-file>. Options must precede the entry file; format and locale may each be supplied only once.\nreason: invocation.usage\n";

    for arguments in [
        vec![OsString::from("--root")],
        vec![
            OsString::from("--root"),
            OsString::from("std"),
            entry.clone().into_os_string(),
        ],
        vec![
            OsString::from("--root"),
            OsString::from(format!("={}", tree.0.display())),
            entry.clone().into_os_string(),
        ],
        vec![
            OsString::from("--root"),
            OsString::from("std="),
            entry.clone().into_os_string(),
        ],
    ] {
        let output = ash(arguments);
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        assert_eq!(output.stderr, usage);
    }
}

#[test]
fn multiple_entry_paths_are_usage_failures() {
    let tree = TempTree::create();
    let first = tree.write("first.ash", "main : Unit -> Int\nmain () = 1\n");
    let second = tree.write("second.ash", "main : Unit -> Int\nmain () = 2\n");

    let output = ash([first.into_os_string(), second.into_os_string()]);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(
        output.stderr,
        b"Expected: ash [--message-format human|short|json] [--locale NAME] [--root name=path]... <entry-file>. Options must precede the entry file; format and locale may each be supplied only once.\nreason: invocation.usage\n"
    );
}

#[test]
fn duplicate_root_names_are_invocation_failures() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : Unit -> Unit\nmain value = value\n");
    let first = tree.directory("first");
    let second = tree.directory("second");

    let output = ash([
        OsString::from("--root"),
        root_argument("std", &first),
        OsString::from("--root"),
        root_argument("std", &second),
        entry.into_os_string(),
    ]);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(
        output.stderr,
        b"The module root `std` is configured more than once.\nreason: invocation.duplicate-root\n"
    );
}

#[test]
fn invalid_root_names_are_invocation_failures() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : Unit -> Unit\nmain value = value\n");
    let root = tree.directory("root");

    let output = ash([
        OsString::from("--root"),
        root_argument("Std", &root),
        entry.into_os_string(),
    ]);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(output.stderr, b"`Std` is not a valid lowercase Ash identifier for a module root.\nreason: invocation.invalid-root-name\n");
}

#[test]
fn unavailable_root_paths_are_invocation_failures() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : Unit -> Unit\nmain value = value\n");
    let unavailable = tree.path("missing-root");

    let output = ash([
        OsString::from("--root"),
        root_argument("std", &unavailable),
        entry.into_os_string(),
    ]);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(
        output.stderr,
        format!(
            "Cannot use `{}` for module root `std`: the file or directory does not exist.\nreason: invocation.root-unavailable\n",
            unavailable.display()
        )
        .as_bytes()
    );
}

#[test]
fn source_caused_module_failures_use_status_one() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import missing as Missing\n",
            "main : Unit -> Unit\n",
            "main value = value\n",
        ),
    );

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert!(stderr.ends_with("reason: module.not-found\n"));
    assert!(stderr.contains("The failure occurred while processing this import."));
    assert!(stderr.contains(&format!("`{}`", tree.path("missing.ash").display())));
}

#[test]
fn imported_input_failures_retain_the_import_cause_and_target_path() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import invalid as Invalid\n",
            "main : Unit -> Unit\n",
            "main value = value\n",
        ),
    );
    let invalid = tree.path("invalid.ash");
    fs::write(&invalid, [0xff, 0xfe]).expect("invalid UTF-8 fixture should be writable");

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert!(stderr.ends_with("reason: input.invalid-utf8\n"));
    assert!(stderr.contains("The failure occurred while processing this import."));
    assert!(stderr.contains(&format!("`{}`", invalid.display())));
}

#[test]
fn entry_contract_failures_retain_a_causal_source_label() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "helper : Unit -> Unit\nhelper value = value\n");

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.ends_with("reason: entry.missing-main\n"));
    assert!(stderr.contains("This is the entry module."));
}

#[test]
fn cli_renders_the_structured_interface_diagnostic_without_reclassifying_it() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "interface Render<A> {\nrender : A -> Int\n}\n\n",
            "main : Unit -> Int\n",
            "main () = render true\n",
        ),
    );
    let structured = run_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect_err("the interface obligation should remain unsatisfied");
    let PipelineFailure::Typing(TypeError::Interface(diagnostic)) =
        structured.pipeline_failure().expect("pipeline failure")
    else {
        panic!("the programmatic boundary should retain the structured interface diagnostic");
    };
    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    let expected = human_diagnostic(&structured);

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let actual = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert_eq!(
        canonicalize_source_ids(&actual),
        canonicalize_source_ids(&expected)
    );
}

#[test]
fn linked_polymorphic_method_product_has_exact_library_and_cli_observations() {
    let tree = TempTree::create();
    let fixture_directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/method-parameters/linked-product");
    let interface = fs::read_to_string(fixture_directory.join("interface.ash"))
        .expect("the retained interface fixture should be readable");
    let implementation = fs::read_to_string(fixture_directory.join("implementation.ash"))
        .expect("the retained implementation fixture should be readable");
    let entry_source = fs::read_to_string(fixture_directory.join("entry.ash"))
        .expect("the retained entry fixture should be readable");
    // `interface` is reserved in Ash, so the retained plan-mandated filename
    // stages under the parser-valid module identity imported by `entry.ash`.
    tree.write("api.ash", &interface);
    tree.write("carrier.ash", &implementation);
    let entry = tree.write("entry.ash", &entry_source);
    let observation = run_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("the linked polymorphic method product should evaluate through the library");
    assert_eq!(observation.value_display(), "(Box(true), Box(42))");
    assert_eq!(observation.type_display(), "(Box<Bool>, Box<Int>)");

    let output = ash([entry.into_os_string()]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        output.stdout,
        b"(Box(true), Box(42)) : (Box<Bool>, Box<Int>)\n"
    );
    assert!(output.stderr.is_empty());
}

#[test]
fn method_parameter_cli_diagnostics_preserve_library_structure_exactly() {
    let absent_text = concat!(
        "interface Project<I> {\n",
        "project : G<Int> -> I\n",
        "}\n\n",
        "main : Unit -> Unit\n",
        "main () = ()\n",
    );
    let absent_tree = TempTree::create();
    let absent_entry = absent_tree.write("entry.ash", absent_text);
    let absent_failure = run_path(RunConfiguration {
        entry: absent_entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect_err("an absent method binder list should retain predecessor rejection");
    let PipelineFailure::Typing(TypeError::Interface(absent)) =
        absent_failure.pipeline_failure().expect("pipeline failure")
    else {
        panic!("the absent-list failure should remain an interface diagnostic");
    };
    assert_eq!(absent.reason, InterfaceReason::MethodParameter);
    assert_eq!(
        (
            absent.primary.span().range().start(),
            absent.primary.span().range().end(),
        ),
        occurrence_range(absent_text, "project : G<Int> -> I"),
    );
    assert_eq!(
        absent.primary.message(),
        "this method signature must use its interface parameter and only declared type parameters"
    );
    assert_eq!(absent.related.len(), 1);
    assert_eq!(
        (
            absent.related[0].span().range().start(),
            absent.related[0].span().range().end(),
        ),
        occurrence_range(absent_text, "I"),
    );
    assert_eq!(
        absent.related[0].message(),
        "the interface parameter is declared here"
    );
    let absent_expected = human_diagnostic(&absent_failure);
    let absent_output = ash([absent_entry.into_os_string()]);
    assert_eq!(absent_output.status.code(), Some(1));
    assert!(absent_output.stdout.is_empty());
    assert_eq!(
        canonicalize_source_ids(
            &String::from_utf8(absent_output.stderr)
                .expect("the absent-list diagnostic should be UTF-8")
        ),
        canonicalize_source_ids(&absent_expected),
    );

    let recursive_text = concat!(
        "interface Repeat<I> {\nrepeat<A> : (I, A) -> A\n}\n\n",
        "impl Repeat<Int> {\n",
        "repeat (owner, value) = repeat((owner, (value, value)))\n",
        "}\n",
    );
    let recursive_tree = TempTree::create();
    let recursive_entry = recursive_tree.write("entry.ash", recursive_text);
    let recursive_failure = run_path(RunConfiguration {
        entry: recursive_entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect_err("a method-local recursive self-use must remain monomorphic");
    let PipelineFailure::Typing(TypeError::Source(recursive)) = recursive_failure
        .pipeline_failure()
        .expect("pipeline failure")
    else {
        panic!("method-local polymorphic recursion should retain a source diagnostic");
    };
    assert_eq!(recursive.reason, TypeReason::PolymorphicRecursion);
    assert_eq!(recursive.expected.as_deref(), Some("A"));
    assert_eq!(recursive.found.as_deref(), Some("(A, A)"));
    let application = "((owner, (value, value)))";
    let application_start = recursive_text
        .rfind(application)
        .expect("the recursive application should remain source-authored");
    assert_eq!(
        (
            recursive.primary.span().range().start(),
            recursive.primary.span().range().end(),
        ),
        (
            u32::try_from(application_start).expect("the application start should fit"),
            u32::try_from(application_start + application.len())
                .expect("the application end should fit"),
        ),
    );
    assert_eq!(
        recursive.primary.message(),
        "this recursive call requires a different type instantiation"
    );
    assert!(
        recursive.related.iter().any(|label| {
            label.message() == "this recursive function is checked monomorphically"
        })
    );
    let recursive_expected = human_diagnostic(&recursive_failure);
    let recursive_output = ash([recursive_entry.into_os_string()]);
    assert_eq!(recursive_output.status.code(), Some(1));
    assert!(recursive_output.stdout.is_empty());
    assert_eq!(
        canonicalize_source_ids(
            &String::from_utf8(recursive_output.stderr)
                .expect("the recursive method diagnostic should be UTF-8")
        ),
        canonicalize_source_ids(&recursive_expected),
    );
}

#[test]
fn cli_renders_a_selected_facade_prerequisite_route_without_reclassifying_it() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import facade as Facade\n",
            "import facade (impl First)\n\n",
            "main : Unit -> Int\n",
            "main () = Facade.first(1)\n",
        ),
    );
    tree.write(
        "facade.ash",
        "pub import dependency (First, first, impl First)\n",
    );
    tree.write(
        "dependency.ash",
        concat!(
            "pub interface First<A> {\n",
            "first : A -> A\n",
            "}\n\n",
            "pub interface Second<A> {\n",
            "second : A -> A\n",
            "}\n\n",
            "pub impl First<Int> where Second<Int> {\n",
            "first value = value\n",
            "}\n",
        ),
    );
    let structured = run_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect_err("the selected implementation prerequisite should remain unsatisfied");
    let PipelineFailure::Typing(TypeError::Interface(diagnostic)) =
        structured.pipeline_failure().expect("pipeline failure")
    else {
        panic!("the programmatic boundary should retain the facade prerequisite diagnostic");
    };
    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert_eq!(diagnostic.related.len(), 8);
    let expected = human_diagnostic(&structured);

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let actual = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert_eq!(
        canonicalize_source_ids(&actual),
        canonicalize_source_ids(&expected)
    );
}

#[test]
fn cli_renders_each_structured_kind_reason_without_reclassifying_it() {
    struct Case {
        name: &'static str,
        entry: &'static str,
        dependency: Option<&'static str>,
        reason: KindReason,
        imported_relation: bool,
    }

    let cases = [
        Case {
            name: "not-applicable",
            entry: concat!(
                "bad<A> : A<Int> -> Unit\n",
                "bad value = ()\n\n",
                "main : Unit -> Unit\n",
                "main value = value\n",
            ),
            dependency: None,
            reason: KindReason::NotApplicable,
            imported_relation: false,
        },
        Case {
            name: "argument",
            entry: concat!(
                "import dependency as Dependency\n",
                "bad : Dependency.Holder<Int> -> Unit\n",
                "bad value = ()\n\n",
                "main : Unit -> Unit\n",
                "main value = value\n",
            ),
            dependency: Some("pub type Holder<F : Type -> Type> = Holder\n"),
            reason: KindReason::Argument,
            imported_relation: true,
        },
        Case {
            name: "expected-type",
            entry: concat!(
                "import dependency as Dependency\n",
                "bad : Dependency.Holder -> Unit\n",
                "bad value = ()\n\n",
                "main : Unit -> Unit\n",
                "main value = value\n",
            ),
            dependency: Some("pub type Holder<F : Type -> Type> = Holder\n"),
            reason: KindReason::ExpectedType,
            imported_relation: true,
        },
    ];

    for case in cases {
        let tree = TempTree::create();
        let entry = tree.write("entry.ash", case.entry);
        if let Some(dependency) = case.dependency {
            tree.write("dependency.ash", dependency);
        }
        let structured = run_path(RunConfiguration {
            entry: entry.clone(),
            roots: ModuleRoots::empty(),
        })
        .expect_err("the fixture should fail during kind checking");
        let PipelineFailure::Kind(KindFailure::Source(diagnostic)) =
            structured.pipeline_failure().expect("pipeline failure")
        else {
            panic!(
                "{} should retain the structured Kind failure, found {structured:?}",
                case.name
            );
        };
        assert_eq!(diagnostic.reason, case.reason, "case: {}", case.name);
        assert_eq!(diagnostic.related.len(), 1, "case: {}", case.name);
        assert_eq!(
            diagnostic.primary.span().source() != diagnostic.related[0].span().source(),
            case.imported_relation,
            "case: {}",
            case.name,
        );
        if let Some(dependency) = case.dependency {
            let (primary_text, primary_message, related_message, expected_kind, found_kind) =
                match case.reason {
                    KindReason::Argument => (
                        "Int",
                        "this type argument has the wrong kind",
                        "the applied type's parameter kind is declared here",
                        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                        Kind::Type,
                    ),
                    KindReason::ExpectedType => (
                        "Dependency.Holder",
                        "this function domain must have kind Type",
                        "the found kind is fixed by this declaration",
                        Kind::Type,
                        Kind::Arrow(
                            Box::new(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))),
                            Box::new(Kind::Type),
                        ),
                    ),
                    KindReason::NotApplicable => {
                        unreachable!("the imported fixtures cover argument and expected-type")
                    }
                };
            assert_eq!(
                (
                    diagnostic.primary.span().range().start(),
                    diagnostic.primary.span().range().end(),
                ),
                occurrence_range(case.entry, primary_text),
                "imported primary span: {}",
                case.name,
            );
            assert_eq!(
                diagnostic.primary.message(),
                primary_message,
                "imported primary message: {}",
                case.name,
            );
            assert_eq!(
                (
                    diagnostic.related[0].span().range().start(),
                    diagnostic.related[0].span().range().end(),
                ),
                occurrence_range(dependency, "pub type Holder<F : Type -> Type> = Holder"),
                "imported declaration span: {}",
                case.name,
            );
            assert_eq!(
                diagnostic.related[0].message(),
                related_message,
                "imported related message: {}",
                case.name,
            );
            assert_eq!(diagnostic.expected_kind(), Some(&expected_kind));
            assert_eq!(diagnostic.found_kind(), Some(&found_kind));
        }
        let expected = human_diagnostic(&structured);

        let output = ash([entry.into_os_string()]);
        assert_eq!(output.status.code(), Some(1), "case: {}", case.name);
        assert!(output.stdout.is_empty(), "case: {}", case.name);
        let actual = String::from_utf8(output.stderr).expect("kind diagnostics should be UTF-8");
        assert_eq!(
            canonicalize_source_ids(&actual),
            canonicalize_source_ids(&expected),
            "case: {}",
            case.name,
        );
    }
}
